module VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

variable
  l : Level
  A B C : Set l
  M V : Set l -> Set l

record SuccMonad (M : Set l -> Set l) : Set l where
field
  return : A -> M A
  _>>=_ : M A -> (A -> M B) -> M B
  next : M (A -> M B)
  -- next_prop : next >>= K -- would get itself as an input...

-- one could do the get thing separately

record VarMonad (M : Set l -> Set l) (V : Set l -> Set l) : Set l where
field
  get : V A -> (A -> M B) -> M B --requires waiting. Also, do-notation does not work here...
  -- ...

-- maybe fix that by giving information into the next state that a split occurred or a variable has been read.
-- or just, during get, trace the value that was read. simple as that. constrain the get to only return a DTC type.


record BaseVarMonad M V : Set _ where
  field
    new : A -> M (V A)
    get : V A -> M A
    modify : V A -> (A -> (A -x- B)) -> M B
  put : V A -> A -> M ()
  put p val = modify p $ const (val, ())

AsmList : Set l
AsmList = List $ exists T st (V T -x- T)

record CLVarMonad M V : Set _ where
  field
    bvm : BaseVarMonad M V
    getReason : V A -> AsmList
  open BaseVarMonad bvm

baseToCL : BaseVarMonad M V -> BaseVarMonad (StateT AsmList M) V
baseToCL bvm = record{
  bvm = record{
    new = \x -> lift $ new ([],x),
    get = \p -> do
      v <- snd <$> (lift $ get p)
      state ( (_ , (p , v)) ::_)
      return v
    --this just discards the old reasons...that might cause problems.
    modify = \p f -> do
      s <- getState
      lift $ modify p (\(_ , v) -> let (v' , res) = f v in ((s , v') , res))
    };
  getReason = (fst <$>) o lift o get
}
  where open BaseVarMonad bvm

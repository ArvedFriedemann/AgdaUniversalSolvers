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

record LatticeVarMonad M V : Set _ where
  field
    new : A -> M (V A)
    get : V A -> M A
    put : {Lattice A} -> V A -> A -> M ()
    put-prop : put p v >> m >> get p >>= \v' -> return (v leq v')

AsmList : Set l
AsmList = List $ exists T st (V T -x- T)

record CLVarMonad M V : Set _ where
  field
    bvm : BaseVarMonad M V
    getReason : V A -> AsmList
  open BaseVarMonad bvm

record LatCLVarMonad M V : Set _ where
  field
    lvm : LatticeVarMonad M V
    getReason : V A -> AsmList
  open LatticeVarMonad lvm

--this whole approach obviously only works if variable assignment is only growing.
baseToCL : BaseVarMonad M V -> CLVarMonad (StateT AsmList M) V
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

--The V probably needs to be a Carr V for some Carrier Carr : Set l -> Set l -> Set l, becuase the pointers now point to something bigger, but the functor still is just to the pointer. So prolly \A -> V (AsmList -x- A)
--TODO: check if this compiles
lattToCl : LatticeVarMonad M V -> LatCLVarMonad (StateT AsmList M) (\A -> V (AsmList -x- A))
lattToCl lvm = record {
  lvm = record {
    new = \x -> lift $ new ([[]],x), --can hold multiple reasons
    get = \p -> do
      v <- snd <$> (lift $ get p)
      state ( (_ , (p , v)) ::_)
      return v
    put = \p v -> do
      s <- getState
      lift $ put p (s , v)
  };
  getReason = (fst <$>) o lift o get
}
  where open LatticeVarMonad lvm


--TODO: Do the scopes with lattices

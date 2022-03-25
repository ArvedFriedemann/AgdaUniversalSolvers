module VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

variable
  l : Level
  A B C L : Set l
  M V F : Set l -> Set l

record Functor F : Set _ where
  field
    _<$>_ : (A -> B) -> F A -> F B

record Applicative F : Set _ where
  field
    pure : A -> F A
    <*> : F (A -> B) -> F A -> F B
    func : Functor F
  open Functor func public

record Monad M : Set _ where
  field
    appl : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B
  open Applicative appl public
  return : A -> M A
  return = pure

record VarMonad M V : Set _ where
  field
    new : A -> M (V A)
    get : V A -> M A
    modify : V A -> (A -> A -x- B) -> M B

  modify' : V A -> (A -> A) -> M T
  modify' p f = modify p (\v -> (f v , tt))

  put : V A -> A -> M T
  put p v = modify' p (const v)

record Lattice L : Set _ where
  _/\_ : L -> L -> L
  _\/_ : L -> L -> L
  top : L
  bot : L

record IncrFunc {lat : Lattice L} L : Set _ where
  constructor IncrFuncC
  open Lattice lat
  field
    f : L -> L
    incr-prop : forall l -> l leq f l

record LatVarMonad M V : Set _ where
  field
    new : L -> (V L)
    get : V L -> M L
    modify : V L -> IncrFunc L -> (L -> B) -> M B

  modifyIncr : V L -> (L -> (L , B)) -> M B
  modifyIncr p f = modify p (_/\ o fst o f) (snd o f) --TODO: increason proof

  put : {Lattice L} -> V L -> L -> M T
  put lat p v = modify p (IncrFunc (_/\ v) _) (const tt)

  new' : {Lattice L} -> M (V L)
  new' lat = new top
    where open Lattice lat

VMToLatVM : VarMonad M V -> LatVarMonad M V
VMToLatVM vm = record {
  new = new;
  get = get;
  modify = \{lat} p fs fo -> modify p (\l -> (fs l , fo l) )
}
  where open VarMonad vm

record UpdateVarMonad M V : Set _ where
  field
    observe : V A -> (A -> A -> M T) -> M T
    --there needs to be some law stating that observe and modify are kinda working together

record TFunc {lat : Lattice A} A B : Set _ where
  constructor TFuncC
  open Lattice lat
  field
    f : A -> Maybe B
    f-prop : forall v v' r -> f v === just r -> v leq v' -> f v' === just r


record ThresholdVarMonad M V : Set _ where
  field
    latvm : LatVarMonad M V
    observe : {lat : Lattice A} -> V A -> TFunc {lat} A B -> (B -> M T) -> M T

record ForkMonad M : Set _ where
  field
    fork : M T -> M T

--container still needs lattice instance
LatVMToTVM : LatVarMonad M V -> ForkMonad M -> Container C -> LatVarMonad M (\A -> V (A -x- C))
LatVMToTVM vlm forkM con = record {
  letvm = record {
    new = \v -> new (v , empty);
    get = (snd <$>) o get;
    modify = \p fs fo -> do
      --TODO: needs proof of increason (or use modifyIncr...is just a bit less performant)
      (res , props) <- modify p (\(v , c) -> (fs v , c) ) (\(v , c) -> (fo v , c))
      sequenceMap fork props --TODO: check if props even fire first!
      return res
  };
  observe = \{lat} p (TFuncC f _) fm -> do --TODO: clean this up!
    props <- modifyIncr p (\l with f l
      ...| just v = (top , singleton $ fm v)
      ...| nothing = (top , empty) )
    void $ sequenceMap fork props
}
  where
    open LatVarMonad vlm
    open Container con
    open FormMonad forkM

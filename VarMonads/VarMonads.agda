{-# OPTIONS --type-in-type --overlapping-instances #-}

module VarMonads.VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B L S : Set
    M V F C : Set -> Set

record Functor (F : Set -> Set) : Set  where
  field
    _<$>_ : (A -> B) -> F A -> F B


record Applicative F : Set where
  field
    pure : A -> F A
    <*> : F (A -> B) -> F A -> F B
    func : Functor F
  open Functor func public

record Monad M : Set where
  field
    appl : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B
  open Applicative appl public

  return : A -> M A
  return = pure

  _>>_ : M A -> M B -> M B
  _>>_ m1 m2 = m1 >>= const m2

--open Monad {{...}} public

record Lattice A : Set where
  field
    _/\_ : A -> A -> A
    _\/_ : A -> A -> A
    ltop : A
    lbot : A

open Lattice {{...}} public

record VarMonad M (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    get : V A -> M A
    modify : V A -> (A -> A -x- B) -> M B

    overlap {{mon}} : Monad M
  open Monad mon public



record LatVarMonad M (V : Set -> Set) : Set where
  field
    new : {{lat : Lattice A}} -> A -> M (V A)
    get : V A -> M A
    modify : {{lat : Lattice A}} -> V A -> (A -> A -x- B) -> M B

    overlap {{mon}} : Monad M
  open Monad mon public
    --Properties:
    {-
    --value of a variable only every increases exactly by values given through modify
    modprop : (p : V A) -> do
      v <- get p
      m1
      modify p f
      m2
      v' <- get p
      return (v' leq (v /\ (fst $ f v)))
    -}


  new' : {{lat : Lattice A}} -> M (V A)
  new' = new ltop

  modify' : {{lat : Lattice A}} -> V A -> (A -> A) -> M T
  modify' p f = modify p (\ x -> (f x , top) )

  put : {{lat : Lattice A}} -> V A -> A -> M T
  put p v = modify' p (const v)


VarMonad=>LatVarMonad : VarMonad M V -> LatVarMonad M V
VarMonad=>LatVarMonad vm = record {
  new = new ;
  get = get ;
  modify = \ p f -> modify p (\ v -> v /\ fst (f v) , snd (f v)) ;

  mon = mon }
  where open VarMonad vm

record Container (C : Set -> Set) : Set where
  field
    empty : C A
    singleton : A -> C A
open Container {{...}} public
{-}
record LatCont (C : Set -> Set) : Set where
  field
    cont : Container C
    lat : Lattice (C A)
  open Container cont public
  open Lattice lat public
-}

AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C $ Sigma Set (\A -> (A -x- V A))

--TODO: Those need to be threshold functions
IndrAsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
IndrAsmCont C V = C $ Sigma (Set -x- Set) (\ (A , B) -> ((A -> Maybe B) -x- B -x- V A))


record CLLatVarMonad M V C : Set where
  field
    lvm : LatVarMonad M V
  open LatVarMonad lvm public
  field
    getReasons : V A -> M (C $ AsmCont C V)

instance
  lat-to-tup : {{latA : Lattice A}} -> {{latB : Lattice B}} -> Lattice (A -x- B)
  lat-to-tup = {!!}

  contLattice : {{cont : Container C}} -> Lattice (C A)
  contLattice = {!!}

record TrackLatVarMonad M V C : Set where
  field
    lvm : LatVarMonad M V
    getCurrAssignments : M (AsmCont C V)

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : M A -> T M A
open MonadTrans {{...}} public

record StateT S (M : Set -> Set) A : Set where
  field
    runStateT : S -> M (A -x- S)

state : {{mon : Monad M}} -> (S -> (B -x- S)) -> StateT S M B
state {{mon = mon}} f = record { runStateT = return o f }
  where open Monad mon

modifyS : {{mon : Monad M}} -> (S -> S) -> StateT S M T
modifyS f = state (\ s -> (top , f s))

getS : {{mon : Monad M}} -> StateT S M S
getS = state \ x -> x , x

putS : {{mon : Monad M}} -> S -> StateT S M T
putS s = state $ const $ (top , s)

instance

  monad-stateT : {{mon : Monad M}} -> Monad (StateT S M)
  monad-stateT {{mon = mon}} = record {
    appl = {!   !} ;
    _>>=_ = \ m fm -> record{runStateT = \ s -> (StateT.runStateT m s >>= \ (a , s') -> StateT.runStateT (fm a) s') } }
    where open Monad mon

  StateTMonadTrans : MonadTrans (StateT S)
  StateTMonadTrans = {!!}





LatVarMonad=>TrackLatVarMonad : {{cont : Container C}} -> LatVarMonad M V -> TrackLatVarMonad (StateT (AsmCont C V) M) V C
LatVarMonad=>TrackLatVarMonad lvm = record {
  lvm = record {
    mon = monT;
    new = liftT o new ;
    get = \ {A = A} p -> liftT (get p) >>= (\ v -> modifyS (_/\ singleton (A , v , p)) >> return v)  ;
    modify = \ p f -> liftT (modify p f) };
  getCurrAssignments = getS
  }
  where
    monT = monad-stateT
    open LatVarMonad lvm hiding (return; _>>=_; _>>_)
    open Monad monT

{-
--TODO: Tracking should be done separately
LatVarMonad=>CLLatVarMonad : {{cont : Container C}} -> LatVarMonad M V -> CLLatVarMonad M (\ A -> V (A -x- (C $ AsmCont C V) )) C
LatVarMonad=>CLLatVarMonad lvm = record {
  lvm = record {
    new = new o ( _, empty) ;
    get = (fst <$>_) o get ;
    modify = {!   !} ;
    mon = {!   !} } ;
  getReasons = {!   !} }
  where
    open LatVarMonad lvm
-}

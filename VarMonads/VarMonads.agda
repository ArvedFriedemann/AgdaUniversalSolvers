{-# OPTIONS --type-in-type --overlapping-instances #-}
--{-# OPTIONS --guardedness #-}

module VarMonads.VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B L S D : Set
    M V F C : Set -> Set

record Functor (F : Set -> Set) : Set  where
  field
    _<$>_ : (A -> B) -> F A -> F B
open Functor {{...}}

record Applicative F : Set where
  field
    pure : A -> F A
    <*> : F (A -> B) -> F A -> F B
    overlap {{func}} : Functor F
  --open Functor func public
open Applicative {{...}}

record Monad M : Set where
  field
    overlap {{appl}} : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B
  --open Applicative appl public

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

open Lattice {{...}}

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

record SpecLatVarMonad (M : Set -> Set) (V : Set -> Set) B : Set where
  field
    {{lat}} : Lattice B
    get : V A -> M B
    --lattice instance here technically not needed, because A value never touched.
    --However, underlying modify is still used, so lattice instance comes in handy
    modify : {{Lattice A}} -> V A -> (B -> B -x- D) -> M D

    overlap {{mon}} : Monad M

  modify' : {{Lattice A}} -> V A -> (B -> B) -> M T
  modify' p f = modify p (\ x -> (f x , top))

  put : {{Lattice A}} -> V A -> B -> M T
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

ProdPtr : (V : Set -> Set) -> (B : Set) -> (A : Set) -> Set
ProdPtr V B A = V (A -x- B)

productLatVarMonad : (B : Set) -> {{lat : Lattice B}} -> LatVarMonad M V ->
  LatVarMonad M (ProdPtr V B) -x- SpecLatVarMonad M (ProdPtr V B) B
productLatVarMonad B {{lat = lat}} lvm =
  (record {
    new = \x -> new (x , ltop) ;
    get = (fst <$>_) o get ;
    modify = \ p f -> modify p (\(v , b) -> let v' , res = f v in (v' , b) , res) }) ,
  (record {
    get = (snd <$>_) o get ;
    modify = \ p f -> modify p (\(v , b) -> let b' , res = f b in (v , b') , res) })
  where open LatVarMonad lvm

liftSpecLatVarMon : forall {T} -> {{monT : MonadTrans T}} -> {{monmonT : Monad (T M)}} ->
  SpecLatVarMonad M V B -> SpecLatVarMonad (T M) V B
liftSpecLatVarMon splvm = record {
  get = liftT o get ;
  modify = \ p f -> liftT $ modify p f }
  where open SpecLatVarMonad splvm

Fix : (F : Set -> Set) -> Set
Fix F = {A : Set} -> (F A -> A) -> A

foldF : (F A -> A) -> Fix F -> A
foldF alg fa = fa alg

data _:+:_ (F : Set -> Set) (G : Set -> Set) (A : Set) : Set where
  Inl : F A -> (F :+: G) A
  Inr : G A -> (F :+: G) A

data Lit (A : Set) : Set where
  litC : Lit A

data Add (A : Set) : Set where
  addC : A -> A -> Add A

lit : Fix (Lit :+: Add)
lit alg = alg (Inl litC)

add : Fix (Lit :+: Add) -> Fix (Lit :+: Add) -> Fix (Lit :+: Add)
add f1 f2 alg = alg (Inr (addC (foldF alg f1) (foldF alg f2)))

test : Fix (Lit :+: Add)
test = add lit (add lit lit)

FixF : (F : (Set -> Set) -> Set -> Set) -> Set -> Set
FixF F A = {B : Set -> Set} -> (F B A -> B A) -> B A

RecPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set -> Set) -> (A : Set) -> Set
RecPtr V F = FixF (\ V' A -> V (F V' A) )

testRefVarMonad : LatVarMonad M V -> {{cont : Container C}} -> LatVarMonad M (RecPtr V (\ V' A -> (A -x- C (Sigma Set V') )))
testRefVarMonad {V = V} {C = C} lvm = record {
    new = \ {A = A} x -> (\ p -> {!!} ) <$> new ( x , empty ) ;
    get = {!   !} ;
    modify = {!   !} }
  where open LatVarMonad lvm

--{-# NO_POSITIVITY_CHECK #-}
{-
data Fix (F : Set -> Set) : Set where
  In : F (Fix F) -> Fix F
-}
--{-# TERMINATING #-}
{-
foldF : {F : Set -> Set} -> {{func : Functor F}} -> (F A -> A) -> Fix F -> A
foldF alg (In x) = alg (foldF alg <$> x)
-}
--{-# NO_POSITIVITY_CHECK #-}
{-
data FixF (F : (Set -> Set) -> Set -> Set) : Set -> Set where
  InF : (F (FixF F) A) -> FixF F A
-}

{-

fixCont : {F : (Set -> Set) -> Set -> Set} -> FixF F A -> F (FixF F) A
fixCont (InF x) = x

FixW : {A : Set} -> (F : A -> A) -> A
FixW F = {!!} --???


RecPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set -> Set) -> (A : Set) -> Set
RecPtr V F = FixF (\ V' A -> V (F V' A) )

RecTupPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> Set -> Set
RecTupPtr V F = RecPtr V (\ V' A -> A -x- F V')

ReasPtr : (V : Set -> Set) -> (C : Set -> Set) -> Set -> Set
ReasPtr V C = RecTupPtr V (\ V' -> C $ AsmCont C V')

recProductVarMonad : {A : Set} -> {V : Set -> Set} -> {B : (Set -> Set) -> Set} ->
  {{lat : Lattice (B (RecTupPtr V B))}} ->
  LatVarMonad M V ->
  LatVarMonad M (RecTupPtr V B) -x- SpecLatVarMonad M (RecTupPtr V B) (B (RecTupPtr V B))
recProductVarMonad lvm = (record {
    new = \ x -> InF <$> {!!} ; --\ x -> InF <$> new (x , ltop) ;
    get = {!   !} ;
    modify = {!   !} }) ,
  (record {
    get = {!   !} ;
    modify = {!   !} })
  where open LatVarMonad lvm


--ProdPtr V (C $ AsmCont C V)
-- V (A -x- C (V (A -x- C (...) )))
-- => PtrTp V C A = V (A -x- PtrTp V C A)
-- => PtrTp V C A = In (V (A -x- PtrTp V C A))
-- => PtrTp V C A = Fix (\ V' -> V (A -x- V'))
--TODO: Tracking should be done separately
LatVarMonad=>CLLatVarMonad : {{cont : Container C}} -> LatVarMonad M V ->
  CLLatVarMonad M (ReasPtr V C) C --TODO: pointer type here changes. Problem with fixpoint
LatVarMonad=>CLLatVarMonad {C = C} {V = V} lvm = record {
    lvm = {!   !} ;
    getReasons = {! tpl  !} }
  where
    singleReason = AsmCont C (ReasPtr V C)
    reasonType = C singleReason
    tpl = productLatVarMonad reasonType lvm
    lvm' = fst tpl
    reasonContMon = snd tpl
    lvmTrack = LatVarMonad=>TrackLatVarMonad lvm'
    reasonContMonT = liftSpecLatVarMon reasonContMon
-}

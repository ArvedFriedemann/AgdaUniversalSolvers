{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonads.VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

open import Debug.Trace

private
  variable
    A B L S D : Set
    M V F C : Set -> Set

record Functor (F : Set -> Set) : Set  where
  field
    _<$>_ : (A -> B) -> F A -> F B
open Functor {{...}}

record Applicative F : Set where
  infixl 4 _<*>_
  field
    pure : A -> F A
    _<*>_ : F (A -> B) -> F A -> F B
    overlap {{func}} : Functor F
  --open Functor func public
open Applicative {{...}}

record Monad M : Set where
  infixl 1 _>>=_
  field
    overlap {{appl}} : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B
  --open Applicative appl public

  return : A -> M A
  return = pure

  infixl 1 _>>_
  _>>_ : M A -> M B -> M B
  _>>_ m1 m2 = m1 >>= const m2

open Monad {{...}} public

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
  --open Monad mon public
  modify' : V A -> (A -> A) -> M T
  modify' p f = modify p \ v -> f v , tt

  put : V A -> A -> M T
  put p v = modify' p (const $ v)


record LatVarMonad M (V : Set -> Set) : Set where
  field
    new : {{lat : Lattice A}} -> A -> M (V A)
    get : V A -> M A
    modify : {{lat : Lattice A}} -> V A -> (A -> A -x- B) -> M B

    overlap {{mon}} : Monad M
  --open Monad mon public
    --Properties:.
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
  modify' p f = modify p (\ x -> (f x , tt) )

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
  modify' p f = modify p (\ x -> (f x , tt))

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

record LatCont (C : Set -> Set) : Set where
  field
    {{cont}} : Container C
    {{lat}} : {A} -> Lattice (C A)


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

{-}
--TODO: Does not terminate yet (might have circular reasons)

getRecReasons : {lvm : CLLatVarMonad M V C} -> V A -> M (AsmCont C V)
getRecReasons {lvm = lvm} p = do
    res <- getReasons p
    if null $ filter null res
    then let res' = head res in join $ forM res' getRecReasons
    else return empty
  where open CLLatVarMonad lvm
  -}

instance
  lat-to-tup : {{latA : Lattice A}} -> {{latB : Lattice B}} -> Lattice (A -x- B)
  lat-to-tup {{latA}} {{latB}} = record {
      _/\_ = \(x , y) (x' , y') -> (x /\ x') , (y /\ y') ;
      _\/_ = \(x , y) (x' , y') -> (x \/ x') , (y \/ y') ;
      ltop = ltopA , ltopB ;
      lbot = lbotA , lbotB }
    where
      open Lattice latA renaming (_/\_ to _/\A_; _\/_ to _\/B_; ltop to ltopA; lbot to lbotA)
      open Lattice latB renaming (_/\_ to _/\B_; _\/_ to _\/B_; ltop to ltopB; lbot to lbotB)

  --contLattice : {{cont : Container C}} -> Lattice (C A)
  --contLattice = {!!}

record TrackLatVarMonad M V C : Set where
  field
    lvm : LatVarMonad M V
    getCurrAssignments : M (AsmCont C V)
  open LatVarMonad lvm public

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : {{Monad M}} -> M A -> T M A
open MonadTrans {{...}} public

record StateT S (M : Set -> Set) A : Set where
  constructor StateTC
  field
    runStateT : S -> M (A -x- S)

state : {{mon : Monad M}} -> (S -> (B -x- S)) -> StateT S M B
state f = record { runStateT = return o f }

modifyS : {{mon : Monad M}} -> (S -> S) -> StateT S M T
modifyS f = state (\ s -> (tt , f s))

getS : {{mon : Monad M}} -> StateT S M S
getS = state \ x -> x , x

putS : {{mon : Monad M}} -> S -> StateT S M T
putS s = state $ const $ (tt , s)

evalStateT : {{mon : Monad M}} -> StateT S M B -> S -> M B
evalStateT st s = fst <$> StateT.runStateT st s

data Identity A : Set where
  IdentC : A -> Identity A

runIdentity : Identity A -> A
runIdentity (IdentC x) = x

instance

  functor-stateT : {{Functor M}} -> Functor (StateT S M)
  functor-stateT = record { _<$>_ = \ f m -> StateTC $ ((\(a , s) -> (f a) , s ) <$>_) o StateT.runStateT m }

  applicative-stateT : {{mon : Monad M}} -> Applicative (StateT S M)
  applicative-stateT = record {
      pure = \ a -> StateTC \ s -> pure (a , s) ;
      _<*>_ = \ mf ma -> StateTC \ s -> do
        (f , s') <- StateT.runStateT mf s
        (a , s'') <- StateT.runStateT ma s'
        return (f a , s'')
    }

  monad-stateT : {{mon : Monad M}} -> Monad (StateT S M)
  monad-stateT = record {
    _>>=_ = \ m fm -> record{runStateT = \ s -> (StateT.runStateT m s >>= \ (a , s') -> StateT.runStateT (fm a) s') } }

  StateTMonadTrans : MonadTrans (StateT S)
  StateTMonadTrans = record { liftT = \ m -> StateTC $ \ x -> (\ a -> a , x) <$> m }

  functor-Identity : Functor Identity
  functor-Identity = record { _<$>_ = \ f i -> IdentC (f (runIdentity i)) }

  applicative-Identity : Applicative Identity
  applicative-Identity = record { pure = IdentC ; _<*>_ = \ if i -> IdentC ((runIdentity if) (runIdentity i)) }

  monad-Identity : Monad Identity
  monad-Identity = record { _>>=_ = \ i fi -> fi (runIdentity i) }





LatVarMonad=>TrackLatVarMonad :
  {{cont : Container C}} ->
  {{lat : Lattice (AsmCont C V)}} ->
  LatVarMonad M V ->
  TrackLatVarMonad (StateT (AsmCont C V) M) V C
LatVarMonad=>TrackLatVarMonad {C} lvm = record {
  lvm = record {
    new = liftT o new ;
    get = \ {A = A} p -> do
      v <- liftT (get p)
      modifyS (_/\ singleton {C = C} (A , v , p))
      return v
    ;
    modify = \ p f -> liftT (modify p f) };
  getCurrAssignments = getS
  }
  where
    --monT = monad-stateT
    open LatVarMonad lvm
    --open Monad monT

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


{-# NO_POSITIVITY_CHECK #-}
record FixF (F : (Set -> Set) -> Set -> Set) (A : Set) : Set where
  constructor FixFC
  coinductive
  field
    InF : F (FixF F) A

RecPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set -> Set) -> (A : Set) -> Set
RecPtr V F = FixF (\ V' A -> V (F V' A) )

{-
--does not seem to work...maybe because the coinductive record does not evaluate far enough or something
testRefVarMonad : LatVarMonad M V -> {{cont : LatCont C}} -> LatVarMonad M (RecPtr V (\ V' A -> (A -x- C (Sigma Set V') )))
testRefVarMonad {M} {V = V} {C = C} lvm = record {
    new = new'' ;
    get = ((fst <$>_) o get) o FixF.InF ;
    modify = (\ p f -> modify p \ (x , lst) -> ((fst $ f x) , lst) , (snd $ f x)) o FixF.InF }
  where
    open LatVarMonad lvm
    new'' : {{lat : Lattice A}} -> A -> M $ (RecPtr V (\ V' A -> (A -x- C (Sigma Set V') ))) A
    new'' {A} x = FixFC <$> new {A = A -x- C (Sigma Set (RecPtr V (\ V' A -> (A -x- C (Sigma Set V') ))))} (x , empty)
-}

RecTupPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> Set -> Set
RecTupPtr V F = RecPtr V (\ V' A -> A -x- F V')

ReasPtr : (V : Set -> Set) -> (C : Set -> Set) -> Set -> Set
ReasPtr V C = RecTupPtr V (\ V' -> C $ AsmCont C V')

recProductVarMonad : {V : Set -> Set} -> {F : (Set -> Set) -> Set} ->
  {{lat : Lattice (F (RecTupPtr V F))}} ->
  LatVarMonad M V ->
  LatVarMonad M (RecTupPtr V F) -x- SpecLatVarMonad M (RecTupPtr V F) (F (RecTupPtr V F))
recProductVarMonad lvm = (record {
      new = (FixFC <$>_) o new o (_, ltop) ;
      get = ((fst <$>_) o get) o FixF.InF ;
      modify = (\ p f -> modify p \ (x , lst) -> ((fst $ f x) , lst) , (snd $ f x)) o FixF.InF }) ,
    (record {
      get = ((snd <$>_) o get) o FixF.InF ;
      modify = (\ p f -> modify p \ (x , lst) -> (ltop , (fst $ f $ lst)) , (snd $ f $ lst)) o FixF.InF })
  where open LatVarMonad lvm

reasProductVarMonad : {V : Set -> Set} -> {F : (Set -> Set) -> Set} ->
  {{lat : Lattice (C $ AsmCont C (ReasPtr V C))}} ->
  LatVarMonad M V ->
  LatVarMonad M (ReasPtr V C) -x- SpecLatVarMonad M (ReasPtr V C) (C $ AsmCont C (ReasPtr V C))
reasProductVarMonad lvm = recProductVarMonad lvm


--ProdPtr V (C $ AsmCont C V)
-- V (A -x- C (V (A -x- C (...) )))
-- => PtrTp V C A = V (A -x- PtrTp V C A)
-- => PtrTp V C A = In (V (A -x- PtrTp V C A))
-- => PtrTp V C A = Fix (\ V' -> V (A -x- V'))
--TODO: Tracking should be done separately
--The weird naming is necessary due to a but in my current agda version.
LatVarMonad=>CLLatVarMonad :
  {{cont : Container C}} ->
  -- {{ latFkt : {A : Set} -> Lattice (C A) }} ->
  {{lat : Lattice (AsmCont C (ReasPtr V C))}} ->
  {{latC : Lattice (C $ AsmCont C (ReasPtr V C))}} ->
  LatVarMonad M V ->
  CLLatVarMonad (StateT (AsmCont C (ReasPtr V C)) M) (ReasPtr V C) C --TODO: pointer type here changes. Problem with fixpoint
LatVarMonad=>CLLatVarMonad {C} {V = V} {M = M} lvm = record {
    lvm = record {
      new = \x -> do
        p <- new x
        r <- getCurrAssignments
        putR p (singleton r)
        return p
      ;
      get = get ;
      modify = \ p f -> getCurrAssignments >>= \r -> putR p (singleton r) >> modify p f } ;
      --TODO: maybe putting the reason and the value should be just one modify operation...
      --TODO: this currently does not store which part of the lattice the reason caused...
    getReasons = getR }
  where
    tpl = reasProductVarMonad {C = C} {F = AsmCont C} lvm
    lvm' = fst $ tpl
    reaslvm = snd $ tpl
    traclvm = LatVarMonad=>TrackLatVarMonad lvm'
    liftReaslvm = liftSpecLatVarMon reaslvm
    open TrackLatVarMonad traclvm
    open SpecLatVarMonad liftReaslvm renaming (get to getR; modify to modifyR; put to putR)


-------------------------------------------------
-- Default VarMonad
-------------------------------------------------
open import Data.Nat.Properties renaming (<-strictTotalOrder to NatSTO)
open import Data.Tree.AVL.Map NatSTO renaming (empty to empty-map)


record NatPtr (A : Set) : Set where
  constructor ptr
  field
    idx : Nat

open NatPtr

defaultState : Set
defaultState = Nat -x- Map (Sigma Set id)

defaultInit : defaultState
defaultInit = (0 , empty-map)

open import Agda.Builtin.TrustMe
postulate dummy : {A : Set} -> A

safeLookup : NatPtr A -> Map (Sigma Set id) -> A
safeLookup {A} (ptr p) mp with lookup p mp
safeLookup {A} (ptr p) mp | just (B , b) with primTrustMe {x = A} {y = B}
safeLookup {A} (ptr p) mp | just (B , b) | refl = b
safeLookup {A} (ptr p) mp | nothing = dummy

defaultVarMonad : VarMonad (StateT defaultState Identity) NatPtr
defaultVarMonad = record {
    new = \ {A} x -> state \ (n , mp) -> (ptr n) , (suc n , insert n (A , x) mp) ;
    get = \ { {A} p -> state \ (n , mp) -> safeLookup p mp , (n , mp) } ;
    modify = \ {A} p f -> state \ (n , mp) -> let
      oldCont = safeLookup p mp
      (v , res) = f oldCont
      in res , (n , insert (idx p) (A , v) mp)
  }

instance
  list-container : Container List
  list-container = record {
    empty = [] ;
    singleton = \ x -> [ x ] }

  list-lattice : {A : Set} -> Lattice (List A)
  list-lattice = record { --TODO: this does not make sense!
    _/\_ = _++_ ;
    _\/_ = _++_ ;
    ltop = [] ;
    lbot = [] }

  nat-lattice : Lattice Nat
  nat-lattice = record { --TODO: does not make sense!
    _/\_ = _+_ ;
    _\/_ = _+_ ;
    ltop = 0 ;
    lbot = 0 }

test : Nat
test = fst $ runIdentity $ StateT.runStateT act (0 , empty-map)
  where
    open VarMonad defaultVarMonad
    act = (_* 10) <$> (new 10 >>= \p -> modify' p (_+ 3) >> get p)

--test2 : Nat
test2 = runIdentity $ flip evalStateT defaultInit $ flip evalStateT [] mond
  where
    cllvm : CLLatVarMonad
      (StateT (AsmCont List (ReasPtr NatPtr List)) (StateT defaultState Identity))
      (ReasPtr NatPtr List)
      List
    cllvm = LatVarMonad=>CLLatVarMonad (VarMonad=>LatVarMonad defaultVarMonad)
    open CLLatVarMonad cllvm
    --mond : StateT (AsmCont List (ReasPtr NatPtr List)) (StateT defaultState Identity) Nat
    mond = do
      p1 <- new 5
      p2 <- new 7
      vp <- get p1
      vp' <- get p2
      put p1 2
      vp'' <- get p1
      put p1 1
      getReasons p1


{-
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
-}

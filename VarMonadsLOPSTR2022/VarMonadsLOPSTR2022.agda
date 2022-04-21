{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.VarMonadsLOPSTR2022 where

open import AgdaAsciiPrelude.AsciiPrelude

open import Category.Functor renaming (RawFunctor to Functor)
open import Category.Applicative renaming (RawApplicative to Applicative)
open import Category.Monad renaming (RawMonad to Monad; RawMonadPlus to MonadPlus)
open import Category.Monad.State renaming (RawMonadState to MonadState)

open Functor {{...}} --renaming (_<$>_ to fmap)
open Applicative {{...}} hiding (_<$>_) renaming (_⊛_ to _<*>_)
open Monad {{...}} hiding (_<$>_;_⊛_)
open MonadPlus {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_) renaming (∅ to mzero;_∣_ to _<|>_)
open MonadState {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_) renaming (get to getS; put to putS; modify to modifyS)

private
  variable
    A B S : Set
    K C M F V : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : {{mon : Monad M}} -> M A -> T M A
    --overlap {{mon'}} : {{mon : Monad M}} -> Monad (T M)

open MonadTrans {{...}}

instance
  monadApplicative : {{mon : Monad M}} -> Applicative M
  monadApplicative {{mon = mon}} = Monad.rawIApplicative mon

  applicativeFunctor : {{apl : Applicative F}} -> Functor F
  applicativeFunctor {{apl = apl}} = Applicative.rawFunctor apl

  stateTMonad : {{mon : Monad M}} -> Monad (StateT S M)
  stateTMonad {S = S} {{mon = mon}} = StateTMonad S mon

  stateTMonadState : {{mon : Monad M}} -> MonadState S (StateT S M)
  stateTMonadState {S = S} {{mon = mon}} = StateTMonadState S mon

  stateTMonadTrans : MonadTrans (StateT S)
  stateTMonadTrans = record { liftT = \ ma s -> (_, s) <$> ma }

  monadPlusMonad : {{mp : MonadPlus M}} -> Monad M
  monadPlusMonad {{mp = mp}} = MonadPlus.monad mp

{-
Basic VarMonad modelling Haskell pointers. Problem: Not useful for solvers due to complete rewriting of variables.
-}
record BaseVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    get : V A -> M A
    write : V A -> A -> M T
    overlap {{mon}} : Monad M

{-
The Continuation style VarMonad makes the most sense with clause learning, because
with get, the value can really only be used in the concealed context, not in the contexts after. This could still be achieved with forks, however, the forks might depend on previously read values.
-}

{-
whole thing works with normal VarMonads too, if the monad is Alternative. Here, the continuation is harder to achieve.
-}
record ConstrDefVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> M (V A)
    get : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M
  --open Monad mon public

record ConstrVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    get : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M
  --open Monad mon public

AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C $ Sigma Set (\A -> (A -x- V A))

record ConstrTrackVarMonad (K : Set -> Set) (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    cdvm : ConstrDefVarMonad K M V
    getCurrAssignments : M $ AsmCont C V
  open ConstrDefVarMonad cdvm public


ConstrDefVarMonad=>ConstrTrackVarMonad : {{mpc : MonadPlus C}} ->
  ConstrDefVarMonad K M V ->
  ConstrTrackVarMonad K C (StateT (AsmCont C V) M) V
ConstrDefVarMonad=>ConstrTrackVarMonad {C = C} cdvm = record {
    cdvm = record {
      new = liftT new ;
      get = \ {A = A} p -> do
        v <- liftT (get p)
        modifyS (_<|> return (A , v , p))
        return v
        ;
      write = \ p -> liftT o write p } ;
    getCurrAssignments = getS }
  where
    open ConstrDefVarMonad cdvm


{-# NO_POSITIVITY_CHECK #-}
record FixF (F : (Set -> Set) -> Set -> Set) (A : Set) : Set where
  constructor FixFC
  coinductive
  field
    InF : F (FixF F) A

RecPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set -> Set) -> (A : Set) -> Set
RecPtr V F = FixF (\ V' A -> V (F V' A) )

RecTupPtr : (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> Set -> Set
RecTupPtr V F = RecPtr V (\ V' A -> A -x- F V')

ReasPtr : (V : Set -> Set) -> (C : Set -> Set) -> Set -> Set
ReasPtr V C = RecTupPtr V (\ V' -> C $ AsmCont C V')

record ConstrSpecVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) (B : Set) : Set where
  field
    get : {{k : K A}} -> V A -> M B
    write : {{k : K A}} -> V A -> B -> M T
    overlap {{mon}} : Monad M

recProductVarMonad : {V : Set -> Set} -> {F : (Set -> Set) -> Set} ->
  (emptyF : {V' : Set -> Set} -> (F V')) ->
  (emptyA : {A : Set} -> {{k : K A}} -> A) ->
  (tupK : {A : Set} -> {{k : K A}} -> K (A -x- (F (RecTupPtr V F)) ) ) ->
  ConstrVarMonad K M V ->
  ConstrDefVarMonad K M (RecTupPtr V F) -x- ConstrSpecVarMonad K M (RecTupPtr V F) (F (RecTupPtr V F))
recProductVarMonad {K} {V = V} {F = F} emptyF emptyA tupK cdvm = (
  record {
    new = FixFC <$> new {{k = tupK}} (emptyA , emptyF) ;
    get = ((fst <$>_) o get {{k = tupK}}) o FixF.InF ;
    write = (\ p v -> write {{k = tupK}} p (v , emptyF)) o FixF.InF } --this only makes sense with lattices
  ) , (
  record {
    get = ((snd <$>_) o get {{k = tupK}}) o FixF.InF ;
    write = (\ p v -> write {{k = tupK}} p (emptyA , v)) o FixF.InF }
  )
  where
    open ConstrVarMonad cdvm


record ConstrCLVarMonad (K : Set -> Set) (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    cdvm : ConstrDefVarMonad K M V
    getReasons : {{k : K A}} -> V A -> M (C $ AsmCont C V)


ConstrVarMonad=>ConstrCLVarMonad :
  {{mpc : MonadPlus C}} ->
  (emptyC : {V' : Set -> Set} -> (C $ AsmCont C V')) ->
  (emptyA : {A : Set} -> {{k : K A}} -> A) ->
  (tupK : {A : Set} -> {{k : K A}} -> {B : Set} -> K (A -x- B) ) ->
  ConstrVarMonad K M V ->
  ConstrCLVarMonad K C (StateT (AsmCont C (ReasPtr V C)) M) (ReasPtr V C)
ConstrVarMonad=>ConstrCLVarMonad {C} {K} {M = M} {V} emptyC emptyA tupK cvm =
  record {
    cdvm = record {
      new = do
        p <- new
        r <- getCurrAssignments
        writeRes p (return r)
        return p
        ;
      get = get ;
      write = \ p v -> do
        r <- getCurrAssignments
        write p v
        writeRes p (return r)
    } ;
    getReasons = getRes }
  where
    prod = recProductVarMonad emptyC emptyA tupK cvm
    cdvm = fst prod
    specvm : ConstrSpecVarMonad K M (ReasPtr V C) (C $ AsmCont C (ReasPtr V C))
    specvm = snd prod
    tdvm = ConstrDefVarMonad=>ConstrTrackVarMonad cdvm
    liftspecvm : ConstrSpecVarMonad K (StateT (AsmCont C (ReasPtr V C)) M) (ReasPtr V C) (C $ AsmCont C (ReasPtr V C))
    liftspecvm = let open ConstrSpecVarMonad specvm in record {
      get = liftT o get ;
      write = \ p v -> liftT $ write p v }
    open ConstrTrackVarMonad tdvm
    open ConstrSpecVarMonad liftspecvm renaming (get to getRes; write to writeRes)

{-
This VarMonad is needed later when the whole construction is actually done in parallel
-}
record RunnableVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    run : M A -> A or (exists B st V B -x- (B -> M A))

----------------------------------------------------------------------
-- Default memory
----------------------------------------------------------------------

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
safeLookup {A} (ptr p) mp with lookup p mp in eq
safeLookup {A} (ptr p) mp | just (B , b) with primTrustMe {x = A} {y = B}
safeLookup {A} (ptr p) mp | just (B , b) | refl = b
safeLookup {A} (ptr p) mp | nothing = dummy


--------------------------------------------------------------------
--Initial example
--------------------------------------------------------------------

Algebra : (F : Set -> Set) -> (A : Set) -> Set
Algebra F A = F A -> A

Fix : (F : Set -> Set) -> Set
Fix F = forall {A} -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF alg fa = fa alg

MAlgebra : (M : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
MAlgebra M F A = F A -> M A

FixM : (M : Set -> Set) -> (F : Set -> Set) -> Set
FixM M F = forall {A} -> MAlgebra M F A -> M A

foldM : MAlgebra M F A -> FixM M F -> M A
foldM alg fm = fm alg

data _:+:_ (F : Set -> Set) (G : Set -> Set) : Set -> Set where
  Inl : F A -> (F :+: G) A
  Inr : G A -> (F :+: G) A

data ListF (A : Set) : Set -> Set where
  nil : ListF A B
  lcons : A -> B -> ListF A B

[-] : Fix (ListF A)
[-] = \ alg -> alg nil

[-]p : {{bvm : BaseVarMonad M V}} -> FixM M (ListF A o V)
[-]p = \ alg -> alg nil

infixr 1 _:-:_
_:-:_ : A -> Fix (ListF A) -> Fix (ListF A)
_:-:_ a fa = \ alg -> alg (lcons a (foldF alg fa))

infixr 1 _:-:p_
_:-:p_ : {{bvm : BaseVarMonad M V}} ->
  A -> (V $ FixM M (ListF A o V)) -> FixM M (ListF A o V)
_:-:p_ {{bvm = bvm}} a vfa alg = get vfa >>= foldM alg >>= new >>= \ p -> alg (lcons a p)
{-do
    xs <- get vfa
    v <- foldM alg xs
    alg (lcons a v) -}
  where open BaseVarMonad bvm

anyFL : Fix (ListF Bool) -> Bool
anyFL = foldF \ {
  nil -> false;
  (lcons x xs) -> x || xs}

listTest : Bool
listTest = anyFL $ false :-: true :-: false :-: [-]

{-
Problem of the paper: we don't know why the function returned true.
Part of clause learning: Should return that anyFL (false :-: true :-: x) = true
Sure, getting anyFL (x :-: true :-: y) would be better, but would not be an accurate statement that comes from evaluating the function (could be deduced, but in this very example it was important that the first value is false.)

Can be thought bigger when looking at a function sudoku : Field -> Bool. If there is an error where the field is not set corretly, why was that the case?
-}

{-
VarMonad Solution:
-}

RecFPtr : (V : Set -> Set) -> (F : Set -> Set) -> Set
--RecFPtr V F = V (F (V $ RecFPtr V F))
RecFPtr V F = Fix (F o V)

varMonadSolution : {{bvm : BaseVarMonad M V}} -> M Bool
varMonadSolution {{bvm = bvm}} = do
    nl <- new [-]p
    c1 <- new $ true :-:p {!!}
    return false
  where open BaseVarMonad bvm

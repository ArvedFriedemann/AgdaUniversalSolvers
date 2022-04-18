{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --overlapping-instances #-}
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
open MonadPlus {{...}} hiding (_<$>_;_⊛_;return;_>>=_) renaming (∅ to mzero)
open MonadState {{...}} hiding (_<$>_;_⊛_;return;_>>=_) renaming (get to getS; put to putS; modify to modifyS)

private
  variable
    A B S : Set
    K C M F V : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : {{mon : Monad M}} -> M A -> T M A
    overlap {{mon'}} : {{mon : Monad M}} -> Monad (T M)

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

AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C $ Sigma Set (\A -> (A -x- V A))

record ConstrTrackVarMonad (K : Set -> Set) (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    cdvm : ConstrDefVarMonad K M V
    getCurrAssignments : M $ AsmCont C V
  open ConstrDefVarMonad cdvm public

open import Agda.Builtin.Equality.Rewrite

id-rew : {C : Set -> Set} -> (\ x -> C x) === C
id-rew = refl

--{-# REWRITE id-rew #-}

ConstrDefVarMonad=>ConstrTrackVarMonad : {{mpc : MonadPlus C}} ->
  ConstrDefVarMonad K M V ->
  ConstrTrackVarMonad K C (StateT (AsmCont C V) M) V
ConstrDefVarMonad=>ConstrTrackVarMonad {C = C} cdvm = record {
    cdvm = record {
      new = liftT new ;
      get = \ p -> liftT (get p) >>= \ v -> {!  !} ;
      write = \ p -> liftT o write p } ;
    getCurrAssignments = getS }
  where
    open ConstrDefVarMonad cdvm
    --open Monad (ConstrDefVarMonad.mon cdvm) renaming (_>>=_ to _>>=p_)



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
--Continuation style monad
--------------------------------------------------------------------

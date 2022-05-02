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
--open import Function.Identity.Categorical renaming (monad to monad-identity)
--open import Function.Identity.Instances


open Functor {{...}} --renaming (_<$>_ to fmap)
open Applicative {{...}} hiding (_<$>_) renaming (_⊛_ to _<*>_)
open Monad {{...}} hiding (_<$>_;_⊛_;pure)
open MonadPlus {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (∅ to mzero;_∣_ to _<|>_)
open MonadState {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (get to getS; put to putS; modify to modifyS)

private
  variable
    A B D S : Set
    K C M F V : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : {{mon : Monad M}} -> M A -> T M A
    --overlap {{mon'}} : {{mon : Monad M}} -> Monad (T M)

open MonadTrans {{...}}

data Identity A : Set where
  IdentC : A -> Identity A

runIdentity : Identity A -> A
runIdentity (IdentC x) = x

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

  monadIdentity : Monad Identity
  monadIdentity =  record {
    return = IdentC ;
    _>>=_ = \ i fi -> fi (runIdentity i) }

{-
Basic VarMonad modelling Haskell pointers. Problem: Not useful for solvers due to complete rewriting of variables.
-}
record BaseVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    get : V A -> M A
    write : V A -> A -> M T
    overlap {{mon}} : Monad M

----------------------------------------------------------------
--MTC initial example
----------------------------------------------------------------

Algebra : (F : Set -> Set) -> (A : Set) -> Set
Algebra F A = F A -> A

Fix : (F : Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF {A = A} alg f = f A alg

data ListF (A : Set) (B : Set) : Set where
  nil : ListF A B
  lcons : A -> B -> ListF A B


mapListF : (B -> D) -> ListF A B -> ListF A D
mapListF f nil = nil
mapListF f (lcons x lst) = lcons x (f lst)

instance
  Functor-ListF : Functor (ListF A)
  Functor-ListF = record { _<$>_ = mapListF }

In : {{func : Functor F}} -> F (Fix F) -> Fix F
In f B alg = alg (foldF alg <$> f)

[-] : Fix (ListF A)
[-] = In nil

_:-:_ : A -> Fix (ListF A) -> Fix (ListF A)
_:-:_ x xs = In (lcons x xs)

anyF : Fix (ListF Bool) -> Bool
anyF = foldF \ {
  nil -> false;
  (lcons x xs) -> x || xs}

---------------------------------------------------------------
--MTC with VarMonads
---------------------------------------------------------------

MAlgebra : (M : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
MAlgebra M F A = F A -> M A

FixM : (M : Set -> Set) -> (F : Set -> Set) -> Set
FixM M F = forall A -> MAlgebra M F A -> M A

foldM : MAlgebra M F A -> FixM M F -> M A
foldM {A = A} alg f = f A alg

record MFunctor (M : Set -> Set) (F : Set -> Set) : Set where
  field
    _<$M>_ : (A -> M B) -> F A -> M (F B)

instance
  Functor-MFunctor : {{func : Functor F}} -> {{bvm : BaseVarMonad M V}} -> MFunctor M (F o V)
  Functor-MFunctor {F} {M} {V} {{bvm = bvm}} = record {
      _<$M>_ = \ {A = A} {B = B} f fa -> let
        tmp : F (M B)
        tmp = ((_>>= f) o get) <$> fa
        in {!!} } --(f o get) <$> fa
    where open BaseVarMonad bvm
---------------------------------------------------------------
-- Variable tracking
---------------------------------------------------------------

AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C $ Sigma Set (\A -> (A -x- V A))

record TrackVarMonad (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    bvm : BaseVarMonad M V
    getCurrAssignments : M $ AsmCont C V
  open BaseVarMonad bvm public


BaseVarMonad=>ConstrTrackVarMonad : {{mpc : MonadPlus C}} ->
  BaseVarMonad M V ->
  TrackVarMonad C (StateT (AsmCont C V) M) V
BaseVarMonad=>ConstrTrackVarMonad {C = C} bbvm = record {
    bvm = record {
      new = liftT o new ;
      get = \ {A = A} p -> do
        v <- liftT (get p)
        modifyS (_<|> return (A , v , p))
        return v
        ;
      write = \ p -> liftT o write p } ;
    getCurrAssignments = getS }
  where
    open BaseVarMonad bbvm

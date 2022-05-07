{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.Examples where

open import AgdaAsciiPrelude.AsciiPrelude
open import VarMonadsLOPSTR2022.VarMonadsLOPSTR2022

private
  variable
    A B D S : Set
    K C M F V : Set -> Set

open import Category.Functor renaming (RawFunctor to Functor)
open import Category.Applicative renaming (RawApplicative to Applicative)
open import Category.Monad renaming (RawMonad to Monad; RawMonadPlus to MonadPlus)
open import Category.Monad.State renaming (RawMonadState to MonadState)
--open import Function.Identity.Categorical renaming (monad to monad-identity)
--open import Function.Identity.Instances

open import Data.List.Categorical using () renaming (monadPlus to listMonadPlus)
import Data.List.Categorical as LCat
open LCat.TraversableM {{...}}

open Functor {{...}} --renaming (_<$>_ to fmap)
open Applicative {{...}} hiding (_<$>_) renaming (_⊛_ to _<*>_)
open Monad {{...}} hiding (_<$>_;_⊛_;pure)
open MonadPlus {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (∅ to mzero;_∣_ to _<|>_)
open MonadState {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (get to getS; put to putS; modify to modifyS)


------------------------------------------------------
--Initial Example Lists
------------------------------------------------------

[]M : {{bvm : BaseVarMonad M V}} -> FixM M (ListF A o V)
[]M = InM nil

_::M_ : {{bvm : BaseVarMonad M V}} -> A -> V $ FixM M (ListF A o V) -> FixM M (ListF A o V)
_::M_ x xs = InM $ lcons x xs

_::VM_ : {{bvm : BaseVarMonad M V}} -> A -> M $ FixM M (ListF A o V) -> M $ FixM M (ListF A o V)
_::VM_ {{bvm = bvm}} x m = (x ::M_) <$> (m >>= new)
  where open BaseVarMonad bvm

foldBVM :
  {{bvm : BaseVarMonad M V}} ->
  {{mfunc : MFunctor M F}} ->
  Algebra F A -> FixM M (F o V) -> M A
foldBVM {{bvm = bvm}} alg = foldM \ f -> alg <$> (get <$M> f)
  where open BaseVarMonad bvm


anyM : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons x xs) -> (x ||_) <$> get xs }
  where open BaseVarMonad bvm

--this reads more values than it needs to

anyM' : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyM' = foldBVM \ {
  nil -> false;
  (lcons x xs) -> x || xs }

anyOptiM : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyOptiM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons true xs) -> return true;
    (lcons false xs) -> get xs}
  where open BaseVarMonad bvm

-- anyTest :
anyTest = runDefTrackVarMonad $ do
  return 5

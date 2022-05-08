{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
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

open Monad {{...}}
open MonadPlus {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (∅ to mzero;_∣_ to _<|>_)
open MonadState {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (get to getS; put to putS; modify to modifyS)


------------------------------------------------------
--Initial Example Lists
------------------------------------------------------

LVMFunc : {{bvm : BaseVarMonad M V}} -> MFunctor M (ListF A o V)
LVMFunc {{bvm}} = BVM-MFunctor {{bvm}} {{ListF-MFunctor}}

[]M : {{bvm : BaseVarMonad M V}} -> FixM M (ListF A o V)
[]M {{bvm}} = InM {{LVMFunc}} nil


_::M_ : {{bvm : BaseVarMonad M V}} -> A -> V $ FixM M (ListF A o V) -> FixM M (ListF A o V)
_::M_ {{bvm}} x xs = InM {{LVMFunc}} $ lcons x xs

[]VM : {{bvm : BaseVarMonad M V}} -> M $ FixM M (ListF A o V)
[]VM = return []M

infixr 5 _::VM_

_::VM_ : {{bvm : BaseVarMonad M V}} -> A -> M $ FixM M (ListF A o V) -> M $ FixM M (ListF A o V)
_::VM_ {{bvm = bvm}} x m = (x ::M_) <$> (m >>= new)
  where open BaseVarMonad bvm

foldBVM :
  {{bvm : BaseVarMonad M V}} ->
  {{mfunc : MFunctor M F}} ->
  Algebra F A -> FixM M (F o V) -> M A
foldBVM {{bvm}} {{mfunc}} alg = foldM \ f -> alg <$> (get <$M>' f)
  where
    open BaseVarMonad bvm
    open MFunctor mfunc renaming (_<$M>_ to _<$M>'_)

toList : {{bvm : BaseVarMonad M V}} -> FixM M (ListF Bool o V) -> M (List Bool)
toList = foldBVM {{mfunc = ListF-MFunctor}} \{
  nil -> [];
  (lcons x xs) -> x :: xs }

anyM : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons x xs) -> (x ||_) <$> get xs }
  where open BaseVarMonad bvm

--this reads more values than it needs to

anyM' : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyM' = foldBVM {{mfunc = ListF-MFunctor}} \ {
  nil -> false;
  (lcons x xs) -> x || xs }

anyOptiM : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyOptiM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons true xs) -> return true;
    (lcons false xs) -> get xs}
  where open BaseVarMonad bvm



instance
  MFunctor-TupPtr : {{bvm : BaseVarMonad M V}} -> {A : Set} -> MFunctor M (\ R -> V (List R))
  MFunctor-TupPtr {{bvm = bvm}} = record { _<$M>_ = \ f fx -> get fx >>= \ lst -> sequenceM (map f lst) >>= new }
    where open BaseVarMonad bvm

module Temp where
  open BaseVarMonad defaultVarMonad
  instance
    bvm = defaultVarMonad
  listTest : Bool
  listTest = runDefVarMonad $
    false ::VM true ::VM false ::VM []VM >>= anyOptiM

module Temp2 where
  open TrackVarMonad (BaseVarMonad=>TrackVarMonad defaultVarMonad)
  instance
    bvmi = bvm

  run : StateT (AsmCont List NatPtr) defaultVarMonadStateM A -> A
  run = runDefVarMonad o \ m -> fst <$> m []
  listTest = run $
    false ::VM true ::VM false ::VM []VM >>= anyOptiM >> getCurrAssignments

  asmTest = run $ do
    true ::VM []VM >>= toList


instance
  defCLVarMonad = CLVarMonad.bvm defaultCLVarMonad


open CLVarMonad defaultCLVarMonad
--open BaseVarMonad (CLVarMonad.bvm defaultCLVarMonad)

--anyTest : List (AsmCont List _)
--anyTest : List Nat
--anyTest : List $ List Nat
anyTest = runDefTrackVarMonad $ do
  p <- false ::VM true ::VM false ::VM []VM >>= anyOptiM >>= new
  res <- getReasons p
  return $ map (map \ (T , v , p) -> idx p) res

reasonTest : List (AsmCont List _)
reasonTest = runDefTrackVarMonad $ do
  p <- new 5
  get p
  write p 6
  getReasons p

--reasonRet : (AsmCont List _)
reasonRet = runDefTrackVarMonad $ do
    p <- new 5
    get p
    get p
    getCurrAssignments

--AsmContTest : FixM defaultCLVarMonadStateM (\ R -> defaultCLVarMonadV (List R))
AsmContTest = runDefTrackVarMonad $ return 5 --InM <$> new {A = List (FixM defaultCLVarMonadStateM (\ R -> defaultCLVarMonadV (List R))) } []

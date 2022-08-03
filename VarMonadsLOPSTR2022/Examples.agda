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

open Functor {{...}} renaming (_<$>_ to _<$>'_)

open import Data.List.Categorical using () renaming (monadPlus to listMonadPlus)
import Data.List.Categorical as LCat
--open LCat.TraversableM {{...}}

------------------------------------------------------
--Initial Example Lists
------------------------------------------------------

[]M : {{bvm : BaseVarMonad M V}} -> Fix (ListF A o V)
[]M {{bvm}} = In nil


_::M_ : {{bvm : BaseVarMonad M V}} -> A -> V $ Fix (ListF A o V) -> Fix (ListF A o V)
_::M_ {{bvm}} x xs = In $ lcons x xs

[]VM : {{bvm : BaseVarMonad M V}} -> M $ Fix (ListF A o V)
[]VM = return []M

infixr 5 _::VM_

_::VM_ : {{bvm : BaseVarMonad M V}} -> A -> M $ Fix (ListF A o V) -> M $ Fix (ListF A o V)
_::VM_ {{bvm = bvm}} x m = (x ::M_) <$> (m >>= new)
  where open BaseVarMonad bvm

instance
  Comp-Functor : {{f1 : Functor F}} -> {{f2 : Functor V}} -> Functor (F o V)
  Comp-Functor {{f1}} {{f2}} = record { _<$>_ = \ f fva -> (f <$>2_) <$>1 fva }
    where
      open Functor f1 renaming (_<$>_ to _<$>1_)
      open Functor f2 renaming (_<$>_ to _<$>2_)


foldBVM :
  {{bvm : BaseVarMonad M V}} ->
  {{mfunc : Functor F}} ->
  Algebra F (M A) -> Fix (F o V) -> M A
foldBVM {{bvm}} {{mfunc}} alg = foldF \ _ [[_]] f -> alg _ (get >=> [[_]]) f --alg <$> (get <$>' f)
  where
    open BaseVarMonad bvm
    open Functor mfunc renaming (_<$>_ to _<$>'_)

toList : {{bvm : BaseVarMonad M V}} -> {{vfunc : Functor V}} ->
  Fix (ListF Bool o V) -> M (List Bool)
toList {V = V} = foldBVM {F = ListF Bool} {{mfunc = ListF-MTCFunctor}} \{
  _ [[_]] nil -> return [];
  _ [[_]] (lcons x xs) -> (x ::_) <$> [[ xs ]] }

anyM : {{bvm : BaseVarMonad M V}} -> Fix ((ListF Bool) o V) -> M Bool
anyM {{bvm = bvm}} = foldF \ {
    _ [[_]] nil -> return false;
    _ [[_]] (lcons x xs) -> (x ||_) <$> (get xs >>= [[_]]) }
  where open BaseVarMonad bvm

--this reads more values than it needs to

anyM' : {{bvm : BaseVarMonad M V}} -> Fix ((ListF Bool) o V) -> M Bool
anyM' = foldBVM {F = ListF Bool} {{mfunc = ListF-MTCFunctor}} \ {
  _ [[_]] nil -> return false;
  _ [[_]] (lcons x xs) -> (x ||_) <$> [[ xs ]] }

anyOptiM : {{bvm : BaseVarMonad M V}} -> Fix ((ListF Bool) o V) -> M Bool
anyOptiM {{bvm = bvm}} = foldF \ {
    _ [[_]] nil -> return false;
    _ [[_]] (lcons true xs) -> return true;
    _ [[_]] (lcons false xs) -> get xs >>= [[_]] }
  where open BaseVarMonad bvm



instance
  MFunctor-TupPtr : {{bvm : BaseVarMonad M V}} -> {{vfunc : Functor V}} -> {A : Set} -> Functor (\ R -> V (List R))
  MFunctor-TupPtr {{bvm = bvm}} {{vfunc = vfunc}} = record { _<$>_ = \ f fx -> (map f) <$>v fx }
    where
      open BaseVarMonad bvm
      open Functor vfunc renaming (_<$>_ to _<$>v_)


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
    true ::VM []VM >>= toList {{vfunc = NatPtrFunctor}}


instance
  defCLVarMonad = CLVarMonad.bvm defaultCLVarMonad


open CLVarMonad defaultCLVarMonad
--open BaseVarMonad (CLVarMonad.bvm defaultCLVarMonad)

open import Agda.Builtin.TrustMe

trustVal : (a : A) -> B
trustVal {A} {B} a with primTrustMe {x = A} {y = B}
...| refl = a

--anyTest : List (AsmCont List _)
--anyTest : List Nat
anyTest : List $ List (Nat)
anyTest = runDefTrackVarMonad $ do
  p <- false ::VM true ::VM false ::VM []VM >>= anyOptiM >>= new
  res <- getReasons p
  sequenceM $ map (sequenceM o map \ (T , v , d) -> return (idx d) ) res

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

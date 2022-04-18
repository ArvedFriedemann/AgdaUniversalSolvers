{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.VarMonadsLOPSTR2022 where

open import AgdaAsciiPrelude.AsciiPrelude

open import Category.Monad renaming (RawMonad to Monad)
--open import Category.Monad.State

open Monad {{...}}

private
  variable
    A B : Set
    C M F V : Set -> Set

{-
Basic VarMonad modelling Haskell pointers. Problem: Not useful for solvers due to complete rewriting of variables.
-}
record BaseVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    get : V A -> M A
    write : V A -> A -> M T

{-
This VarMonad uses continuation style variable reading. This works well with lattice structures or MVars
-}
record ContVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : M (V A)
    get : V A -> (A -> M T) -> M T
    write : V A -> A -> M T --This cannot rewrite values,

{-
The Continuation style VarMonad makes the most sense with clause learning, because
with get, the value can really only be used in the concealed context, not in the contexts after. This could still be achieved with forks, however, the forks might depend on previously read values.
-}

{-
A VarMonad with constraints (like eq or lattice) to the values.
-}
record ConstrContVarMonad (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{C A}} -> A -> M (V A)
    get : {{C A}} -> V A -> (A -> M T) -> M T
    write : {{C A}} -> V A -> A -> M T

{-
whole thing works with normal VarMonads too, if the monad is Alternative. Here, the continuation is harder to achieve.
-}
record ConstrDefVarMonad (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{C A}} -> M (V A)
    get : {{C A}} -> V A -> M A
    write : {{C A}} -> V A -> A -> M T

record RunnableVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    run : M A -> A or (Sigma Set \ B -> V B -x- (B -> M A))

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
{-
data FreeVarMonad (V : Set -> Set) : Set -> Set where
  new : FreeVarMonad V (V A)
  get : V A -> FreeVarMonad V A
  write : V A -> A -> FreeVarMonad V T
  return : FreeVarMonad V A
  bind : FreeVarMonad V A -> (A -> FreeVarMonad V B) -> FreeVarMonad V B
-}

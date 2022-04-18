{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.VarMonadsLOPSTR2022 where

open import AgdaAsciiPrelude.AsciiPrelude

open import Category.Monad renaming (RawMonad to Monad)


open Monad {{...}}

private
  variable
    A B : Set
    C M F : Set -> Set

test : {{Monad M}} -> M T
test = return tt

test2 : Nat
test2 = 0 * 0

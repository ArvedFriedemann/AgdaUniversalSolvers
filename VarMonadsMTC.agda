{-# OPTIONS --rewriting --guardedness #-}
{-# OPTIONS --type-in-type #-}

module VarMonadsMTC where

open import VarMonadsMTC.VarMonadsMTC

open import AgdaAsciiPrelude.AsciiPrelude

open import IO
open import Data.Nat.Show using (show)
open import Agda.Builtin.IO

main : Agda.Builtin.IO.IO T
main = run {!!}

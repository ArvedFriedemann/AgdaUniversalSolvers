module AsciiPrelude where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_) public
open Eq.≡-Reasoning using (begin_) renaming (_≡⟨⟩_ to _=<>_; step-≡ to step-=; _∎ to _qed) public

open import Function renaming (_∘_ to _o_) public

open import Data.Product renaming (_×_ to _and_; proj₁ to fst; proj₂ to snd) public
open import Data.Unit renaming (⊤ to T; tt to top) public
open import Data.Sum renaming ([_,_] to case-or; _⊎_ to _or_; inj₁ to left; inj₂ to right) public
open import Data.Empty renaming (⊥ to BOT; ⊥-elim to absurd) public

open import Data.Product renaming (Σ to sigma; ∃ to exists) public

sigma-syntax = sigma
infix 2 sigma-syntax
syntax sigma-syntax A (\ x -> B) = exists x of A st B

exists-syntax = exists
syntax exists-syntax (\ x -> B) = exists x st B

open import Data.List public


--

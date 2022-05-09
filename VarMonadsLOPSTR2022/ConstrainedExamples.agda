{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.ConstrainedExamples where

open import AgdaAsciiPrelude.AsciiPrelude
open import VarMonadsLOPSTR2022.VarMonadsConstrained

private
  variable
    A B D S : Set
    K C M F V : Set -> Set

instance
  cvmi = defaultConstrCLVarMonad

open ConstrCLVarMonad defaultConstrCLVarMonad

instance
  showNat : Show Nat
  showNat = ShowC showN

test1 : String
test1 = runDefConstrTrackVarMonad $ do
  p <- new 5
  p' <- new 6
  get p
  get p'
  --show <$> getCurrAssignments
  pw <- new 0
  write pw 8
  --show {{showDefReasons}} <$> getReasons pw
  get p
  write pw 9
  show {{showDefReasons}} <$> getReasons pw

module LatticeSolverNew.LatticeSolverNew where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l' l'' l1 l2 l3 : Level
    A B C D L K : Set l
    F G H M V : Set l -> Set l

record Lattice (L : Set l) : Set l where
  infixr 6 _/\_
  infixr 5 _\/_
  field
    _/\_ : L -> L -> L
    _\/_ : L -> L -> L
    ltop : L
    lbot : L
open Lattice {{...}} public

_leq_ : {{_ : Lattice L}} -> L -> L -> Set _
l1 leq l2 = exists x st (l1 /\ x === l2)

instance
  funLattice : {{_ : Lattice L}} -> Lattice (A -> L)
  Lattice._/\_ funLattice = \f1 f2 x -> (f1 x) /\ (f2 x)
  Lattice._\/_ funLattice = \f1 f2 x -> (f1 x) \/ (f2 x)
  Lattice.ltop funLattice = const ltop
  Lattice.lbot funLattice = const lbot

record Extractor (L : Set l) : Set l where
  field
    extract : L -> (L -> L)
open Extractor {{...}} public

record ExtractorLattice (L : Set l) : Set l where
  field
    {{lat-inst}} : Lattice L
    {{extr-inst}} : Extractor L

propagate : {{_ : ExtractorLattice L}} -> Nat -> L -> L
propagate 0 l = l
propagate (suc n) l = propagate n ((extract l $ l) /\ l)

record LatticePart (L : Set l) (A : Set l) : Set l where
  field
    get : L -> A
    put : A -> L
{-
Problem: functions always need to be able to create new variables. Problem is, that the new lattice part needs to be created first, which technically requires a state. possible fix: Return as a lattice thing an operation, that creates a variable on meet.
-}

record CreatorLattice (L : Set l) : Set l where
  field
    c-op : (LatticePart L A -> L) -> L
open CreatorLattice {{...}} public
--TODO: properties

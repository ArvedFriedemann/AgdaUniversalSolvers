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


_:-*_ : {L : Set l} -> {{_ : ExtractorLattice L}} ->
  L -> L -> Set l
l1 :-* l2 = exists n st (propagate n l1 === l2)

_eventually_ : {L : Set l} -> {{_ : ExtractorLattice L}} ->
  L -> (L -> Set l) -> Set l
l eventually P = exists l' st (l :-* l' and P l')

contains : {{_ : Lattice L}} -> L -> L -> Set _
contains l l' = l leq l'

extract-contains : {{_ : ExtractorLattice L}} -> (L -> L) -> L -> Set _
extract-contains f l' = f leq (extract l')

_ : {{_ : ExtractorLattice L}} ->
    forall l ->
    {P : L -> Set _} ->
    {Q : L -> Set _} ->
    {f : L -> L} ->
    (forall l -> P l -> Q (f l)) ->
    l eventually P ->
    l eventually (extract-contains f) ->
    l eventually Q
_ = {!!}

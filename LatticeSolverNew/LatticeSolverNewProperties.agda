module LatticeSolverNew.LatticeSolverNewProperties where

open import AgdaAsciiPrelude.AsciiPrelude
open import LatticeSolverNew.LatticeSolverNew


private
  variable
    l l' l'' l1 l2 l3 : Level
    A B C D L K : Set l
    F G H M V : Set l -> Set l

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

{-}
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
-}

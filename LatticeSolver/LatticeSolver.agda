module LatticeSolver.LatticeSolver where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l' l'' l1 l2 l3 : Level
    A B C D L : Set l
    F G H M : Set l -> Set l'

record Lattice (L : Set l) : Set l where
  infixr 6 _/\_
  infixr 5 _\/_
  field
    _/\_ : L -> L -> L
    _\/_ : L -> L -> L
open Lattice {{...}} public

Idempotency : {A : Set l} -> (op : A -> A -> A) -> Set l
Idempotency _op_ = forall x -> x op x === x

Absorption : {A : Set l} -> (op1 : A -> A -> A) -> (op2 : A -> A -> A) -> Set l
Absorption _op1_ _op2_ = forall x y -> x op1 (x op2 y) === x

Associativity : {A : Set l} -> (op : A -> A -> A) -> Set l
Associativity _op_ = forall x y z -> x op (y op z) === (x op y) op z

Commutativity : {A : Set l} -> (op : A -> A -> A) -> Set l
Commutativity _op_ = forall x y -> x op y === y op x

Distributivity : {A : Set l} -> (op1 : A -> A -> A) -> (op2 : A -> A -> A) -> Set l
Distributivity _op1_ _op2_ = forall x y z -> x op1 (y op2 z) === (x op1 y) op2 (x op1 z)

record SemiLatticeProp {L : Set l} (_op_ : L -> L -> L) : Set l where
  field
    idem    : Idempotency _op_
    assoc   : Associativity _op_
    commut  : Commutativity _op_

record LatticeProp {L : Set l} {{Lat : Lattice L}} : Set l where
  field
    semi-/\ : SemiLatticeProp _/\_
    semi-\/ : SemiLatticeProp _\/_
    absorb-\/-/\ : Absorption _\/_ _/\_
    absorb-/\-\/ : Absorption _/\_ _\/_



propagateN : {{_ : DecEq L}} {{_ : Lattice L}} -> (extr : L -> (L -> L)) -> Nat -> L -> L or L
propagateN extr 0 l = right l
propagateN extr (suc n) l with r <- (extr l $ l) /\ l | r == l
... | yes p = left l
... | no ¬p = propagateN extr n r

record Propagator (L : Set l) : Set l where
  field
    e-extract : L -> (L -> L)
    e-remove : L -> (L -> L)
    termination : {{_ : DecEq L}} {{_ : Lattice L}} ->
      exists n st (forall (l : L) -> exists l' of L st propagateN e-extract n l === left l')

  propagate : {{_ : DecEq L}} {{_ : Lattice L}} -> L -> L
  propagate l with (n , r) <- termination | r l
  ...| res , _ = res

  

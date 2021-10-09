module LatticeSolver.LatticeSolver where

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


record _-LP>_ (L : Set l) (K : Set l) : Set l where
  field
    getLP : L -> K
    -- notice: the L that comes out here is the minimum l that adds the given K!
    setLP : L -> K -> L
  -- laws?

record GenLPLattice (L : Set l) {{_ : Lattice L}} : Set (lsuc l) where
  field
    newLP : {{_ : Lattice K}} -> L -> (L -LP> K and L)
open GenLPLattice {{...}} public

record Monad (M : Set l -> Set l) : Set (lsuc l) where
  field
    return : A -> M A
    _>>=_ : M A -> (A -> M B) -> M B

  _>>_ : M A -> M B -> M B
  _>>_ m m' = m >>= const m'

  _>>*_ : M A -> (A -> M B) -> M A
  _>>*_ m m' = m >>= \a -> m' a >> return a
open Monad {{...}} public

record MonadVarLattice (M : Set l -> Set l) (V : Set l -> Set l) : Set (lsuc l) where
  field
    new : {A : Set l} {{_ : Lattice A}} -> M (V A)
    get : {{_ : Lattice A}} -> V A -> M A
    modify : {A B : Set l} {{_ : Lattice A}} -> (A -> A and B) -> V A -> M B
    instance monad-MonadVar : Monad M

  set : {{_ : Lattice A}} -> A -> V A -> M T
  set a = modify (const (a , top))

  modify' : {{_ : Lattice A}} -> (A -> A) -> V A -> M T
  modify' f = modify (\a -> (f a , top))

  new' : {{_ : Lattice A}} -> A -> M (V A)
  new' a = new >>* set a

open MonadVarLattice {{...}} public

State : (S : Set l) -> (A : Set l) -> Set l
State S A = S -> A and S

record MonadState (S : Set l) (M : Set l -> Set l) : Set (lsuc l) where
  field
    state : (S -> S and A) -> M A

  getState : M S
  getState = state (\s -> s , s)

  putState : S -> M T
  putState t = state (\s -> t , top )

open MonadState {{...}} public

PropMonad : {{_ : Lattice L}} {{_ : GenLPLattice L}} {{_ : MonadState L M}} ->
            MonadVarLattice M (L -LP>_)
MonadVarLattice.new PropMonad = {!   !}
MonadVarLattice.get PropMonad = {!   !}
MonadVarLattice.modify PropMonad = {!   !}
MonadVarLattice.monad-MonadVar PropMonad = {!   !}

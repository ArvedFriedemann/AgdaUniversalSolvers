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
open SemiLatticeProp public renaming
  (idem to SLP-idem; assoc to SLP-assoc; commut to SLP-commut)


record LatticeProp (L : Set l) : Set l where
  field
    overlap {{lattice-LatticeProp}} : Lattice L
    semi-/\ : SemiLatticeProp _/\_
    semi-\/ : SemiLatticeProp _\/_
    absorb-\/-/\ : Absorption _\/_ _/\_
    absorb-/\-\/ : Absorption _/\_ _\/_
open LatticeProp {{...}} public


propagateN : {{_ : DecEq L}} {{_ : Lattice L}} -> (extr : L -> (L -> L)) -> Nat -> L -> L or L
propagateN extr 0 l = right l
propagateN extr (suc n) l with r <- (extr l $ l) /\ l | r == l
... | yes p = left l
... | no ¬p = propagateN extr n r

record Propagator (L : Set l) : Set l where
  field
    e-extract : L -> (L -> L)
    e-remove : L -> (L -> L)
open Propagator public

record TerminatingPropagator (L : Set l) : Set l where
  field
    prop : Propagator L
    termination : {{_ : DecEq L}} {{_ : Lattice L}} ->
      exists n st (forall (l : L) -> exists l' of L st propagateN (e-extract prop) n l === left l')

  propagate : {{_ : DecEq L}} {{_ : Lattice L}} -> L -> L
  propagate l with (n , r) <- termination | r l
  ...| res , _ = res


record _-LP>_ (L : Set l) (K : Set l) : Set l where
  field
    getLP : L -> K
    -- notice: the L that comes out here is the minimum l that adds the given K!
    setLP : K -> L
  -- laws?
open _-LP>_ public

record GenLPLattice (L : Set l) : Set (lsuc l) where
  field
    newLP : {{_ : Lattice K}} -> L -> (L and L -LP> K)
  -- overlap {{lattice}} : Lattice L
open GenLPLattice {{...}} public -- hiding (lattice)

record PropLattice (L : Set l) : Set l where
  field
    extractPtr : L -LP> (L -> L)
    removePtr : L -LP> (L -> L)
open PropLattice public

GeneralPropagator :
  PropLattice L ->
  Propagator L
Propagator.e-extract (GeneralPropagator pl) = getLP $ extractPtr pl
Propagator.e-remove (GeneralPropagator pl) = getLP $ removePtr pl

postulate
  extensionality : {f g : A -> B}
    -> ((x : A) -> f x === g x)
      -----------------------
    -> f === g
    {-}
  forall-extensionality : ∀ {f g : (x : A) -> B x}
    -> ((x : A) -> f x === g x)
      -----------------------
    -> f === g
    -}

instance
  funcLattice :
    {{_ : Lattice B}} ->
    Lattice (A -> B)
  (Lattice._/\_ funcLattice) f1 f2 x = (f1 x) /\ (f2 x)
  (Lattice._\/_ funcLattice) f1 f2 x = (f1 x) \/ (f2 x)

  funcLatticeProps : {A : Set l} {{_ : LatticeProp B}} -> LatticeProp (A -> B)
  SemiLatticeProp.idem (LatticeProp.semi-/\ funcLatticeProps) f = extensionality h where
    h : forall x -> (f x) /\ (f x) === f x
    h x with f x
    ...| k = (SLP-idem semi-/\) k
  SemiLatticeProp.assoc (LatticeProp.semi-/\ funcLatticeProps) = {!   !}
  SemiLatticeProp.commut (LatticeProp.semi-/\ funcLatticeProps) = {!   !}
  LatticeProp.semi-\/ funcLatticeProps = {!   !}
  LatticeProp.absorb-\/-/\ funcLatticeProps = {!   !}
  LatticeProp.absorb-/\-\/ funcLatticeProps = {!   !}


--record ScopeProperty (scope : L -LP> L) : Set l where




record Monad (M : Set l -> Set l) : Set (lsuc l) where
  field
    return : A -> M A
    _>>=_ : M A -> (A -> M B) -> M B

  _<*>_ : M (A -> B) -> M A -> M B
  _<*>_ fm m = fm >>= \f -> m >>= \v -> return $ f v

  _<$>_ : (A -> B) -> M A -> M B
  _<$>_ f m = return f <*> m

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
    overlap {{monad-MonadVar}} : Monad M

  set : {{_ : Lattice A}} -> A -> V A -> M T
  set a = modify (const (a , top))

  modify' : {{_ : Lattice A}} -> (A -> A) -> V A -> M T
  modify' f = modify (\a -> (f a , top))

  new' : {{_ : Lattice A}} -> A -> M (V A)
  new' a = new >>* set a

open MonadVarLattice {{...}} public hiding (monad-MonadVar)

State : (S : Set l) -> (A : Set l) -> Set l
State S A = S -> A and S

record MonadState (S : Set l) (M : Set l -> Set l) : Set (lsuc l) where
  field
    state : (S -> S and A) -> M A
    overlap {{monad-MonadState}} : Monad M

  getState : M S
  getState = state (\s -> s , s)

  putState : S -> M T
  putState t = state (\s -> t , top )

open MonadState {{...}} public

PropMonad : {{_ : Lattice L}} {{_ : GenLPLattice L}} {{_ : MonadState L M}} ->
            MonadVarLattice M (L -LP>_)
MonadVarLattice.new PropMonad = state newLP
(MonadVarLattice.get PropMonad) v = getLP v <$> getState
(MonadVarLattice.modify PropMonad) f v = state \l ->
  let (a , b) = f $ getLP v l
  in (l /\ setLP v a , b)

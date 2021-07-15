{-# OPTIONS --rewriting #-}

module SatSolver.SatSolver where

open import AgdaAsciiPrelude.AsciiPrelude
open import Data.Maybe
open import Data.Maybe.Categorical as Maybe
open import Category.Applicative
open import Category.Functor
open import Category.Monad
open import Relation.Nullary.Decidable.Core using (True; False)

private
  variable
    l l' l'' l1 l2 l3 : Level
    A B C D : Set l
    F G H : Set l -> Set l'

data Formula (A : Set l) : Set l where
  ftrue : Formula A
  ffalse : Formula A
  var : A -> Formula A
  :¬:_ : Formula A -> Formula A
  _:^:_ : Formula A -> Formula A -> Formula A
  _:v:_ : Formula A -> Formula A -> Formula A

eval : (model : A -> Bool) -> Formula A -> Bool
eval _ ftrue = true
eval _ ffalse = false
eval m (var x) = m x
eval m (:¬: a) = not (eval m a)
eval m (a :^: b) = (eval m a) && (eval m b)
eval m (a :v: b) = (eval m a) || (eval m b)



--solver proof
-- solver : forall {f : Formula A} -> (exists m st (Tt $ eval m f)) or (forall m -> ¬ (Tt $ eval m f))
-- solver = {!!}

------------------------------------------------
--assigns-to
------------------------------------------------

just-id : {x y : A} -> just x === just y -> x === y
just-id refl = refl

instance
  bool-dec-eq : DecEq Bool
  DecEq._==_ bool-dec-eq true true = yes refl
  DecEq._==_ bool-dec-eq false false = yes refl
  DecEq._==_ bool-dec-eq false true = no (\ ())
  DecEq._==_ bool-dec-eq true false = no (\ ())

  mab-dec-eq : {{DecEq A}} -> DecEq (Maybe A)
  DecEq._==_ mab-dec-eq nothing nothing = yes refl
  DecEq._==_ mab-dec-eq (just _) nothing = no (\ ())
  DecEq._==_ mab-dec-eq nothing (just _) = no (\ ())
  DecEq._==_ mab-dec-eq (just x) (just y) with (x == y)
  ...| yes x=y = yes (cong just x=y)
  ...| no ¬x=y = no $ \ jx=jy -> ¬x=y $ just-id jx=jy

assign :
  {{_ : DecEq A}} ->
  (a : A) -> (b : B) -> (f : A -> Maybe B) ->
  (f a === just b) or (f a === nothing) ->
  ((x : A) -> Maybe B)
assign a b f _ x = ifDec x == a then just b else f x

data _assigns-to_ {A : Set l1} {B : Set l2} (f1 : A -> Maybe B) : (f2 : A -> Maybe B) -> Set (l1 ~U~ l2) where
  assigns-id : f1 assigns-to f1
  assigns-trans : {{_ : DecEq A}} {{_ : DecEq B}} ->
                  (fi : A -> Maybe B) ->
                  f1 assigns-to fi ->
                  (a : A) -> (b : B) ->
                  (safe : (fi a === just b) or (fi a === nothing)) ->
                  f1 assigns-to (assign a b fi safe)

------------------------------------------
--partial evaluation
------------------------------------------


instance
  _ = Maybe.functor
  _ = Maybe.applicative

open RawApplicative {{...}} using (pure) renaming (_⊛_  to _<*>_)
open RawFunctor {{...}} using (_<$>_)
--open RawMonad {{...}}

--TODO: prove that value is deduced if the undeducible value did not matter!
evalPartial : (model : A -> Maybe Bool) -> Formula A -> Maybe Bool
evalPartial _ ftrue = just true
evalPartial _ ffalse = just false
evalPartial m (var x) = m x
evalPartial m (:¬: a) = (| not (evalPartial m a) |)
evalPartial m (a :^: b) with (evalPartial m a)  | (evalPartial m b)
...                         | just false        | x           = just false
...                         | x                 | just false  = just false
...                         | x                 | y           = (| x && y |)
evalPartial m (a :v: b) with (evalPartial m a)  | (evalPartial m b)
...                         | just true         | x           = just true
...                         | x                 | just true   = just true
...                         | x                 | y           = (| x || y |)


------------------------------------------
--solver
------------------------------------------

dec-eq-refl : {x : A} -> {p : Dec (x === x)} -> p === (yes refl)
dec-eq-refl {p = no ¬x=x} = absurd $ ¬x=x refl
dec-eq-refl {p = yes refl} = refl
--{-# REWRITE +dec-eq-refl #-}

ifDec-refl : {a b : B} -> {{decEq : DecEq A}} -> {x : A} -> (ifDec x == x then a else b) === a
ifDec-refl {x = x} with x == x
...| yes x=x = refl
...| no ¬x=x = absurd $ ¬x=x refl


solver' : {{decEq : DecEq A}} ->
  (f : Formula A) -> (m : A -> Maybe Bool) -> (target : Bool) ->
  (evalPartial m f === just target) or (evalPartial m f === nothing) ->
  (exists m' st ((m assigns-to m') and (evalPartial m' f === just target))) or
  (forall m' -> m assigns-to m' -> ¬ (evalPartial m' f === just target))
solver' f m target (left x) = left (m , assigns-id , x)
solver' {{decEq = decEq}} (var x) m target (right y) = left (assign x target m (right y) ,
  assigns-trans m assigns-id x target (right y) ,
  (begin
    assign x target m (right y) x
    =<>
    ifDec x == x then (just target) else m x
    =< ifDec-refl {{decEq = decEq}} >
    just target
    qed))
solver' (:¬: f) m target (right y) = {!   !} -- solver' f m (not target) {!!}
-- let m' = witness (solver' f m target ...)
-- in solver' f1 m' target ... --TODO: get set of all assignments for backtracking!
solver' (f1 :^: f2) m target (right y) = {!   !}
solver' (f1 :v: f2) m target (right y) = {!   !}

module SatSolver.SatSolver where

open import AgdaAsciiPrelude.AsciiPrelude
open import Data.Maybe
open import Data.Maybe.Categorical as Maybe
open import Category.Applicative
open import Category.Functor
open import Category.Monad

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
solver : forall {f} -> (exists m st (Tt $ eval m f)) or (forall m -> ¬ (Tt $ eval m f))
solver = {!!}

solver' : forall {f target m} -> (exists m st (eval m f === target)) or (forall m -> ¬ (eval m f === target))
solver' = {!!}

data _=<mab_ {l} {A : Set l} {B : Set l}: (f1 : A -> Maybe B) -> (f2 : A -> Maybe B) -> Set l where
  leqmab : (f1 : A -> Maybe B) -> (f2 : A -> Maybe B) -> ((a : A) -> (f1 a === f2 a) or (f1 a === nothing)) -> f1 =<mab f2

assign :
  (_==_ : DecEq A) ->
  (f : A -> Maybe B) -> (a : A) -> (b : B) -> (x : A) -> Maybe B
assign _==_ f a b x = ifDec x == a then just b else f x

semi-subst : forall {f a b c} -> a === b -> f a === c -> f b === c
semi-subst refl refl = refl

assign-prop :
  (_==_ : DecEq A) ->
  (f : A -> Maybe B) -> (a : A) -> (b : B) -> Dec (f =<mab (assign _==_ f a b))
assign-prop {A = A} {B = B} _==_ f a b with f a
...                  | nothing = yes $ leqmab f f' (help refl)
  where
        f' : A -> Maybe B
        f' = assign _==_ f a b
        help : (f a === nothing) -> (k : A) -> (f k === f' k) or (f k === nothing)
        help fa=n k with f k
        ...| nothing = right refl
        ...| just _ with k == a
        ...             | yes k=a = semi-subst k=a fa=n
        ...             | no ¬k=a = left refl
...                  | just x = {!!}


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

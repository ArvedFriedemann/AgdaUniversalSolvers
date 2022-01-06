{-# OPTIONS --rewriting #-}

module SatSolver.SatSolver where

open import AgdaAsciiPrelude.AsciiPrelude
open import Data.Maybe hiding (map)
open import Data.Maybe.Categorical as Maybe
open import Category.Applicative
open import Category.Functor
open import Category.Monad
open import Relation.Nullary.Decidable.Core using (True; False)
open import Data.Bool.Properties using (not-injective)
open import Data.List.Relation.Unary.All using (All) renaming
  ( [] to []-all;
    _∷_ to _::-all_;
    map to map-all;
    fromList to fromList-all;
    toList to toList-all)
open import Data.List.Instances
open import Data.Maybe.Instances

open import Agda.Builtin.Equality.Rewrite

private
  variable
    l l' l'' l1 l2 l3 : Level
    A B C D : Set l
    F G H : Set l -> Set l'

infixr 5 _:^:_
infixr 4 _:v:_

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
--assignments
------------------------------------------

assign :
  {{_ : DecEq A}}
  (a : A) -> (b : B) -> (f : A -> Maybe B) ->
  --(f a === just b) or (f a === nothing) ->
  ((x : A) -> Maybe B)
assign a b f {-_-} x = ifDec x == a then just b else f x

assign-prop : {{_ : DecEq A}} {x : A} {m : A -> Maybe B} {target : B} -> assign x target m x === just target
assign-prop {x = x} with x == x
...| yes p = refl
...| no ¬p = absurd $ ¬p refl

gen-asm : (A -> Maybe Bool) -> A -> Bool
gen-asm f a with f a
...            | just x = x
...            | nothing = false

gen-asm-prop : {m : A -> Maybe Bool} {x : A} {t : Bool} -> m x === just t -> gen-asm m x === t
gen-asm-prop {m = m} {x = x} {t = t} mx=jt with m x
...| just t' = just-id mx=jt
gen-asm-prop {m = m} {x = x} {t = t} () | nothing

------------------------------------------
--solver
------------------------------------------

--TODO: safety condition for preassignment
solver :
  {{_ : DecEq A}}
  (f : Formula A) -> (m : A -> Maybe Bool) -> (target : Bool) -> List (A -> Maybe Bool)
solver ftrue m false = []
solver ftrue m true = [ m ]
solver ffalse m false = [ m ]
solver ffalse m true = []
solver (var x) m false with m x --in mxeq
...                     | just false = [ m ]
...                     | just true = []
...                     | nothing = [ assign x false m {-(right mxeq)-} ]
solver (var x) m true with m x --in mxeq
...                     | just false = []
...                     | just true = [ m ]
...                     | nothing = [ assign x true m {-(right mxeq)-} ]
solver (:¬: f) m target = solver f m (not target)
solver (fa :^: fb) m false = solver fa m false ++ solver fb m false
solver (fa :^: fb) m true with fa-lst <- solver fa m true =
  concatMap (\ m' -> solver fb m' true) fa-lst
solver (fa :v: fb) m false with fa-lst <- solver fa m false =
  concatMap (\ m' -> solver fb m' false) fa-lst
solver (fa :v: fb) m true = solver fa m true ++ solver fb m true


solver-test : Maybe $ List (Nat and (Maybe Bool))
solver-test with head $ solver ((var 1) :^: (:¬: (var 2))) (const nothing) true
...| just m = just ( (1 , m 1) :: (2 , m 2) :: [])
...| nothing = nothing

solver-test' : Maybe $ List (Nat and (Maybe Bool))
solver-test' with head $ solver ((var 1) :^: (var 2) :^: (:¬: ((var 1) :^: (var 2)) )) (const nothing) true
...| just m = just ( (1 , m 1) :: (2 , m 2) :: [])
...| nothing = nothing

solver-test'' : Maybe $ List (Nat and (Maybe Bool))
solver-test'' with head $ solver ((:¬: ((var 1) :^: (var 2)) ) :v: (var 1) :^: (var 2) ) (const nothing) true
...| just m = just ( (1 , m 1) :: (2 , m 2) :: [])
...| nothing = nothing


nothing-congruence : {f : A -> B} {k : Maybe A} -> Data.Maybe.map f k === nothing -> k === nothing
nothing-congruence {f = f} {k = nothing} eq = refl

just-congruence : forall {p} -> {f : A -> A} {k : Maybe A} -> ({x : A} -> x === f (f x)) -> Data.Maybe.map f k === just p -> k === just (f p)
just-congruence {f = f} {k = just x} dual-prop refl = cong just dual-prop

target-consistency :
  {{_ : DecEq A}}
  (fa fb : Formula A) (m : A -> Maybe Bool) (target : Bool) ->
  evalPartial m fa === just target ->
  All (\ m' -> evalPartial m' fa === just target) (solver fb m target)
target-consistency fa ftrue m false safety = []-all
target-consistency fa ftrue m true safety = safety ::-all []-all
target-consistency fa ffalse m false safety = safety ::-all []-all
target-consistency fa ffalse m true safety = []-all
target-consistency fa (var x) m false safety with m x in mxeq
... | just false = safety ::-all []-all
... | just true  = []-all
... | nothing  = {!   !} ::-all []-all
target-consistency fa (var x) m true safety with m x in mxeq
... | just false = []-all
... | just true  = safety ::-all []-all
... | nothing  = {!   !} ::-all []-all
target-consistency fa (:¬: fb) m target safety = {!   !}
target-consistency fa (fb :^: fb₁) m target safety = {!   !}
target-consistency fa (fb :v: fb₁) m target safety = {!   !}


solver-correctness : {{_ : DecEq A}}
  (f : Formula A) -> (m : A -> Maybe Bool) -> (target : Bool) ->
  All (\ m -> evalPartial m f === just target) (solver f m target)
solver-correctness ftrue m false = []-all
solver-correctness ftrue m true = refl ::-all []-all
solver-correctness ffalse m false = refl ::-all []-all
solver-correctness ffalse m true = []-all

solver-correctness (var x) m false with m x in mxeq
... | just false = mxeq ::-all []-all
... | just true = []-all
... | nothing = assign-prop {x = x} {m = m} {target = false} ::-all []-all
solver-correctness (var x) m true with m x in mxeq
... | just false = []-all
... | just true  = mxeq ::-all []-all
... | nothing = assign-prop {x = x} {m = m} {target = true} ::-all []-all

solver-correctness (:¬: f) m target with
  solver-correctness f m (not target)
... | IH = map-all (neg-target {f' = f}) IH --TODO: map-all only works iff the carrier-list is the same, which it is not in this case. We need stronger map-all
  where
    neg-target : {m' : A -> Maybe Bool} {f' : Formula A} ->
      evalPartial m' f' === just (not target) -> evalPartial m' (:¬: f') === just target
    neg-target {m' = m'} {f' = f'} eq with evalPartial m' f'
    neg-target refl | just .(not target) = cong just (sym $ double-not' refl)
    neg-target ()   | nothing

solver-correctness (fa :^: fb) m false = {!   !}
solver-correctness (fa :^: fb) m true with solver-correctness fa m true
... | IHfa = {!   !}


solver-correctness (fa :v: fb) m target = {!   !}




--

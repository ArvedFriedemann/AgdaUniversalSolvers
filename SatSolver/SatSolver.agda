-- {-# OPTIONS --rewriting #-}

module SatSolver.SatSolver where

open import AgdaAsciiPrelude.AsciiPrelude
open import Data.Maybe
open import Data.Maybe.Categorical as Maybe
open import Category.Applicative
open import Category.Functor
open import Category.Monad
open import Relation.Nullary.Decidable.Core using (True; False)
open import Data.Bool.Properties using (not-injective)
--open import Data.List.Membership.Propositional using () renaming (_∈_ to _in-list_; _∉_ to _not-in-list)

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
--assignments
------------------------------------------

data ProofPath {A : Set l} (f : Formula A) (m : A -> Bool) (target : Bool) : Set l where
  ptrue :  (s : eval m f === target) -> f === ftrue -> ProofPath f m target
  pfalse :  (s : eval m f === target) -> f === ffalse -> ProofPath f m target
  pvar : (x : A) -> (s : eval m f === target) ->  f === var x ->  ProofPath f m target
  p:¬: : {f' : Formula A} -> (s : eval m f === target) ->  f === :¬: f' ->
          ProofPath f' m (not target) -> ProofPath f m target
  p:^: : {x y : Formula A} -> (s : eval m f === target) ->  f === x :^: y ->
          ((target === true) and (ProofPath x m true) and (ProofPath y m true)) or
          ((target === false) and ((ProofPath x m false) or (ProofPath y m false))) ->
          ProofPath f m target
  p:v: : {x y : Formula A} -> (s : eval m f === target) ->  f === x :v: y ->
          ((target === false) and (ProofPath x m false) and (ProofPath y m false)) or
          ((target === true) and ((ProofPath x m true) or (ProofPath y m true))) ->
          ProofPath f m target

_=PrP=_ : forall {m m' target} {f : Formula A} -> {{_ : DecEq A}} ->
  ProofPath f m target -> ProofPath f m' target -> Bool
(ptrue _ _) =PrP= (ptrue _ _) = true
(pfalse _ _) =PrP= (pfalse _ _) = true
(pvar x _ _) =PrP= (pvar x' _ _) = isYes (x == x')
(p:¬: _ refl p) =PrP= (p:¬: _ refl p') = p =PrP= p'

(p:^: _ refl (left (_ , p1 , p2) )) =PrP= (p:^: _ refl (left (_ , p1' , p2') )) =
  (p1 =PrP= p1') && (p2 =PrP= p2')
(p:^: _ refl (right (_ , left p) )) =PrP= (p:^: _ refl (right (_ , left p') )) =
  (p =PrP= p')
(p:^: _ refl (right (_ , right p) )) =PrP= (p:^: _ refl (right (_ , right p') )) =
  (p =PrP= p')

(p:v: _ refl (left (_ , p1 , p2) )) =PrP= (p:v: _ refl (left (_ , p1' , p2') )) =
  (p1 =PrP= p1') && (p2 =PrP= p2')
(p:v: _ refl (right (_ , left p) )) =PrP= (p:v: _ refl (right (_ , left p') )) =
  (p =PrP= p')
(p:v: _ refl (right (_ , right p) )) =PrP= (p:v: _ refl (right (_ , right p') )) =
  (p =PrP= p')

p1 =PrP= p2 = false

norm-proof-path : (f : Formula A) -> (m : A -> Bool) ->
                  (target : Bool) -> (s : eval m f === target) ->
                  ProofPath f m target
norm-proof-path ftrue m target s = ptrue s refl
norm-proof-path ffalse m target s = pfalse s refl
norm-proof-path (var x) m target s = pvar x s refl
norm-proof-path (:¬: f) m target s = p:¬: s refl (norm-proof-path f m (not target) (not-injective $ double-not' s))
-- ...
norm-proof-path (fa :^: fb) m false s with (eval m fa) == false | (eval m fb) == false
...| yes fa=f | _           = p:^: s refl (right ( refl , left (norm-proof-path fa m false fa=f)))
...| no _     | yes fb=f    = p:^: s refl (right ( refl , right (norm-proof-path fb m false fb=f)))
...| no fa=t  | no  fb=t    = absurd $ case-or fa=t fb=t (and-false s)
norm-proof-path (fa :^: fb) m true s with and-true {eval m fa} {eval m fb} s
...| (fa=t , fb=t) = p:^: s refl (left (refl , norm-proof-path fa m true fa=t , norm-proof-path fb m true fb=t))
-- ...
norm-proof-path (fa :v: fb) m true s with (eval m fa) == true | (eval m fb) == true
...| yes fa=t | _           = p:v: s refl (right ( refl , left (norm-proof-path fa m true fa=t)))
...| no _     | yes fb=t    = p:v: s refl (right ( refl , right (norm-proof-path fb m true fb=t)))
...| no fa=f  | no  fb=f    = absurd $ case-or fa=f fb=f (or-true s)
norm-proof-path (fa :v: fb) m false s with or-false {eval m fa} {eval m fb} s
...| (fa=f , fb=f) = p:v: s refl (left (refl , norm-proof-path fa m false fa=f , norm-proof-path fb m false fb=f))


no-proof-no-assignment : (f : Formula A) -> (m : A -> Bool) -> (target : Bool) ->
  (ProofPath f m target -> BOT) -> eval m f === target -> BOT
no-proof-no-assignment f m target ¬p f=target = absurd $ ¬p $ norm-proof-path f m target f=target

gen-asm : (A -> Maybe Bool) -> A -> Bool
gen-asm f a with f a
...            | just x = x
...            | nothing = false

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


_in-list_ : {A : Set l} (a : A) -> (lst : List A) -> Set l
_in-list_ a lst = exists n st (lookup lst n === a)

SolutionListRaw : forall {l} -> {A : Set l} -> (f : Formula A) -> (m : A -> Maybe Bool) -> (target : Bool) -> Set l
SolutionListRaw  {l = l} {A = A} f m target = List (exists m' of (A -> Maybe Bool) st
                  (m assigns-to m') and (eval (gen-asm m') f === target) )

solution-list : {A : Set l} -> {{decEq : DecEq A}} ->
  (f : Formula A) -> (m : A -> Maybe Bool) -> (target : Bool) ->
  (lst : SolutionListRaw f m target) -> Set l
solution-list {A = A} f m target lst = (forall (m'' : A -> Maybe Bool) -> (safe'' : eval (gen-asm m'') f === target) ->
            (exists m' st exists assigns st (exists safe' st (((m' , assigns , safe') in-list lst) and (Tt $
                (norm-proof-path f (gen-asm m') target safe') =PrP=
                (norm-proof-path f (gen-asm m'') target safe''))) ) ))

solution-list-prop : {{_ : DecEq A}} {f : Formula A} {m : A -> Maybe Bool} {target : Bool} {lst : SolutionListRaw f m target} ->
  solution-list f m target lst -> lst === [] -> (m' : A -> Bool) -> ¬ (eval m' f === target)
solution-list-prop solLst refl m' evmf=t = {!!}


solver' : {{decEq : DecEq A}} ->
  (f : Formula A) -> (m : A -> Maybe Bool) -> (target : Bool) ->
  (evalPartial m f === just target) or (evalPartial m f === nothing) ->
  exists lst st solution-list f m target lst
solver' = {!!}

{-
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
-}




--

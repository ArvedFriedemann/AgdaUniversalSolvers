module MetaComplexity where

open import AsciiPrelude
open import Category.Functor
open RawFunctor {{...}} public

private
  variable
    l l' l'' l1 l2 l3 : Level
    A B C D : Set l
    F G H : Set l -> Set l'

UnaryTC : Set (lsuc $ l ~U~ l')
UnaryTC {l} {l'} = Set l -> Set l'

Graph : (F : UnaryTC {l} {l'}) -> (A : Set l) -> Set (l ~U~ l')
Graph F A = A -> F A

record Container (F : UnaryTC {l} {l'}) : Set (lsuc $ l ~U~ l') where
  infixr 1 _contains_
  infixr 1 _containsT_
  field
    _contains_ : F A -> A -> Bool
  _containsT_ : F A -> A -> Set
  C containsT x = Tt $ C contains x
open Container {{...}} public

successor-tuples : List A -> List (A -x- A)
successor-tuples [] = []
successor-tuples (x :: []) = []
successor-tuples (x :: y :: xs) = (x , y) :: (successor-tuples (y :: xs))

path-over_from_to_ : {A : Set l} -> {{Container F}} -> Graph F A -> A -> A -> Set _
path-over_from_to_ {l} {_} {_} {A} delta a b =
  exists L of (List A) st (Tt $ flip all (successor-tuples L) (\ (x , x') -> delta x contains x')  )

nub : (A -> A -> Bool) -> List A -> Bool
nub _ [] = true
nub eq (x :: xs) = (not $ any (eq x) xs) && (nub eq xs)

record Enumerable (A : Set l) (eq : A -> A -> Bool) : Set l where
  field
    elems : List A
    all-contained : (a : A) -> Tt $ any (eq a) elems
    nub-condition : Tt $ nub eq elems
  total-number : Nat
  total-number = length elems




--

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

--test : {{_ : RawFunctor F}} -> (A -> B) -> F A -> F B
--test f pa = f <$> pa




--

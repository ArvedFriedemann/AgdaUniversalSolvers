module VarMonads.VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l' l'' l1 l2 l3 l4 : Level
    A B C L : Set l
    M V F : Set l -> Set l'

record Functor (F : Set l -> Set l') : Set (lsuc l ~U~ l') where
  field
    _<$>_ : (A -> B) -> F A -> F B


record Applicative (F : Set l -> Set l') : Set (lsuc l ~U~ l') where
  field
    pure : A -> F A
    <*> : F (A -> B) -> F A -> F B
    func : Functor F
  open Functor func public

record Monad (M : Set l -> Set l') : Set (lsuc l ~U~ l') where
  field
    appl : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B
  open Applicative appl public
  return : A -> M A
  return = pure

record VarMonad {lift : Set l -> Set l'} (M : Set l' -> Set l'') (V : Set l -> Set l') : Set (lsuc $ l ~U~ l' ~U~ l'') where
  field
    new : A -> M (V A)
    get : V A -> M (lift A)
    modify : V A -> (A -> A -x- B) -> M B

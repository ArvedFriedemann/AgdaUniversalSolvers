module VarMonads.VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    l l' l'' l1 l2 l3 l4 : Level
    A B C L : Set l
    M : Set l' -> Set l''
    V : Set l -> Set l'

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

record Lattice (A : Set l) : Set l where
  field
    _/\_ : A -> A -> A
    _\/_ : A -> A -> A
    ltop : A
    lbot : A

open Lattice {{...}} public

record VarMonad (M : Set l' -> Set l'') (V : Set l -> Set l') : Set (lsuc $ l ~U~ l' ~U~ l'') where
  field
    lift : Set l -> Set l'

    new : A -> M (V A)
    get : V A -> M (lift A)
    modify : V A -> (A -> A -x- B) -> M B

    mon : Monad M
  open Monad mon public

record LatVarMonad (M : Set l' -> Set l'') (V : Set l -> Set l') : Set (lsuc $ l ~U~ l' ~U~ l'') where
  field
    lift : Set l -> Set l'

    new : {{lat : Lattice A}} -> A -> M (V A)
    get : V A -> M (lift A)
    modify : {{lat : Lattice A}} -> V A -> (A -> A -x- B) -> M B

    mon : Monad M
  open Monad mon public
    --Properties:
    {-
    --value of a variable only every increases exactly by values given through modify
    modprop : (p : V A) -> do
      v <- get p
      m1
      modify p f
      m2
      v' <- get p
      return (v' leq (v /\ (fst $ f v)))
    -}


  new' : {{lat : Lattice A}} -> M (V A)
  new' = new ltop

  modify' : {{lat : Lattice A}} -> V A -> (A -> A) -> M T
  modify' p f = modify p (\ x -> (f x , top) )

  put : {{lat : Lattice A}} -> V A -> A -> M T
  put p v = modify' p (const v)


VarMonad=>LatVarMonad : VarMonad M V -> LatVarMonad M V
VarMonad=>LatVarMonad vm = record {
  lift = lift ;
  new = new ;
  get = get ;
  modify = \ p f -> modify p (\ v -> v /\ fst (f v) , snd (f v)) ;
  mon = mon }
  where open VarMonad vm

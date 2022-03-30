{-# OPTIONS --type-in-type #-}

module VarMonads.VarMonads where

open import AgdaAsciiPrelude.AsciiPrelude

private
  variable
    A B L : Set
    M V F C : Set -> Set

record Functor (F : Set -> Set) : Set  where
  field
    _<$>_ : (A -> B) -> F A -> F B


record Applicative F : Set where
  field
    pure : A -> F A
    <*> : F (A -> B) -> F A -> F B
    func : Functor F
  open Functor func public

record Monad M : Set where
  field
    appl : Applicative M
    _>>=_ : M A -> (A -> M B) -> M B
  open Applicative appl public
  return : A -> M A
  return = pure

record Lattice A : Set where
  field
    _/\_ : A -> A -> A
    _\/_ : A -> A -> A
    ltop : A
    lbot : A

open Lattice {{...}} public

record VarMonad M (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    get : V A -> M A
    modify : V A -> (A -> A -x- B) -> M B

    mon : Monad M
  open Monad mon public



record LatVarMonad M (V : Set -> Set) : Set where
  field
    new : {{lat : Lattice A}} -> A -> M (V A)
    get : V A -> M A
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
  new = new ;
  get = get ;
  modify = \ p f -> modify p (\ v -> v /\ fst (f v) , snd (f v)) ;

  mon = mon }
  where open VarMonad vm

record Container (C : Set -> Set) : Set where
  field
    empty : C A
    singleton : A -> C A
{-}
record LatCont (C : Set -> Set) : Set where
  field
    cont : Container C
    lat : Lattice (C A)
  open Container cont public
  open Lattice lat public
-}

AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C $ Sigma Set (\A -> (A -x- V A))

--TODO: Those need to be threshold functions
IndrAsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
IndrAsmCont C V = C $ Sigma (Set -x- Set) (\ (A , B) -> ((A -> Maybe B) -x- B -x- V A))


record CLLatVarMonad M V C : Set where
  field
    lvm : LatVarMonad M V
    cont : Container C
  open LatVarMonad lvm public
  field
    getReasons : V A -> M (C $ AsmCont C V)

instance
  lat-to-tup : {{latA : Lattice A}} -> {{latB : Lattice B}} -> Lattice (A -x- B)
  lat-to-tup = {!!}

  listLattice : {{Container C}} -> Lattice (C A)
  listLattice = {!!}

LatVarMonad=>CLLatVarMonad : Container C -> LatVarMonad M V -> CLLatVarMonad M (\ A -> V (A -x- (C $ AsmCont C V) )) C
LatVarMonad=>CLLatVarMonad cont lvm = record {
  lvm = record {
    new = \ x -> new (x , empty) ;
    get = {!   !} ;
    modify = {!   !} ;
    mon = {!   !} } ;
  getReasons = {!   !} }
  where
    open LatVarMonad lvm
    open Container cont

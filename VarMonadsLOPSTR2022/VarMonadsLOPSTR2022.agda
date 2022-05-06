{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.VarMonadsLOPSTR2022 where

open import AgdaAsciiPrelude.AsciiPrelude

open import Category.Functor renaming (RawFunctor to Functor)
open import Category.Applicative renaming (RawApplicative to Applicative)
open import Category.Monad renaming (RawMonad to Monad; RawMonadPlus to MonadPlus)
open import Category.Monad.State renaming (RawMonadState to MonadState)
--open import Function.Identity.Categorical renaming (monad to monad-identity)
--open import Function.Identity.Instances


open Functor {{...}} --renaming (_<$>_ to fmap)
open Applicative {{...}} hiding (_<$>_) renaming (_⊛_ to _<*>_)
open Monad {{...}} hiding (_<$>_;_⊛_;pure)
open MonadPlus {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (∅ to mzero;_∣_ to _<|>_)
open MonadState {{...}} hiding (_<$>_;_⊛_;return;_>>=_;_>>_;pure;_=<<_;join) renaming (get to getS; put to putS; modify to modifyS)

private
  variable
    A B D S : Set
    K C M F V : Set -> Set

record MonadTrans (T : (Set -> Set) -> Set -> Set) : Set where
  field
    liftT : {{mon : Monad M}} -> M A -> T M A
    --overlap {{mon'}} : {{mon : Monad M}} -> Monad (T M)

open MonadTrans {{...}}

data Identity A : Set where
  IdentC : A -> Identity A

runIdentity : Identity A -> A
runIdentity (IdentC x) = x

instance
  monadApplicative : {{mon : Monad M}} -> Applicative M
  monadApplicative {{mon = mon}} = Monad.rawIApplicative mon

  applicativeFunctor : {{apl : Applicative F}} -> Functor F
  applicativeFunctor {{apl = apl}} = Applicative.rawFunctor apl

  stateTMonad : {{mon : Monad M}} -> Monad (StateT S M)
  stateTMonad {S = S} {{mon = mon}} = StateTMonad S mon

  stateTMonadState : {{mon : Monad M}} -> MonadState S (StateT S M)
  stateTMonadState {S = S} {{mon = mon}} = StateTMonadState S mon

  stateTMonadTrans : MonadTrans (StateT S)
  stateTMonadTrans = record { liftT = \ ma s -> (_, s) <$> ma }

  monadPlusMonad : {{mp : MonadPlus M}} -> Monad M
  monadPlusMonad {{mp = mp}} = MonadPlus.monad mp

  monadIdentity : Monad Identity
  monadIdentity =  record {
    return = IdentC ;
    _>>=_ = \ i fi -> fi (runIdentity i) }

{-
Basic VarMonad modelling Haskell pointers. Problem: Not useful for solvers due to complete rewriting of variables.
-}
record BaseVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : A -> M (V A)
    get : V A -> M A
    write : V A -> A -> M T
    overlap {{mon}} : Monad M

----------------------------------------------------------------
--MTC initial example
----------------------------------------------------------------

anyNorm : List Bool -> Bool
anyNorm = foldr (_||_) false

Algebra : (F : Set -> Set) -> (A : Set) -> Set
Algebra F A = F A -> A

Fix : (F : Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF {A = A} alg f = f A alg

data ListF (A : Set) (B : Set) : Set where
  nil : ListF A B
  lcons : A -> B -> ListF A B

{-}
mapListF : (B -> D) -> ListF A B -> ListF A D
mapListF f nil = nil
mapListF f (lcons x lst) = lcons x (f lst)

instance
  Functor-ListF : Functor (ListF A)
  Functor-ListF = record { _<$>_ = mapListF }

In : {{func : Functor F}} -> F (Fix F) -> Fix F
In f B alg = alg (foldF alg <$> f)

[-] : Fix (ListF A)
[-] = In nil

_:-:_ : A -> Fix (ListF A) -> Fix (ListF A)
_:-:_ x xs = In (lcons x xs)

anyF : Fix (ListF Bool) -> Bool
anyF = foldF \ {
  nil -> false;
  (lcons x xs) -> x || xs}
-}
---------------------------------------------------------------
--MTC with VarMonads
---------------------------------------------------------------

MAlgebra : (M : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
MAlgebra M F A = F A -> M A

FixM : (M : Set -> Set) -> (F : Set -> Set) -> Set
FixM M F = forall A -> MAlgebra M F A -> M A

foldM : MAlgebra M F A -> FixM M F -> M A
foldM {A = A} alg f = f A alg

record MFunctor (M : Set -> Set) (F : Set -> Set) : Set where
  field
    _<$M>_ : (A -> M B) -> F A -> M (F B)
    overlap {{mon}} : Monad M
open MFunctor {{...}} public

instance
  ListF-MFunctor : {{mon : Monad M}} -> MFunctor M (ListF A)
  ListF-MFunctor = record {  _<$M>_ = \ {
      f nil -> return nil;
      f (lcons x xs) -> f xs >>= return o lcons x} }

  BVM-MFunctor : {{bvm : BaseVarMonad M V}} -> {{mfunc : MFunctor M F}} -> MFunctor M (F o V)
  BVM-MFunctor {{bvm = bvm}} = record { _<$M>_ = \ f ls -> (\ v -> get v >>= f >>= new) <$M> ls }
    where open BaseVarMonad bvm



InM : {{mfunc : MFunctor M F}} -> F (FixM M F) -> FixM M F
InM fx B alg = (foldM alg <$M> fx) >>= alg

ExM : {{mfunc : MFunctor M F}} -> FixM M F -> M $ F (FixM M F)
ExM = foldM ((return o InM) <$M>_)
{-}
[]M : {{bvm : BaseVarMonad M V}} -> FixM M (ListF A o V)
[]M = InM nil

_::M_ : {{bvm : BaseVarMonad M V}} -> A -> V $ FixM M (ListF A o V) -> FixM M (ListF A o V)
_::M_ x xs = InM $ lcons x xs

foldBVM :
  {{bvm : BaseVarMonad M V}} ->
  {{mfunc : MFunctor M F}} ->
  Algebra F A -> FixM M (F o V) -> M A
foldBVM {{bvm = bvm}} alg = foldM \ f -> alg <$> (get <$M> f)
  where open BaseVarMonad bvm


anyM : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons x xs) -> (x ||_) <$> get xs }
  where open BaseVarMonad bvm

--this reads more values than it needs to

anyM' : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyM' = foldBVM \ {
  nil -> false;
  (lcons x xs) -> x || xs }

anyOptiM : {{bvm : BaseVarMonad M V}} -> FixM M ((ListF Bool) o V) -> M Bool
anyOptiM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons true xs) -> return true;
    (lcons false xs) -> get xs}
  where open BaseVarMonad bvm

  -}

---------------------------------------------------------------
-- Variable tracking
---------------------------------------------------------------


AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C (Sigma Set \ A -> (A -x- V A))

record TrackVarMonad (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    bvm : BaseVarMonad M V
    getCurrAssignments : M $ AsmCont C V
  open BaseVarMonad bvm public


BaseVarMonad=>TrackVarMonad : {{mpc : MonadPlus C}} ->
  BaseVarMonad M V ->
  TrackVarMonad C (StateT (AsmCont C V) M) V
BaseVarMonad=>TrackVarMonad {C = C} bbvm = record {
    bvm = record {
      new = liftT o new ;
      get = \ {A = A} p -> do
        v <- liftT (get p)
        modifyS (_<|> return (A , v , p))
        return v
        ;
      write = \ p -> liftT o write p } ;
    getCurrAssignments = getS }
  where
    open BaseVarMonad bbvm


record SpecVarMonad (M : Set -> Set) (V : Set -> Set) (B : Set) : Set where
  field
    get : V A -> M B
    write : V A -> B -> M T
    overlap {{mon}} : Monad M


RecTupPtr : (M : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> (A : Set) -> Set
RecTupPtr M V F A = V $ A -x- FixM M (\R -> F (\ B -> V (B -x- R) ) )

AsmPtr : (M : Set -> Set) (V : Set -> Set) (C : Set -> Set) (A : Set) -> Set
--RecTupPtr M V C A = V (A -x- FixM M (\ R -> AsmCont C (\ B -> V (B -x- R)) ) )
AsmPtr M V C = RecTupPtr M V (C o AsmCont C)


recProdVarMonad : BaseVarMonad M V -> {B : Set} -> {F : (Set -> Set) -> Set} ->
  {{mfunc : MFunctor M (\ R -> F (\B -> V (B -x- R)))}} ->
  (forall {V'} -> F V') ->
  BaseVarMonad M (RecTupPtr M V F) -x- SpecVarMonad M (RecTupPtr M V F) (F (RecTupPtr M V F))
recProdVarMonad bvm mpty = (record {
      new = new o (_, InM mpty) ;
      get = (fst <$>_) o get ;
      write = \ p v -> write p (v , InM mpty) }
    ) , (record {
      get = \ p -> snd <$> get p >>= ExM ;
      write = \ p v -> fst <$> get p >>= \ a -> write p (a , InM v) })
  where open BaseVarMonad bvm

record CLVarMonad (M : Set -> Set) (V : Set -> Set) (C : Set -> Set) : Set where
  field
    bvm : BaseVarMonad M V
    getReasons : V A -> M $ C $ AsmCont C V
  open BaseVarMonad bvm

liftSpecVarMonad : forall {I} -> {{mtrans : MonadTrans I}} -> {{mon : Monad (I M)}} -> SpecVarMonad M V B -> SpecVarMonad (I M) V B
liftSpecVarMonad svm = record {
    get = liftT o get ;
    write = \ p v -> liftT (write p v) }
  where open SpecVarMonad svm

BaseVarMonad=>CLVarMonad : BaseVarMonad M V ->
  (forall {A} -> C A) ->
  {{mfunc : MFunctor M (\ R -> C $ AsmCont C (\B -> V (B -x- R)))}} ->
  {{mplus : MonadPlus C}} ->
  CLVarMonad (StateT (AsmCont C (AsmPtr M V C)) M) (AsmPtr M V C) C
BaseVarMonad=>CLVarMonad {M} {V = V} {C = C} bvm mpty = record {
    bvm = record {
      new = \ x -> new x >>= putAssignments ;
      get = get ;
      write = \ p v -> putAssignments p >> write p v };
    getReasons = getR }
  where
    vmtup = recProdVarMonad bvm {B = C $ AsmCont C (AsmPtr M V C)} {F = C o AsmCont C} mpty
    trackM = BaseVarMonad=>TrackVarMonad (fst vmtup)
    lspec = liftSpecVarMonad (snd vmtup)
    open BaseVarMonad bvm using (mon)
    open TrackVarMonad trackM
    open SpecVarMonad lspec renaming (get to getR; write to writeR)
    putAssignments : AsmPtr M V C A -> StateT (AsmCont C (AsmPtr M V C)) M (AsmPtr M V C A)
    putAssignments p = getCurrAssignments >>= writeR p o return >> return p

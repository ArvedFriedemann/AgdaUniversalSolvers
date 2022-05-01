{-# OPTIONS --type-in-type #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsMTC.VarMonadsMTC where

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
    A B S : Set
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

{-
The Continuation style VarMonad makes the most sense with clause learning, because
with get, the value can really only be used in the concealed context, not in the contexts after. This could still be achieved with forks, however, the forks might depend on previously read values.
-}

{-
whole thing works with normal VarMonads too, if the monad is Alternative. Here, the continuation is harder to achieve.
-}
record ConstrDefVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> M (V A)
    get : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M
  --open Monad mon public

record ConstrVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    get : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M
  --open Monad mon public

AsmCont : (C : Set -> Set) -> (V : Set -> Set) -> Set
AsmCont C V = C $ Sigma Set (\A -> (A -x- V A))

record ConstrTrackVarMonad (K : Set -> Set) (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    cdvm : ConstrDefVarMonad K M V
    getCurrAssignments : M $ AsmCont C V
  open ConstrDefVarMonad cdvm public


ConstrDefVarMonad=>ConstrTrackVarMonad : {{mpc : MonadPlus C}} ->
  ConstrDefVarMonad K M V ->
  ConstrTrackVarMonad K C (StateT (AsmCont C V) M) V
ConstrDefVarMonad=>ConstrTrackVarMonad {C = C} cdvm = record {
    cdvm = record {
      new = liftT new ;
      get = \ {A = A} p -> do
        v <- liftT (get p)
        modifyS (_<|> return (A , v , p))
        return v
        ;
      write = \ p -> liftT o write p } ;
    getCurrAssignments = getS }
  where
    open ConstrDefVarMonad cdvm

----------------------------------------------------------------
--Algebrae
----------------------------------------------------------------

MAlgebra : (M : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
MAlgebra M F A = F A -> M A

FixM : (M : Set -> Set) -> (F : Set -> Set) -> Set
FixM M F = forall A -> MAlgebra M F A -> M A

foldM : MAlgebra M F A -> FixM M F -> M A
foldM {A = A} alg fa = fa A alg

FixMC : {{mon : Monad M}} -> (forall {A} {B} -> (A -> M B) -> F A -> M (F B) ) -> F (FixM M F) -> FixM M F
FixMC fmapM f B alg = fmapM (foldM alg) f >>= alg

open import Data.Maybe using () renaming (map to mapMab)

record SpecVarMonad (M : Set -> Set) (V : Set -> Set) (B : Set) : Set where
  field
    get : V A -> M B
    write : V A -> B -> M T
    overlap {{mon}} : Monad M

test : {{bvm : BaseVarMonad M V}} -> (A : Set) -> M $ V (FixM M (\ R -> Maybe $ A -x- V R))
test {{bvm = bvm}} A = new \ B alg -> alg nothing
  where open BaseVarMonad bvm

sequence : {{mon : Monad M}} -> List (M A) -> M (List A)
sequence = foldr (\ ma mlst -> (| ma :: mlst |)) (return [])

RecTupLstPtr : (M : Set -> Set) (V : Set -> Set) (A : Set) -> Set
RecTupLstPtr M V A = V (A -x- FixM M (\ R -> List (Sigma Set \ T -> V (T -x- R)) ) )

testConstr : BaseVarMonad M V -> BaseVarMonad M (RecTupLstPtr M V) -x- SpecVarMonad M (RecTupLstPtr M V) (FixM M \ R -> List (Sigma Set \ T -> V (T -x- R)) )
testConstr {M} {V = V} bvm = ( record {
      new = \ x -> new (x , FixMC {!!} []);
      get = \ p -> fst <$> get p ; --foldM (return o fst);
      write = \ p v -> write p (v , FixMC {!!} []) }
    ) , ( record {
      get = \ p -> snd <$> get p ; -- \p -> get p >>= foldM \ (_ , lst) -> concat <$> sequence (map get lst);
      -- TODO: This does not work because the pointer type A depends. List needs to store values independent of A!
      write = \ p v -> write p ({!   !} , v) } )-- \ p v -> get p >>= foldM (return o fst) >>= \ a -> write p (FixMC {!   !} (a , [])) } ) --\ p v -> get p >>= \ pv -> write p \ B alg -> foldM return pv >>= \ {(a , lst) -> alg (a , p :: lst) } } )
  where open BaseVarMonad bvm


{-
BaseVarMonad M (\ A -> V (A -x- FixM M $ \ R -> List (Sigma Set \ T -> V (T -x- R) ) )
                ) )
-}

{-}
RecPtr : (M : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set -> Set -> Set) -> (A : Set) -> Set
RecPtr M V F A = V $ FixM M (\ R -> F V)
-}

{-}

RecPtr : (M : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> (Set -> Set)) -> (A : Set) -> Set
RecPtr M V F = FixFM M (\ V' A -> V (F V' A) )

RecTupPtr : (M : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> Set -> Set
RecTupPtr M V F = RecPtr M V (\ V' A -> A -x- F V')

RTC : {F : (Set -> Set) -> Set} -> V (A -x- F (RecTupPtr M V F)) -> RecTupPtr M V F A
RTC v = {!!}

ReasPtr : (M : Set -> Set) -> (V : Set -> Set) -> (C : Set -> Set) -> Set -> Set
ReasPtr M V C = RecTupPtr M V (\ V' -> C $ AsmCont C V')

record ConstrSpecVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) (B : Set) : Set where
  field
    get : {{k : K A}} -> V A -> M B
    write : {{k : K A}} -> V A -> B -> M T
    overlap {{mon}} : Monad M

recProductVarMonad : {V : Set -> Set} -> {F : (Set -> Set) -> Set} ->
  (emptyF : {V' : Set -> Set} -> (F V')) ->
  (emptyA : {A : Set} -> {{k : K A}} -> A) ->
  (tupK : {A : Set} -> {{k : K A}} -> K (A -x- (F (RecTupPtr M V F)) ) ) ->
  ConstrVarMonad K M V ->
  ConstrDefVarMonad K M (RecTupPtr M V F) -x- ConstrSpecVarMonad K M (RecTupPtr M V F) (F (RecTupPtr M V F))
recProductVarMonad {K} {V = V} {F = F} emptyF emptyA tupK cdvm = (
  record {
    new = {!!} <$> new {{k = tupK}} (emptyA , emptyF) ;
    get = {!!}; --((fst <$>_) o get {{k = tupK}}) o FixF.InF ;
    write = {!!} } --(\ p v -> write {{k = tupK}} p (v , emptyF)) o FixF.InF } --this only makes sense with lattices
  ) , (
  record {
    get = {!!}; --((snd <$>_) o get {{k = tupK}}) o FixF.InF ;
    write = {!!} } --(\ p v -> write {{k = tupK}} p (emptyA , v)) o FixF.InF }
  )
  where
    open ConstrVarMonad cdvm


record ConstrCLVarMonad (K : Set -> Set) (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    cdvm : ConstrDefVarMonad K M V
    getReasons : {{k : K A}} -> V A -> M (C $ AsmCont C V)


ConstrVarMonad=>ConstrCLVarMonad :
  {{mpc : MonadPlus C}} ->
  (emptyC : {V' : Set -> Set} -> (C $ AsmCont C V')) ->
  (emptyA : {A : Set} -> {{k : K A}} -> A) ->
  (tupK : {A : Set} -> {{k : K A}} -> {B : Set} -> K (A -x- B) ) ->
  ConstrVarMonad K M V ->
  ConstrCLVarMonad K C (StateT (AsmCont C (ReasPtr M V C)) M) (ReasPtr M V C)
ConstrVarMonad=>ConstrCLVarMonad {C} {K} {M = M} {V} emptyC emptyA tupK cvm =
  record {
    cdvm = record {
      new = do
        p <- new
        r <- getCurrAssignments
        writeRes p (return r)
        return p
        ;
      get = get ;
      write = \ p v -> do
        r <- getCurrAssignments
        write p v
        writeRes p (return r)
    } ;
    getReasons = getRes }
  where
    prod = recProductVarMonad emptyC emptyA tupK cvm
    cdvm = fst prod
    specvm : ConstrSpecVarMonad K M (ReasPtr M V C) (C $ AsmCont C (ReasPtr M V C))
    specvm = snd prod
    tdvm = ConstrDefVarMonad=>ConstrTrackVarMonad cdvm
    liftspecvm : ConstrSpecVarMonad K (StateT (AsmCont C (ReasPtr M V C)) M) (ReasPtr M V C) (C $ AsmCont C (ReasPtr M V C))
    liftspecvm = let open ConstrSpecVarMonad specvm in record {
      get = liftT o get ;
      write = \ p v -> liftT $ write p v }
    open ConstrTrackVarMonad tdvm
    open ConstrSpecVarMonad liftspecvm renaming (get to getRes; write to writeRes)

-}

{-
This VarMonad is needed later when the whole construction is actually done in parallel
-}
record RunnableVarMonad (M : Set -> Set) (V : Set -> Set) : Set where
  field
    run : M A -> A or (exists B st V B -x- (B -> M A))

----------------------------------------------------------------------
-- Default memory
----------------------------------------------------------------------

open import Data.Nat.Properties renaming (<-strictTotalOrder to NatSTO)
open import Data.Tree.AVL.Map NatSTO renaming (empty to empty-map)


record NatPtr (A : Set) : Set where
  constructor ptr
  field
    idx : Nat

open NatPtr

defaultState : Set
defaultState = Nat -x- Map (Sigma Set id)

defaultInit : defaultState
defaultInit = (0 , empty-map)

open import Agda.Builtin.TrustMe
postulate dummy : {A : Set} -> A

safeLookup : NatPtr A -> Map (Sigma Set id) -> A
safeLookup {A} (ptr p) mp with lookup p mp
safeLookup {A} (ptr p) mp | just (B , b) with primTrustMe {x = A} {y = B}
safeLookup {A} (ptr p) mp | just (B , b) | refl = b
safeLookup {A} (ptr p) mp | nothing = dummy


----------------------------------------------------------------------
-- Default BaseVarMonad
----------------------------------------------------------------------
{-
defaultVarMonad : BaseVarMonad (StateT defaultState Identity) NatPtr
defaultVarMonad = record {
    new = \ {A} x -> {!!}; --\ (n , mp) -> (ptr n) , (suc n , insert n (A , x) mp) ;
    get = \ { {A} p -> {!!} }; --\ (n , mp) -> safeLookup p mp , (n , mp) } ;
    write = \ {A} p f -> {!!} \ (n , mp) -> let
      oldCont = safeLookup p mp
      (v , res) = f oldCont
      in res , (n , insert (idx p) (A , v) mp)
  }
-}

--------------------------------------------------------------------
--Initial example
--------------------------------------------------------------------

Algebra : (F : Set -> Set) -> (A : Set) -> Set
Algebra F A = F A -> A

Fix : (F : Set -> Set) -> Set
Fix F = forall A -> Algebra F A -> A

foldF : Algebra F A -> Fix F -> A
foldF {A = A} alg fa = fa A alg

data _:+:_ (F : Set -> Set) (G : Set -> Set) : Set -> Set where
  Inl : F A -> (F :+: G) A
  Inr : G A -> (F :+: G) A

data ListF (A : Set) : (B : Set) -> Set where
  nil : ListF A B
  lcons : A -> B -> ListF A B

[-] : Fix (ListF A)
[-] A alg = alg nil

infixr 1 _:-:_
_:-:_ : A -> Fix (ListF A) -> Fix (ListF A)
_:-:_ a fa B alg = alg (lcons a (foldF alg fa))

anyFL : Fix (ListF Bool) -> Bool
anyFL = foldF \ {
  nil -> false;
  (lcons x xs) -> x || xs}

listTest : Bool
listTest = anyFL $ false :-: true :-: false :-: [-]

{-
Problem of the paper: we don't know why the function returned true.
Part of clause learning: Should return that anyFL (false :-: true :-: x) = true
Sure, getting anyFL (x :-: true :-: y) would be better, but would not be an accurate statement that comes from evaluating the function (could be deduced, but in this very example it was important that the first value is false.)

Can be thought bigger when looking at a function sudoku : Field -> Bool. If there is an error where the field is not set corretly, why was that the case?
-}

{-
VarMonad Solution:
-}

anyNaive : {{bvm : BaseVarMonad M V}} -> Fix (ListF Bool o V) -> M Bool
anyNaive {{bvm = bvm}} = foldF \ {
    nil -> return false;
    (lcons x xs) -> (x ||_) <$> (join $ get xs)}
  where open BaseVarMonad bvm

anyFLM : {{bvm : BaseVarMonad M V}} -> FixM M (ListF Bool o V) -> M Bool
anyFLM {{bvm = bvm}} = foldM \ {
    nil -> return false;
    (lcons x xs) -> (x ||_) <$> get xs } --(| (return x) || (get xs) |) } --technically correct, but takes ages to compile
  where open BaseVarMonad bvm

_=<<vm_ : {{bvm : BaseVarMonad M V}} -> (A -> M B) -> M (V A) -> M B
_=<<vm_ {{bvm = bvm}} m p = p >>= get >>= m
  where open BaseVarMonad bvm


[-]p : FixM M (ListF A o V)
[-]p A alg = alg nil

infixr 1 _:-:p_
_:-:p_ : {{bvm : BaseVarMonad M V}} -> A -> V ( FixM M (ListF A o V) ) -> M $ FixM M (ListF A o V)
_:-:p_ {{bvm = bvm}} a p = return \ B alg -> do
    xs <- get p
    recres <- foldM alg xs >>= new
    alg (lcons a recres)
  where open BaseVarMonad bvm

[]vm : {{bvm : BaseVarMonad M V}} -> M $ V $ FixM M (ListF A o V)
[]vm {{bvm = bvm}} = new [-]p
  where open BaseVarMonad bvm

infixr 1 _::vm_
_::vm_ : {{bvm : BaseVarMonad M V}} -> A -> (M $ V ( FixM M (ListF A o V) )) -> M $ V ( FixM M (ListF A o V) )
_::vm_ {{ bvm = bvm }} a mxs = do
    xs <- mxs
    (a :-:p xs) >>= new
  where open BaseVarMonad bvm

{-
_::vm'_ : {{bvm : BaseVarMonad M V}} -> A -> V $ Fix (ListF A o V) -> M $ V $ Fix (ListF A o V)
_::vm'_ {{bvm = bvm}} a p = do
    new \ B alg -> alg (lcons a {!!}) --this doesn't work at this point. In order to properly fold over the value, one needs to create a pointer with the result. This can only be done in a monadic context.
  where open BaseVarMonad bvm
-}

varMonadSolution : {{bvm : BaseVarMonad M V}} -> M Bool
varMonadSolution {{bvm = bvm}} = anyFLM =<<vm (false ::vm true ::vm false ::vm []vm)
  where open BaseVarMonad bvm

{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.ConstrainedExamples where

open import AgdaAsciiPrelude.AsciiPrelude
open import VarMonadsLOPSTR2022.VarMonadsConstrained

private
  variable
    A B D S : Set
    K C M F V : Set -> Set

{-
{-# NO_POSITIVITY_CHECK #-}
data FixR (F : Set -> Set) : Set where
  In : F (FixR F) -> FixR F

{-# TERMINATING #-}
anyR : {{cvm : ConstrVarMonad K M V}} -> {{K (FixR $ ListF Bool o V)}} -> FixR (ListF Bool o V) -> M Bool
anyR {{cvm = cvm}} (In nil) = return false
anyR {{cvm = cvm}} (In (lcons true xs)) = return true
anyR {{cvm = cvm}} (In (lcons false xs)) = get xs >>= anyR
  where open ConstrVarMonad cvm
-}

KMTCAlgebra : (K : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
KMTCAlgebra K F A = forall R -> {{k : K R}} -> (R -> A) -> F R -> A

KMTCFix : (K : Set -> Set) -> (F : Set -> Set) -> Set
KMTCFix K F = forall A -> K A -> KMTCAlgebra K F A -> A

KMTCFold : {{k : K A}} -> KMTCAlgebra K F A -> KMTCFix K F -> A
KMTCFold {A = A} {{k = k}} alg fa = fa A k alg

KMTCIn : {{kf : K (KMTCFix K F)}} -> F (KMTCFix K F) -> KMTCFix K F
KMTCIn f R k alg = alg _ (KMTCFold {{k = k}} alg) f

KMTCEx : {{func : Functor F}} ->
  {{kf : K (KMTCFix K F)}} ->
  {{kff : K (F (KMTCFix K F))}} ->
  KMTCFix K F -> F (KMTCFix K F)
KMTCEx {{func}} = KMTCFold \ R [[_]] f -> KMTCIn o [[_]] <$>' f
  where open Functor func renaming (_<$>_ to _<$>'_)

KFixT : (K : Set -> Set) -> (F : Set -> Set) -> Set
KFixT K F = F (KMTCFix K F) -x- KMTCFix K F

KFoldT : {{k : K A}} -> KMTCAlgebra K F A -> KFixT K F -> A
KFoldT {A = A} {{k = k}} alg (_ , fa) = fa A k alg

--KInT : {{kf : K (KMTCFix K F)}} -> F (KFixT K F) -> KFixT K F
--KInT f = f , \ _ k alg -> alg _ (KMTCFold {{k = k}} alg) f

anyMTCBVM : {{cvm : ConstrVarMonad K M V}} ->
  {{kmb : K (M Bool)}} ->
  KMTCFix K (ListF Bool o V) -> M Bool
anyMTCBVM {{cvm}} = KMTCFold \{
    R [[_]] nil -> return false ;
    R [[_]] (lcons true _) -> return true ;
    R [[_]] (lcons false xs) -> get xs >>= [[_]] }
  where open ConstrVarMonad cvm


record ListFVConstraints (K : Set -> Set) (V : Set -> Set) (A : Set) : Set where
  field
    {{kptr}} : forall {A} -> K (V A)
    {{klistf}} : forall {A} {B} -> {{ka : K A}} -> {{kb : K B}} -> K (ListF A B)
    {{ka}} : K A


LVMFunc :
  {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V A}} ->
  CMFunctor K M (ListF A o V)
LVMFunc {{cvm}} = BVM-CMFunctor {{cvm}} {{ListF-CMFunctor}}


[]M : {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V A}} ->
  {{klst : K (CFixM K M (ListF A o V))}} ->
  CFixM K M (ListF A o V)
[]M = CInM {{LVMFunc}} nil


_::M_ : {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V A}} ->
  {{klst : K (CFixM K M (ListF A o V))}} ->
  A -> V $ CFixM K M (ListF A o V) -> CFixM K M (ListF A o V)
_::M_ x xs = CInM {{LVMFunc}} $ lcons x xs


[]VM : {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V A}} ->
  {{klst : K (CFixM K M (ListF A o V))}} ->
  M $ CFixM K M (ListF A o V)
[]VM = return []M

infixr 5 _::VM_

_::VM_ : {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V A}} ->
  {{klst : K (CFixM K M (ListF A o V))}} ->
  A -> M $ CFixM K M (ListF A o V) -> M $ CFixM K M (ListF A o V)
_::VM_ {{cvm = cvm}} x m = (x ::M_) <$> (m >>= new)
  where open ConstrVarMonad cvm

foldBVM :
  {{cvm : ConstrVarMonad K M V}} ->
  {{mfunc : CMFunctor K M F}} ->
  {{kv : forall {A} -> K (V A)}} ->
  {{ka : K A}} ->
  Algebra F A -> CFixM K M (F o V) -> M A
foldBVM {{cvm}} {{mfunc}} alg = CfoldM \ f -> alg <$> (get <$CM>' f)
  where
    open ConstrVarMonad cvm
    open CMFunctor mfunc renaming (_<$CM>_ to _<$CM>'_)

toList : {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V Bool}} ->
  {{kb : K (List Bool)}} ->
  CFixM K M (ListF Bool o V) -> M (List Bool)
toList = foldBVM {{mfunc = ListF-CMFunctor}} \{
  nil -> [];
  (lcons x xs) -> x :: xs }


toListMTC : {{cvm : ConstrVarMonad K M V}} ->
  {{kmla : K (M (List A))}} ->
  KMTCFix K (ListF A o V) -> M (List A)
toListMTC {{cvm}} = KMTCFold \ {
    R [[_]] nil -> return [] ;
    R [[_]] (lcons x xs) -> (x ::_) <$> (get xs >>= [[_]])}
  where open ConstrVarMonad cvm


anyOptiM : {{cvm : ConstrVarMonad K M V}} ->
  {{kb : K Bool}} ->
  CFixM K M ((ListF Bool) o V) -> M Bool
anyOptiM {{cvm = cvm}} = CfoldM \ {
    nil -> return false;
    (lcons true xs) -> return true;
    (lcons false xs) -> get xs}
  where open ConstrVarMonad cvm

{-# TERMINATING #-}
anyOptiM' : {{cvm : ConstrVarMonad K M V}} ->
  {{lfvc : ListFVConstraints K V Bool}} ->
  {{klst : K (CFixM K M (ListF Bool o V))}} ->
  --{{kb : K Bool}} ->
  CFixM K M ((ListF Bool) o V) -> M Bool
anyOptiM' {{cvm = cvm}} lst = CExM {{LVMFunc {A = Bool} }} lst >>= \{
  nil -> return false;
  (lcons true xs) -> return true;
  (lcons false xs) -> get xs >>= anyOptiM'
  }
  where open ConstrVarMonad cvm



instance
  cvmi = ConstrCLVarMonad.cvm defaultConstrCLVarMonad

  listFVConstraints :
    {{kptr : forall {A} -> K (V A) }} ->
    {{klistf : forall {A} {B} -> {{ka : K A}} -> {{kb : K B}} -> K (ListF A B)}} ->
    {{ka : K A}} ->
    ListFVConstraints K V A
  listFVConstraints = record {}

open ConstrCLVarMonad defaultConstrCLVarMonad

functorListF : Functor (ListF A)
functorListF = record { _<$>_ = \{ f nil -> nil; f (lcons x xs) -> lcons x (f xs)}}

instance
  showNat : Show Nat
  showNat = ShowC showN

  showBool : Show Bool
  showBool = ShowC \{true -> "true" ; false -> "false"}

  showListF : {{Show A}} -> {{Show B}} -> Show (ListF A B)
  showListF = ShowC \{nil -> "nil"; (lcons x xs) -> "lcons " ++s show x ++s " " ++s show xs}

  showList : {{s : Show A}} -> Show (List A)
  showList = ShowC ((\ x -> "[" ++s x ++s "]") o concats o intersperse " , " o map show)

  --showFixR : {{Show (F (FixR F))}} -> Show (FixR F)
  --showFixR = ShowC \{(In x) -> show x}

  funcListF = functorListF

{-}
  showMTCFix : {F : Set -> Set} ->
    {{func : Functor F}} ->
    {{sf : Show (F (KMTCFix K F)) }} ->
    {{kf : K (KMTCFix K F)}} ->
    {{kff : K (F (KMTCFix K F))}} ->
    Show (KMTCFix K F)
  showMTCFix = ShowC $ show o KMTCEx
-}
  --showMTCFix : Show (KMTCFix K F)
  --showMTCFix = ShowC $ const "#KMTCFix"

  showString : Show String
  showString = ShowC id

  showMTCFixListF :
    {{sh : Show A}} ->
    {{svr : forall {R} -> Show (V R)}} ->
    {{ks : K String}} ->
    Show (KMTCFix K (ListF A o V))
  showMTCFixListF = ShowC (KMTCFold \{
    R [[_]] nil -> "nil";
    R [[_]] (lcons x xs) -> "lcons " ++s show x ++s " " ++s show xs })

  --showMBool : Show (defaultCLVarMonadStateM Bool)
  --showMBool = ShowC $ const "#MBool"

test1 : String
test1 = runDefConstrTrackVarMonad $ do
  p <- new 5
  p' <- new 6
  get p
  get p'
  --show <$> getCurrAssignments
  pw <- new 0
  write pw 8
  --show {{showDefReasons}} <$> getReasons pw
  get p --here, get pw makes the whole thing not terminate...muste be because of universe polymorphism
  write pw 9
  show {{showDefReasons}} <$> getReasons pw

anyTest : Bool
anyTest = runDefConstrTrackVarMonad $ do
  false ::VM true ::VM false ::VM []VM >>= anyOptiM

anyTest2 = runDefConstrTrackVarMonad $ do
  false ::VM true ::VM false ::VM []VM >>= anyOptiM >>= new >>= (show {{showDefReasons}} <$>_) o getReasons

anyTest22 = runDefConstrTrackVarMonad $ do
  res <- false ::VM true ::VM false ::VM []VM >>= anyOptiM >>= new >>= getReasons
  return $ (map o map) (\ (T , v , p , k) -> idx p) res


open import Agda.Builtin.TrustMe

trustVal : (a : A) -> B
trustVal {A} {B} a with primTrustMe {x = A} {y = B}
...| refl = a

anyTest3 = runDefConstrTrackVarMonad $ do
  --res <- false ::VM true ::VM false ::VM []VM >>= anyOptiM >>= new >>= getReasons
  res <- true ::VM []VM >>= new >>= get >>= anyOptiM' >>= new >>= getReasons
  sequenceM $ map ((sequenceM o map \ (T , v , p , k) -> (idx p ,_) <$> toList (trustVal v) ) o take 3) res

anyTest4 = runDefConstrTrackVarMonad $ do
  res <- false ::VM true ::VM false ::VM false ::VM []VM >>= new >>= get >>= anyOptiM >>= new >>= getReasons
  --false ::VM []VM >>= CExM {{LVMFunc}}
  sequenceM $ map ((sequenceM o map \ (T , v , p , k) -> (idx p ,_) <$> CExM {{LVMFunc {A = Bool} }} (trustVal v) ) o take 3) res

{-
--anyRTest : Bool
anyRTest = runDefConstrTrackVarMonad $ do
  lst0 <- new (In nil)
  lst1 <- new (In $ lcons false lst0)
  lst2 <- new (In $ lcons true lst1)
  lst3 <- new (In $ lcons false lst2)
  res <- get lst3 >>= anyR >>= new
  (show {{showDefReasons}}) <$> (getReasons res)
-}


[]MMTC : {{cvm : ConstrVarMonad K M V}} ->
  {{klst : K (KMTCFix K (ListF A o V))}} ->
  KMTCFix K (ListF A o V)
[]MMTC = KMTCIn nil


_::MMTC_ : {{cvm : ConstrVarMonad K M V}} ->
  {{klst : K (KMTCFix K (ListF A o V))}} ->
  A -> V $ KMTCFix K (ListF A o V) -> KMTCFix K (ListF A o V)
_::MMTC_ x xs = KMTCIn (lcons x xs)


--anyMTCTest : Bool
anyMTCTest = runDefConstrTrackVarMonad $ do
    --t <- new ([]MMTC {{cvm = ConstrCLVarMonad.cvm defaultConstrCLVarMonad}})
    lst0 <- new {- A = KMTCFix defaultConstraint (ListF Bool o defaultCLVarMonadV) -} ([]MMTC {A = Bool})
    lst1 <- new (false ::MMTC lst0)
    lst2 <- new (true ::MMTC lst1)
    lst3 <- new (false ::MMTC lst2)
    res <- get lst3 >>= new
    (show {{showDefReason}}) <$> getCurrAssignments

    {-
    TODO: Problem is, that during the CExM in the CL monad, new pointers are created.
    That should be avoided, as it changes the pointer in the assignment 
    -}

    --res <- get lst3 >>= anyMTCBVM {{kmb = record {showi = showMA } }} >>= new -- >>= toListMTC
    --(show (lst0 :: lst1 :: lst2 :: lst3 :: res :: []) ++s_) <$>
      --((show {{showDefReasons}}) <$> (getReasons res))
  where
    instance
      showStateT : Show (StateT S M A)
      showStateT = ShowC $ const "#StateTMon"

      showMA : Show (defaultConstrCLVarMonadStateM A)
      showMA = ShowC $ const "#M(A)"
{-}
      showListFPtr : {sh : Show A} -> {sv : forall {B} -> Show (V B)} -> {C : Set} ->
        Show (ListF A (V C))
      showListFPtr = {!!}
-}

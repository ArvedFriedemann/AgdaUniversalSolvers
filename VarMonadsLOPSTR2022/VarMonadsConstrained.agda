{-# OPTIONS --type-in-type #-}
--{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --rewriting #-}

module VarMonadsLOPSTR2022.VarMonadsConstrained where

open import AgdaAsciiPrelude.AsciiPrelude
open import VarMonadsLOPSTR2022.VarMonadsLOPSTR2022

private
  variable
    A B D S : Set
    K C M F V : Set -> Set

----------------------------------------------------------------------
--Constrained Algebrae
----------------------------------------------------------------------

CMAlgebra : (K : Set -> Set) -> (M : Set -> Set) -> (F : Set -> Set) -> (A : Set) -> Set
CMAlgebra K M F A = {{K A}} -> F A -> M A

CFixM : (K : Set -> Set) -> (M : Set -> Set) -> (F : Set -> Set) -> Set
CFixM K M F = forall A -> K A -> MAlgebra M F A -> M A

CfoldM : {{k : K A}} -> MAlgebra M F A -> CFixM K M F -> M A
CfoldM {A = A} {{k}} alg f = f A k alg

record CMFunctor (K : Set -> Set) (M : Set -> Set) (F : Set -> Set) : Set where
  field
    _<$CM>_ : {{ka : K A}} -> {{kb : K B}} -> (A -> M B) -> F A -> M (F B)
    overlap {{mon}} : Monad M
open CMFunctor {{...}} public

instance
  ListF-CMFunctor : {{mon : Monad M}} -> {{forall {B} -> {{K B}} -> K (ListF A B)}} -> CMFunctor K M (ListF A)
  ListF-CMFunctor = record {  _<$CM>_ = \ {
      f nil -> return nil;
      f (lcons x xs) -> f xs >>= return o lcons x} }

  BVM-CMFunctor : {{bvm : BaseVarMonad M V}} -> {{mfunc : MFunctor M F}} -> CMFunctor K M (F o V)
  BVM-CMFunctor {{bvm = bvm}} {{mfunc = mfunc}} = record { _<$CM>_ = \ f ls -> (\ v -> get v >>= f >>= new) <$M>' ls }
    where
      open BaseVarMonad bvm
      open MFunctor mfunc using () renaming (_<$M>_ to _<$M>'_)



CInM : {{mfunc : CMFunctor K M F}} -> {{kf : K (CFixM K M F)}} -> F (CFixM K M F) -> CFixM K M F
CInM {{mfunc = mfunc}} fx B k alg = (CfoldM' alg <$CM>'' fx) >>= alg
  where
    open CMFunctor mfunc using () renaming (_<$CM>_ to _<$CM>'_)
    CfoldM' = CfoldM {{k = k}}
    _<$CM>''_ = _<$CM>'_ {{kb = k}}

CExM :
  {{mfunc : CMFunctor K M F}} ->
  {{kfcf : K (F (CFixM K M F))}} ->
  {{kcf : K (CFixM K M F)}} ->
  CFixM K M F -> M $ F (CFixM K M F)
CExM {{mfunc = mfunc}} = CfoldM ((return o CInM {{mfunc = mfunc}}) <$CM>'_)
  where open CMFunctor mfunc using () renaming (_<$CM>_ to _<$CM>'_)


----------------------------------------------------------------------
--Constrained Constructions
----------------------------------------------------------------------

record ConstrVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    new : {{k : K A}} -> A -> M (V A)
    get : {{k : K A}} -> V A -> M A
    write : {{k : K A}} -> V A -> A -> M T
    overlap {{mon}} : Monad M

ConstrAsmCont : (K : Set -> Set) -> (C : Set -> Set) -> (V : Set -> Set) -> Set
ConstrAsmCont K C V = C (Sigma Set \ A -> (A -x- V A -x- K A))

record ConstrTrackVarMonad (K : Set -> Set) (C : Set -> Set) (M : Set -> Set) (V : Set -> Set) : Set where
  field
    cvm : ConstrVarMonad K M V
    getCurrAssignments : M $ ConstrAsmCont K C V
  open ConstrVarMonad cvm public

ConstrVarMonad=>ConstrTrackVarMonad : {{mpc : MonadPlus C}} ->
  ConstrVarMonad K M V ->
  ConstrTrackVarMonad K C (StateT (ConstrAsmCont K C V) M) V
ConstrVarMonad=>ConstrTrackVarMonad {C = C} {{mpc = mpc}} ccvm = record {
    cvm = record {
      new = liftT o new ;
      get = \ {A = A} {{k = k}} p -> do
        v <- liftT (get p)
        modifyS (_<|> singleton (A , v , p , k))
        return v
        ;
      write = \ p -> liftT o write p } ;
    getCurrAssignments = getS }
  where
    open ConstrVarMonad ccvm
    open MonadPlus mpc using () renaming (return to singleton)

ConstrRecTupPtr : (K : Set -> Set) -> (M : Set -> Set) -> (V : Set -> Set) -> (F : (Set -> Set) -> Set) -> (A : Set) -> Set
ConstrRecTupPtr K M V F A = V $ A -x- CFixM K M (\R -> F (\ B -> V (B -x- R) ) )

ConstrAsmPtr : (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) (C : Set -> Set) (A : Set) -> Set
ConstrAsmPtr K M V C = ConstrRecTupPtr K M V (C o ConstrAsmCont K C)

record ConstrSpecVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) (B : Set) : Set where
  field
    get : {{k : K A}} -> V A -> M B
    write : {{k : K A}} -> V A -> B -> M T
    overlap {{mon}} : Monad M

constrRecProdVarMonad : ConstrVarMonad K M V -> {B : Set} -> {F : (Set -> Set) -> Set} ->
  {{mfunc : CMFunctor K M (\ R -> F (\B -> V (B -x- R)))}} ->
  {{fixK : K (CFixM K M (\R -> F (\ B -> V (B -x- R) ) ) )}} ->
  {{ffixK : K (F (\ B -> V (B -x- CFixM K M (\R -> F (\ B -> V (B -x- R) ) ) ) ) )}} ->
  {{ktup : forall {A} {B} -> {{K A}} -> {{K B}} -> K (A -x- B)}} ->
  (forall {V'} -> F V') ->
  ConstrVarMonad K M (ConstrRecTupPtr K M V F) -x- ConstrSpecVarMonad K M (ConstrRecTupPtr K M V F) (F (ConstrRecTupPtr K M V F))
constrRecProdVarMonad cvm {{mfunc = mfunc}} mpty = (record {
      new = new o (_, CInM {{mfunc = mfunc}} mpty) ;
      get = (fst <$>_) o get ;
      write = \ p v -> snd <$> get p >>= \ b -> write p (v , b {-InM mpty-}) }
    ) , (record {
      get = \ p -> snd <$> get p >>= CExM {{mfunc = mfunc}} ;
      write = \ p v -> fst <$> get p >>= \ a -> write p (a , CInM {{mfunc = mfunc}} v) })
  where open ConstrVarMonad cvm

record ConstrCLVarMonad (K : Set -> Set) (M : Set -> Set) (V : Set -> Set) (C : Set -> Set) : Set where
  field
    cvm : ConstrVarMonad K M V
    getReasons : {{K A}} -> V A -> M $ C $ ConstrAsmCont K C V
    getCurrAssignments : M $ ConstrAsmCont K C V
  open ConstrVarMonad cvm public

liftConstrSpecVarMonad : forall {K} {I} -> {{mtrans : MonadTrans I}} -> {{mon : Monad (I M)}} -> ConstrSpecVarMonad K M V B -> ConstrSpecVarMonad K (I M) V B
liftConstrSpecVarMonad svm = record {
    get = liftT o get ;
    write = \ p v -> liftT (write p v) }
  where open ConstrSpecVarMonad svm

ConstrVarMonad=>ConstrCLVarMonad : ConstrVarMonad K M V ->
  (forall {A} -> C A) ->
  {{mfunc : CMFunctor K M (\ R -> C $ ConstrAsmCont K C (\B -> V (B -x- R)))}} ->
  {{fixK : K (CFixM K M (\R -> C $ ConstrAsmCont K C (\ B -> V (B -x- R) ) ) )}} ->
  {{ffixK : K (C $ ConstrAsmCont K C (\ B -> V (B -x- (CFixM K M (\R -> C $ ConstrAsmCont K C (\ B -> V (B -x- R) ) )) ) ) )}} ->
  {{ktup : forall {A} {B} -> {{K A}} -> {{K B}} -> K (A -x- B)}} ->
  {{mplus : MonadPlus C}} ->
  ConstrCLVarMonad K (StateT (ConstrAsmCont K C (ConstrAsmPtr K M V C)) M) (ConstrAsmPtr K M V C) C
ConstrVarMonad=>ConstrCLVarMonad {K} {M} {V = V} {C = C} cvm mpty {{mfunc}} {{fixK}} {{ffixK}} {{ktup}} {{mplus}} = record {
    cvm = record {
      new = \ x -> new x >>= putAssignments ;
      get = get;
      write = \ p v -> putAssignments p >> write p v };
    getReasons = getR ;
    getCurrAssignments = getCurrAssignments }
  where
    vmtup = constrRecProdVarMonad cvm {B = C $ AsmCont C (AsmPtr M V C)} {F = C o ConstrAsmCont K C} {{mfunc = mfunc}} mpty
    trackM = ConstrVarMonad=>ConstrTrackVarMonad (fst vmtup)
    lspec = liftConstrSpecVarMonad (snd vmtup)
    open ConstrVarMonad cvm using (mon)
    open ConstrTrackVarMonad trackM
    open ConstrSpecVarMonad lspec renaming (get to getR; write to writeR)
    putAssignments : {{K A}} -> ConstrAsmPtr K M V C A -> StateT (ConstrAsmCont K C (ConstrAsmPtr K M V C)) M (ConstrAsmPtr K M V C A)
    putAssignments p = getCurrAssignments >>= writeR p o singleton >> return p
      where open MonadPlus mplus using () renaming (return to singleton)


-------------------------------------------------------------------
--default implementations
-------------------------------------------------------------------

defaultConstraint : (A : Set) -> Set
defaultConstraint A = T

instance
  alwaysI : defaultConstraint A
  alwaysI = tt
  --tupI : {{defaultConstraint A}} -> {{defaultConstraint B}} -> defaultConstraint (A -x- B)
  --tupI = tt


defaultConstrVarMonad : ConstrVarMonad defaultConstraint defaultVarMonadStateM NatPtr
defaultConstrVarMonad = {!!}
  where open BaseVarMonad (defaultVarMonad)

instance
  dcvm = defaultConstrVarMonad

instance
  private
    cmFuncListAsm :
      {{cvm : ConstrVarMonad K M V}} ->
      {{k : K (FixM M (\ R -> List $ ConstrAsmCont K List (\B -> V (B -x- R)))) }} ->
      CMFunctor K M (\ R -> List $ ConstrAsmCont K List (\B -> V (B -x- R)))
    cmFuncListAsm {{cvm = cvm}} = record { _<$CM>_ = \ f lst -> sequenceM (map (sequenceM o map \ (A , v , p , k) -> snd <$> get { {!!} } {{ k = {!!} }} p >>= f >>= \ b -> new {{ k = {!!} }} (v , b) >>= \ p' -> return (A , v , p' , {!!} )) lst) }
      where open ConstrVarMonad cvm

defaultConstrCLVarMonadStateM : Set -> Set
defaultConstrCLVarMonadStateM = StateT
  (ConstrAsmCont defaultConstraint defCont
    (ConstrAsmPtr defaultConstraint defaultVarMonadStateM NatPtr defCont))
  defaultVarMonadStateM

defaultConstrCLVarMonadV : Set -> Set
defaultConstrCLVarMonadV = ConstrAsmPtr defaultConstraint defaultVarMonadStateM NatPtr defCont

defaultConstrCLVarMonad : ConstrCLVarMonad defaultConstraint defaultConstrCLVarMonadStateM defaultConstrCLVarMonadV defCont
defaultConstrCLVarMonad = ConstrVarMonad=>ConstrCLVarMonad defaultConstrVarMonad [] {{mfunc = cmFuncListAsm}}

runDefConstrTrackVarMonad : defaultConstrCLVarMonadStateM A -> A
runDefConstrTrackVarMonad = runDefVarMonad o \ m -> fst <$> m []

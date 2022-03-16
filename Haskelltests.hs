{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.List
import Data.Maybe

infixr :+:
data (f :+: g) a = Inl (f a) | Inr (g a) deriving (Show, Eq, Ord)

data Unit b a = Unit b deriving (Show, Eq, Ord)

data Fix f = In (f (Fix f))
deriving instance (Eq (f (Fix f))) => Eq (Fix f)
deriving instance (Show (f (Fix f))) => Show (Fix f)
deriving instance (Ord (f (Fix f))) => Ord (Fix f)

instance Functor (Unit a) where
  fmap _ (Unit x) = Unit x

instance (Functor a, Functor b) => Functor (a :+: b) where
  fmap f (Inl x) = Inl (fmap f x)
  fmap f (Inr x) = Inr (fmap f x)

foldF :: (Functor f) => (f a -> a) -> Fix f -> a
foldF alg (In x) = alg $ fmap (foldF alg) x

class Eval f a where
  eval :: f a -> a

instance (Eval f a, Eval g a) => Eval (f :+: g) a where
  eval (Inl x) = eval x
  eval (Inr x) = eval x

---------------------------------
data ConstOp t a = ConstOp t deriving (Show, Eq, Ord)

instance Functor (ConstOp t) where
  fmap _ (ConstOp t) = (ConstOp t)

instance forall c. Eval (ConstOp c) c where
  eval (ConstOp c) = c

---------------------------------

data MonOp t a = MonOp a deriving (Show, Eq, Ord)

instance Functor (MonOp a) where
  fmap f (MonOp x) = MonOp (f x)

class MonOpEval t a where
  monFunc :: a -> a

instance forall t a. (MonOpEval t a) => Eval (MonOp t) a where
  eval (MonOp x) = monFunc @t x

--------------------------------

data BinOp t a = BinOp a a deriving (Show, Eq, Ord)

instance Functor (BinOp t) where
  fmap f (BinOp x y) = BinOp (f x) (f y)

class BinOpEval t a where
  binFunc :: a -> a -> a

instance forall t a. (BinOpEval t a) => Eval (BinOp t) a where
  eval (BinOp x y) = binFunc @t x y

---------------------------------

class (Functor f, Functor g) => f :<: g where
  inj :: f a -> g a

instance (Functor f) => f :<: f where
  inj = id

instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl

instance (Functor f, Functor g, Functor h, f :<: h) => f :<: (g :+: h) where
  inj = Inr . inj

inject :: (g :<: f) => g (Fix f) -> Fix f
inject = In . inj

---------------------------------

data AND = AND deriving (Show, Eq, Ord)
data OR = OR deriving (Show, Eq, Ord)
data NOT = NOT deriving (Show, Eq, Ord)

type Expr =
      BinOp AND
  :+: BinOp OR
  :+: MonOp NOT
  :+: ConstOp Bool

evalExpr :: Fix Expr -> Bool
evalExpr = foldF eval

--evalExpr (one /\ (zero \/ one))

(/\) :: (BinOp AND :<: f) => (Fix f) -> (Fix f) -> (Fix f)
a /\ b = inject (BinOp @AND a b)

(\/) :: (BinOp OR :<: f) => (Fix f) -> (Fix f) -> (Fix f)
a \/ b = inject (BinOp @OR a b)

notb :: (MonOp NOT :<: f) => (Fix f) -> (Fix f)
notb x = inject (MonOp @NOT x)

one :: (ConstOp Bool :<: f) => (Fix f)
one = inject (ConstOp True)

zero :: (ConstOp Bool :<: f) => (Fix f)
zero = inject (ConstOp False)

con :: (ConstOp a :<: f) => a -> Fix f
con = inject . ConstOp

instance BinOpEval AND Bool where
  binFunc = (&&)

instance BinOpEval OR Bool where
  binFunc = (||)

instance MonOpEval NOT Bool where
  monFunc = not


----------------------------------------
--partial evaluation
----------------------------------------

data Var b a = Var b deriving(Show, Eq, Ord)
type ParExpr b = (Var b) :+: Expr

instance Functor (Var b) where
  fmap _ (Var b) = (Var b)

var :: (Var b :<: f) => b -> Fix f
var = inject . Var

{-
Creating a partial function from a total one:
When variable is present, return total value iff stays the same for all evaluations
of the variable
-}

class PartialEval f g a where
  evalPart :: f (Either a (Fix g)) -> Either a (Fix g)

instance (PartialEval f h a, PartialEval g h a) => PartialEval (f :+: g) h a where
  evalPart (Inl x) = evalPart x
  evalPart (Inr x) = evalPart x

instance (Var b :<: g) => PartialEval (Var b) g a where
  evalPart (Var b) = Right $ var b

instance forall c g. PartialEval (ConstOp c) g c where
  evalPart (ConstOp c) = Left $ c

instance forall t e g. (Eq e, Enum e, Bounded e, MonOpEval t e) => PartialEval (MonOp t) g e where
  evalPart (MonOp (Left x)) = Left $ monFunc @t x
  evalPart (MonOp (Right expr)) = toUniqueValue expr [monFunc @t x | x <- [minBound..maxBound]]

instance forall t e g. (Eq e, Enum e, Bounded e, BinOpEval t e, ConstOp e :<: g, BinOp t :<: g) => PartialEval (BinOp t) g e where
  evalPart (BinOp (Left x) (Left y)) = Left $ binFunc @t x y
  evalPart (BinOp (Right expr) (Left y)) = toUniqueValue
                                            (inject $ BinOp @t expr (con y))
                                            [binFunc @t x y | x <- [minBound..maxBound]]
  evalPart (BinOp (Left x) (Right expr)) = toUniqueValue
                                            (inject $ BinOp @t (con x) expr)
                                            [binFunc @t x y | y <- [minBound..maxBound]]

toUniqueValue :: (Eq e) => b -> [e] -> Either e b
toUniqueValue def vals
  | length (filter (not . null) groups) == 1 = Left $ fromJust $ find (not . null) groups >>= listToMaybe
  | otherwise = Right def
  where groups = groupBy (==) vals

evalPartBool :: Fix (ParExpr Integer) -> Either Bool (Fix (ParExpr Integer))
evalPartBool = foldF evalPart

--evalPartBool $ con True \/ var 1
--evalPartBool $ con False \/ var 1
--evalPartBool $ (con False /\ var 2) \/ var 1

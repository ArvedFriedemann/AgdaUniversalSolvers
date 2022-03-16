{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

data (f :+: g) a = Inl (f a) | Inr (g a)

data Unit b a = Unit b

data Fix f = In (f (Fix f))

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
data ConstOp t a = ConstOp

instance Functor (ConstOp t) where
  fmap _ ConstOp = ConstOp

class ConstOpEval t a where
  constFunc :: a

instance forall t a.(ConstOpEval t a) => Eval (ConstOp t) a where
  eval ConstOp = constFunc @t

---------------------------------

data MonOp t a = MonOp a

instance Functor (MonOp a) where
  fmap f (MonOp x) = MonOp (f x)

class MonOpEval t a where
  monFunc :: a -> a

instance forall t a. (MonOpEval t a) => Eval (MonOp t) a where
  eval (MonOp x) = monFunc @t x

--------------------------------

data BinOp t a = BinOp a a

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

instance (Functor f, Functor g, f :<: h) => f :<: (g :+: h) where
  inj = Inr . inj

inject :: (g :<: f) => g (Fix f) -> Fix f
inject = In . inj

---------------------------------

data AND = AND
data OR = OR
data NOT = NOT
data ONE = ONE
data ZERO = ZERO

type Expr =
      BinOp AND
  :+: BinOp OR
  :+: MonOp NOT
  :+: ConstOp ONE
  :+: ConstOp ZERO

evalExpr :: Fix Expr -> Bool
evalExpr = foldF eval

(/\) :: (BinOp AND :<: f) => (Fix f) -> (Fix f) -> (Fix f)
a /\ b = inject (BinOp @AND a b)

(\/) :: (BinOp OR :<: f) => (Fix f) -> (Fix f) -> (Fix f)
a \/ b = inject (BinOp @OR a b)

notb :: (MonOp NOT :<: f) => (Fix f) -> (Fix f)
notb x = inject (MonOp @NOT x)

one :: (ConstOp ONE :<: f) => (Fix f)
one = inject (ConstOp @ONE)

zero :: (ConstOp ZERO :<: f) => (Fix f)
zero = inject (ConstOp @ZERO)

instance BinOpEval AND Bool where
  binFunc = (&&)

instance BinOpEval OR Bool where
  binFunc = (||)

instance MonOpEval NOT Bool where
  monFunc = not

instance ConstOpEval ONE Bool where
  constFunc = True

instance ConstOpEval ZERO Bool where
  constFunc = False

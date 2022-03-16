{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

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
  fmap ConstOp = ConstOp

class ConstOpEval t a where
  constFunc :: a

instance (ConstOpEval t a) => Eval (ConstOp t) a where
  eval ConstOp = constFunc

---------------------------------

data MonOp t a = MonOp a

instance Functor (MonOp a) where
  fmap f (MonOp x) = MonOp (f x)

class MonOpEval t a where
  monFunc :: a -> a

instance (MonOpEval t a) => Eval (MonOp t) a where
  eval (MonOp x) = monFunc (eval x)

--------------------------------

data BinOp t a = BinOp a a

instance Functor (BinOp t) where
  fmap f (BinOp x y) = BinOp (f x) (f y)

class BinOpEval t a where
  binFunc :: a -> a -> a

instance (BinOpEval t a) => Eval (BinOp t) a where
  eval (BinOp x y) = binFunc (eval x) (eval y)


---------------------------------

data AND = AND
data OR = OR
data NOT = NOT
data ONE = ONE
data ZERO = ZERO

type Expr f =
      BinOp AND
  :+: BinOp OR
  :+: MonOp NOT
  :+: ConstOp ONE
  :+: ConstOp ZERO


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

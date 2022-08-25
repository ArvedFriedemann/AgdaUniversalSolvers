{-# OPTIONS --type-in-type #-}
module SafePointers.SafePointers where

open import AgdaAsciiPrelude.AsciiPrelude
open import Category.Monad.Indexed renaming (RawIMonad to IMonad)
open import Category.Monad.State


private
  variable
    X Y Z K S : Set
    XS YS ZS : List Set
    V M : Set -> Set
{-}
instance
  stateTIMonad : {{mon : Monad M}} -> StateTIMonad (IState S M)
  stateTIMonad {S = S} {{mon = mon}}
  -}

data HList : List Set -> Set where
  nil : HList []
  cons : forall {X} {XS} -> X -> HList XS -> HList (X :: XS)

snoc : X -> HList XS -> HList (XS ++ [ X ])
snoc x nil = cons x nil
snoc x (cons y ys) = cons y (snoc x ys)


data Elem : Set -> List Set -> Set where
  here : forall {X XS} -> Elem X (X :: XS)
  there : forall {X Y XS} -> Elem X XS -> Elem X (Y :: XS)

lastElem : HList (XS ++ [ X ]) -> Elem X (XS ++ [ X ])
lastElem {[]} lst = here
lastElem {x :: XS} (cons x₁ lst) = there (lastElem lst)

get : Elem X XS -> HList XS -> X
get here (cons x _) = x
get (there e) (cons _ xs) = get e xs

EnvironmentT : (Set -> Set) -> List Set -> List Set -> Set -> Set
EnvironmentT M XS YS A = IStateT HList M XS YS A

-- new : X -> EnvironmentT M (EV (Snoc X XS)) XS (Snoc X XS) (EV X (Snoc X XS))


extend : Elem X XS -> Elem X (XS ++ [ Y ])
extend {_} {[]} e = there e
extend {_} {_ :: xs} here = here
extend {_} {x :: xs} (there x₁) = there (extend x₁)

extend' : Elem X XS -> Elem X (XS ++ YS)
extend' {_} {[]} ()
extend' {_} {_ :: xs} here = here
extend' {_} {x :: xs} (there x₁) = there (extend' x₁)


EV : List Set -> Set -> Set
EV context val = Elem val context

new : {{mon : Monad M}} -> X -> EnvironmentT M XS (XS ++ [ X ]) (EV (XS ++ [ X ]) X)
new x old = return (lastElem (snoc x old), snoc x old)


read : {{mon : Monad M}} -> EV XS X -> EnvironmentT M (XS ++ YS) (XS ++ YS) X
read v old = return {!!}{!!}

write : EV XS X -> X -> EnvironmentT M (XS ++ YS) (XS ++ YS) T
write = {!!}

--V X = Elem X XS

  -- new
  --   :: forall f m i j x
  --    . ( Snoc x i j
  --      , Applicative m
  --      )
  --   => f x
  --   -> EnvironmentT f m i j (Elem x j)
  -- new x = IxStateT \init -> do
  --   let extended :: HListF f j
  --       extended = snoc x init
  --
  --   pure (last extended, extended)

-- --
-- class Snoc x xs ys | x xs -> ys, ys -> x xs where
--   snoc :: f x -> HListF f xs -> HListF f ys
--   last :: HListF f ys -> Elem x ys
--   extend :: Elem x xs -> Elem x ys
--
-- instance Snoc x '[] (x ': '[]) where
--   snoc x Nil = Cons x Nil
--   last (Cons _ Nil) = Here
--   extend = \case
--
-- instance Snoc x yss (z ': zss) => Snoc x (y ': yss) (y ': (z ': zss)) where
--   snoc x (Cons y ys) = Cons y (snoc x ys)
--   last (Cons _ ys) = There (last ys)
--
--   extend = \case
--     Here -> Here
--     There x -> There (extend x)

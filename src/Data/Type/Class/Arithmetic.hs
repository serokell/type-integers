{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoStarIsType #-}

module Data.Type.Class.Arithmetic where

import Data.Singletons.TH
import Data.Singletons.Prelude.Num
import Data.Type.Natural hiding (induction)
import Unsafe.Coerce

import Data.Type.Internal.Integer

class IsCommutativeRing z where
  type Zero' :: z
  type One' :: z
  type Inv (m :: z) :: z

  oneIsNotZero :: forall (x :: z) (y :: z). (y ~ Zero', x ~ One') => x :~: y -> Void
  associativity
    :: Sing (x :: z)
    -> Sing y
    -> Sing n
    -> (x + y) + n :~: x + (y + n)
  commutativity
    :: forall (x :: z) (y :: z). Sing x
    -> Sing y
    -> x + y :~: y + x
  multRightDistrib
    :: forall (x :: z) (y :: z) (u :: z). Sing x
    -> Sing y
    -> Sing u
    -> (x * (y + u)) :~: ((x * y) + (x * u))
  zeroNeutral
    :: forall (x :: z). Sing x
    -> Zero' + x :~: x
  oneNeutral
    :: forall (x :: z). Sing x
    -> x * One' :~: x
  inverseAxiom
    :: forall (x :: z). Sing x
    -> (x + Inv x) :~: Zero'
  associativityProduct
    :: forall (m :: z) (n :: z) (p :: z). Sing m
    -> Sing n
    -> Sing p
    -> (m * n) * p :~: m * (n * p)
  commutativityProduct
    :: forall (m :: z) (n :: z). Sing m
    -> Sing n
    -> m * n :~: n * m
  invPostulate
    :: forall (m :: z). Sing m
    -> (Inv m) :~: (Negate m)

class IsCommutativeRing z => IsInteger z where
  type Signum (m :: z) :: Sign
  type Absolute'' (m :: z) :: Nat

  zeroEquality :: (Absolute'' x ~ Absolute'' y, Absolute'' x ~ 'Z) => x :~: y
  zeroEquality = unsafeCoerce Refl
  zeroEquality' :: Absolute'' x :~: Absolute'' y -> Absolute'' x :~: 'Z -> x :~: y
  zeroEquality' Refl Refl = unsafeCoerce Refl

  induction  :: forall k p. p Zero'
             -> (forall (n :: z). ((Zero' <= n) ~ 'True) => Sing n -> p n -> p (One' + n))
             -> (forall (n :: z). ((Zero' <= n) ~ 'True) => Sing (Inv n) -> p n -> p (Inv n))
             -> Sing k -> p k
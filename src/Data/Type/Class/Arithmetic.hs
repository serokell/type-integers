{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Data.Type.Class.Arithmetic where

import Data.Singletons.TH
import Data.Type.Natural hiding (induction)
import Unsafe.Coerce

import Data.Type.Internal.Integer

class IsCommutativeRing z where
  type Zero' :: z
  type One' :: z
  type Inv (m :: z) :: z

  oneIsNotZero :: One' :~: Zero' -> Void
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
    :: forall x. Sing x
    -> x * One' :~: x
  inverseAxiom
    :: forall x. Sing x
    -> (x + Inv x) :~: Zero'

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
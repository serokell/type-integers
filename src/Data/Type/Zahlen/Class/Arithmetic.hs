{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NoStarIsType        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Zahlen.Class.Arithmetic where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.Typeable
import Unsafe.Coerce

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Type.Natural
import Data.Type.Natural.Class.Arithmetic
import Data.Type.Natural.Class.Order (leqAntisymm, leqRefl, leqTrans)
import Proof.Propositional

import Data.Type.Zahlen.Definitions

-- Equality

-- TODO: Remove comment
--posInjective
--  :: forall n m. Pos n :~: Pos m
--  -> n :~: m
--posInjective Refl = Refl
--
--negInjective
--  :: forall n m. Neg n :~: Neg m
--  -> n :~: m
--negInjective Refl = Refl
--
--posLemma
--  :: forall n m. n :~: m
--  -> Pos n :~: Pos m
--posLemma Refl = Refl
--
--negLemma
--  :: forall n m. n :~: m
--  -> Neg n :~: Neg m
--negLemma Refl = Refl
--
--plusCong
--  :: forall (n :: Zahlen) (m :: Zahlen) (p :: Zahlen). n :~: m
--  -> n + p :~: m + p
--plusCong Refl = Refl
--
--plusCong'
--  :: forall (n :: Nat) (m :: Nat) (p :: Nat). Sing n
--  -> Sing m
--  -> Sing p
--  -> n + m :~: p
--  -> Pos n + Pos m :~: Pos p
--plusCong' n m p Refl = Refl
--
--multCong
--  :: forall (n :: Zahlen) (m :: Zahlen) (p :: Zahlen). n :~: m
--  -> (n * p) :~: (m * p)
--multCong Refl = Refl
--
--negNeg
--  :: forall n. Sing (n :: Zahlen)
--  -> Negate (Negate n) :~: n
--negNeg (SPos n) = Refl
--negNeg (SNeg n) = Refl
--
--absoluteIdem
--  :: forall n. Sing n
--  -> Absolute (Absolute n) :~: Absolute n
--absoluteIdem (SPos n) = Refl
--absoluteIdem (SNeg n) = Refl
--
--zeroIdentity
--  :: forall (m :: Zahlen). Sing m
--  -> Pos Z + m :~: m
--zeroIdentity (SPos n)      = Refl
--zeroIdentity (SNeg SZ)     = unsafeCoerce Refl
--zeroIdentity (SNeg (SS n)) = Refl
--
--zeroIdentityR
--  :: forall (m :: Zahlen). Sing m
--  -> m + Pos Z :~: m
--zeroIdentityR (SPos SZ) = Refl
--zeroIdentityR (SPos (SS n)) =
--  plusCong' (SS n) SZ (SS n) (plusZeroR (SS n))
--zeroIdentityR (SNeg SZ) = unsafeCoerce Refl
--zeroIdentityR (SNeg (SS n)) = Refl
--
--plusAssoc
--  :: forall (m :: Zahlen) (n :: Zahlen) (p :: Zahlen). Sing m
--  -> Sing n
--  -> Sing p
--  -> m + n + p :~: m + (n + p)
--plusAssoc (SPos SZ) (SPos SZ) (SPos SZ)         = Refl
--plusAssoc (SPos SZ) (SPos (SS n)) (SPos SZ)     = Refl
--plusAssoc (SPos SZ) (SPos (SS n)) (SPos (SS p)) = Refl
--plusAssoc (SPos (SS n)) (SPos SZ) (SPos SZ)     = undefined
--plusAssoc m n p                                 = undefined

--class IsCommutativeRing z where
--  type Zero' :: z
--  type One' :: z
--  type Inv (m :: z) :: z
--
--  oneIsNotZero :: One' :~: Zero' -> Void
--  associativity
--    :: forall x y z. Sing x
--    -> Sing y
--    -> Sing z
--    -> (x + y) + z :~: x + (y + z)
--  commutativity
--    :: forall x y. Sing x
--    -> Sing y
--    -> x + y :~: y + z
--  distr
--    :: forall x y z. Sing x
--    -> Sing y
--    -> Sing z
--    -> (x * (y + z)) :~: ((x * y) + (x * z))
--  zeroNeutral
--    :: forall x. Sing x
--    -> x + Zero' :~: x
--  oneNeutral
--    :: forall x. Sing x
--    -> x * One' :~: x
--  inverseAxiom
--    :: forall x. Sing x
--    -> (x + Inv x) :~: Zero'
-- end TODO

--class IsCommutativeRing z => IsInteger z where
--  type Signum (m :: z) :: Sign
--  type Absolute'' (m :: z) :: Nat
--
--  zeroEquality :: (Absolute'' x ~ Absolute'' y, Absolute'' x ~ 'Z) => x :~: y
--  zeroEquality = unsafeCoerce Refl
--  zeroEquality' :: Absolute'' x :~: Absolute'' y -> Absolute'' x :~: 'Z -> x :~: y
--  zeroEquality' Refl Refl = unsafeCoerce Refl

--  zeroIdentity :: forall x m. Absolute'' x :~: 'Z -> x + m :~: m
--  zeroIdentity = Refl

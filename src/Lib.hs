--{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes#-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses#-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Lib where

--import Data.Promotion.Prelude.Enum
import Data.Type.Natural
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable
import Data.Type.Equality

import Unsafe.Coerce

import Data.Kind                    (Type, Constraint)

singletons [d|
  data Zahlen = Pos Nat | Neg Nat
    deriving (Show, Eq)
  |]

deriving instance Typeable 'Neg
deriving instance Typeable 'Pos

singletons [d|
  data Sign = P | N
    deriving (Show, Eq)

  opposite
    :: Sign
    -> Sign
  opposite P = N
  opposine N = P

  signZ
    :: Zahlen
    -> Zahlen
  signZ (Pos (S n)) = Pos (S Z)
  signZ (Neg (S n)) = Neg (S Z)
  signZ (Pos Z) = Pos Z
  signZ (Neg Z) = Pos Z

  signOf
    :: Zahlen
    -> Sign
  signOf (Pos _) = P
  singOf (Neg _) = N

  signMult
    :: Sign
    -> Sign
    -> Sign
  signMult P s2 = s2
  signMult N s2 = opposite N

  signToZ
    :: Sign
    -> Nat
    -> Zahlen
  signToZ P = Pos
  signToZ N = Neg
  |]

singletons [d|

  absolute'
    :: Zahlen
    -> Nat
  absolute' (Pos n) = n
  absolute' (Neg n) = n

  absolute
    :: Zahlen
    -> Zahlen
  absolute (Pos n) = Pos n
  absolute (Neg n) = Pos n

  inverse
    :: Zahlen
    -> Zahlen
  inverse (Pos n) = Neg n
  inverse (Neg n) = Pos n
  |]

singletons [d|
  instance Ord Zahlen where
    Pos n <= Pos m = n <= m
    Neg _ <= Pos _ = True
    Neg n <= Neg m = m <= n
    Pos _ <= Neg _ = False
  |]

singletons [d|
  instance Enum Zahlen where
    fromEnum (Pos n) = fromEnum n
    fromEnum (Neg n) = -1 * fromEnum n

    toEnum n =
      case (n >= 0) of
        True ->  Pos $ toEnum n
        False -> Neg $ toEnum n
  |]

singletons [d|
  sub
    :: Nat
    -> Nat
    -> Zahlen
  sub m Z = Pos m
  sub Z (S n) = Neg (S n)
  sub (S m) (S n) = m `sub` n
  |]

singletons [d|
  instance Num Zahlen where
    Neg m + Neg n = Neg (m + n)
    Pos m + Pos n = Pos (m + n)
    Pos m + Neg (S n) = m `sub` S n
    Neg (S m) + Pos n = n `sub` S m

    n * m = case (signOf n, signOf m) of
      (s1, s2) -> (signToZ $ s1 `signMult` s2) $ prodNat
      where
        prodNat = absolute' n * absolute' m

    abs = absolute

    signum = signZ

    negate = inverse

    fromInteger n =
      case (n >= 0) of
        True -> Pos $ fromInteger n
        False -> Neg $ fromInteger n
  |]

class IsCommutativeRing z where
  type Zero' :: z
  type One' :: z
  type Inv (m :: z) :: z

  oneIsNotZero :: One' :~: Zero' -> Void
  associativity
    :: forall x y z. Sing x
    -> Sing y
    -> Sing z
    -> (x + y) + z :~: x + (y + z)
  commutativity
    :: forall x y. Sing x
    -> Sing y
    -> x + y :~: y + z
  distr
    :: forall x y z. Sing x
    -> Sing y
    -> Sing z
    -> (x * (y + z)) :~: ((x * y) + (x * z))
  zeroNeutral
    :: forall x. Sing x
    -> x + Zero' :~: x
  oneNeutral
    :: forall x. Sing x
    -> x * One' :~: x
  inverseAxiom
    :: forall x. Sing x
    -> (x + Inv x) :~: Zero'

instance IsCommutativeRing Zahlen where
  type Zero' = ('Pos 'Z)
  type One' = ('Pos (S Z))
  type Inv m = Inverse m
--   zeroIdentity :: forall x m. Absolute'' x :~: 'Z -> x + m :~: m
--   zeroIdentity Refl = Refl `because` (Proxy )

class IsCommutativeRing z => IsInteger z where
  type Signum (m :: z) :: Sign
  type Absolute'' (m :: z) :: Nat

  zeroEquality :: (Absolute'' x ~ Absolute'' y, Absolute'' x ~ 'Z) => x :~: y
  zeroEquality = unsafeCoerce Refl
  zeroEquality' :: Absolute'' x :~: Absolute'' y -> Absolute'' x :~: 'Z -> x :~: y
  zeroEquality' Refl Refl = unsafeCoerce Refl
  zeroIdentity :: forall x m. Absolute'' x :~: 'Z -> x + m :~: m
--  zeroIdentity = Refl

instance IsInteger Zahlen where
  type Signum ('Pos m) = P
  type Signum ('Neg m) = N
  type Absolute'' (_ m) = m

natToZ :: Sing n -> Sing (Pos n)
natToZ SZ = SPos SZ
natToZ (SS n) = SPos (SS n)

zToNat :: Sing (Pos n) -> Sing n
zToNat (SPos n) = n

zToNatNeg :: Sing (Neg n) -> Sing n
zToNatNeg (SNeg n) = n

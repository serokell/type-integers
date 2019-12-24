{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib where

import Data.Promotion.Prelude.Enum
import Data.Type.Natural
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable

import Unsafe.Coerce

singletons [d|
  data Zahlen = Pos Nat | Neg Nat
    deriving (Show, Eq)
  |]

deriving instance Typeable 'Pos
deriving instance Typeable 'Neg

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

natToZ :: Sing n -> Sing (Pos n)
natToZ SZ = SPos SZ
natToZ (SS n) = SPos (SS n)

zToNat :: Sing (Pos n) -> Sing n
zToNat (SPos n) = n

zToNatNeg :: Sing (Neg n) -> Sing n
zToNatNeg (SNeg n) = n

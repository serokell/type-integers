{-# LANGUAGE DataKinds #-}
--{-# LANGUAGE AllowAmbiguousTypes#-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Internal.Integer where

import Data.Type.Natural hiding (induction, plusSuccL, plusSuccR)
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Typeable

import Prelude hiding (Integer)

$(singletons [d|
  data Integer = Pos Nat | Neg Nat
    deriving (Show, Eq)
  |])

deriving instance Typeable 'Neg
deriving instance Typeable 'Pos

singletons [d|
  data Sign = P | N
    deriving (Show, Eq)

  opposite
    :: Sign
    -> Sign
  opposite P = N
  opposite N = P

  signZ
    :: Integer
    -> Integer
  signZ (Pos (S _)) = Pos (S Z)
  signZ (Neg (S _)) = Neg (S Z)
  signZ (Pos Z) = Pos Z
  signZ (Neg Z) = Pos Z

  signOf
    :: Integer
    -> Sign
  signOf (Pos _) = P
  signOf (Neg _) = N

  signMult
    :: Sign
    -> Sign
    -> Sign

  signMult P P = P
  signMult N N = P
  signMult N P = N
  signMult P N = N

  signToZ
    :: Sign
    -> Nat
    -> Integer
  signToZ P = Pos
  signToZ N = Neg
  |]

singletons [d|

  absolute'
    :: Integer
    -> Nat
  absolute' (Pos n) = n
  absolute' (Neg n) = n

  absolute
    :: Integer
    -> Integer
  absolute (Pos n) = Pos n
  absolute (Neg n) = Pos n

  inverse
    :: Integer
    -> Integer
  inverse (Pos n) = Neg n
  inverse (Neg n) = Pos n
  |]

singletons [d|
  instance Ord Integer where
    Pos n <= Pos m = n <= m
    Neg _ <= Pos _ = True
    Neg n <= Neg m = m <= n
    Pos _ <= Neg _ = False
  |]

singletons [d|
  instance Enum Integer where
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
    -> Integer
  sub m Z = Pos m
  sub Z (S m) = Neg (S m)
  sub (S m) (S n) = m `sub` n
  |]

singletons [d|
  instance Num Integer where
    Neg m + Neg n = Neg (m + n)
    Pos m + Pos n = Pos (m + n)
    Pos m + Neg n = m `sub` n
    Neg m + Pos n = n `sub` m

    (Pos n) * (Pos m) = Pos $ n * m
    (Neg n) * (Neg m) = Pos $ n * m
    (Pos n) * (Neg m) = Neg $ n * m
    (Neg n) * (Pos m) = Neg $ n * m

    abs = absolute

    signum = signZ

    negate = inverse

    fromInteger n =
      case (n >= 0) of
        True -> Pos $ fromInteger n
        False -> Neg $ fromInteger n
  |]

natToZ :: Sing n -> Sing ('Pos n)
natToZ SZ = SPos SZ
natToZ (SS n) = SPos (SS n)

zToNat :: Sing ('Pos n) -> Sing n
zToNat (SPos n) = n

zToNatNeg :: Sing ('Neg n) -> Sing n
zToNatNeg (SNeg n) = n
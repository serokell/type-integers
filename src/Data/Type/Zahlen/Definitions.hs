{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE EmptyCase                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE NoStarIsType             #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module Data.Type.Zahlen.Definitions where

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Type.Natural
import Data.Typeable

import Unsafe.Coerce

import Data.Kind (Constraint, Type)

singletons [d|
  data Zahlen = Pos Nat | Neg Nat
    deriving (Show, Eq)
  |]

deriving instance Typeable 'Neg
deriving instance Typeable 'Pos

singletons [d|
  data Sign = P | N
    deriving (Show, Eq)
  |]

singletons [d|
  opposite
    :: Sign
    -> Sign
  opposite P = N
  opposine N = P
  |]

singletons [d|
  signZ
    :: Zahlen
    -> Zahlen
  signZ (Pos (S n)) = Pos (S Z)
  signZ (Neg (S n)) = Neg (S Z)
  signZ (Pos Z)     = Pos Z
  signZ (Neg Z)     = Pos Z
  |]

singletons [d|
  signOf
    :: Zahlen
    -> Sign
  signOf (Pos _) = P
  singOf (Neg _) = N
  |]

singletons [d|
  signMult
    :: Sign
    -> Sign
    -> Sign
  signMult P s2 = s2
  signMult N s2 = opposite N
  |]

singletons [d|
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
  |]

singletons [d|
  absolute
    :: Zahlen
    -> Zahlen
  absolute (Pos n) = Pos n
  absolute (Neg n) = Pos n
  |]

singletons [d|
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
        True  ->  Pos $ toEnum n
        False -> Neg $ toEnum n
  |]

singletons [d|
  sub
    :: Nat
    -> Nat
    -> Zahlen
  sub m Z         = Pos m
  sub Z (S n)     = Neg (S n)
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
        True  -> Pos $ fromInteger n
        False -> Neg $ fromInteger n
  |]

natToZ :: Sing n -> Sing (Pos n)
natToZ SZ     = SPos SZ
natToZ (SS n) = SPos (SS n)

zToNat :: Sing (Pos n) -> Sing n
zToNat (SPos n) = n

zToNatNeg :: Sing (Neg n) -> Sing n
zToNatNeg (SNeg n) = n

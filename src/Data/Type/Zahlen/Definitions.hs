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
import Data.Singletons.TH
import Data.Type.Natural

{-| We represent integers with two constructors @Pos :: Nat -> Zahlen@ and
    @Neg1 :: Nat -> Zahlen@, such that @Pos n@ represents the integer /n/ and
    @Neg1 n@ represents the integer /-n - 1/. Note that zero has two representations
    under this scheme.
-}
singletons [d|
  data Zahlen = Pos Nat
              | Neg1 Nat
    deriving (Show, Eq)
  |]

{-| The sign of a 'Zahlen'. -}
-- TODO: Decide what to do with sign
--singletons [d|
--  data Sign = P | N
--    deriving (Show, Eq)
--  |]

{-| Flip a sign. -}
-- TODO: Decide what to do with sign
--singletons [d|
--  opposite
--    :: Sign
--    -> Sign
--  opposite P = N
--  opposite N = P
--  |]

{-| Get the sign of a 'Zahlen' as a 'Zahlen'. Note that the sign of either zero
    representation is @Pos Z@.
-}
-- TODO: Decide what to do with signZ
--singletons [d|
--  signZ
--    :: Zahlen
--    -> Zahlen
--  signZ (Pos (S n)) = Pos (S Z)
--  signZ (Neg (S n)) = Neg (S Z)
--  signZ (Pos Z)     = Pos Z
--  signZ (Neg Z)     = Pos Z
--  |]

{-| Get the sign of a 'Zahlen' as a 'Sign'. Note that the sign of @Pos Z@ is @P@
    and the sign of @Neg z@ is @N@.
-}
-- TODO: Decide what to do with sign
--singletons [d|
--  signOf
--    :: Zahlen
--    -> Sign
--  signOf (Pos _) = P
--  signOf (Neg _) = N
--  |]

{-| Get the sign of a product from the signs of the factors. -}
-- TODO: Decide what to do with sign
--singletons [d|
--  signMult
--    :: Sign
--    -> Sign
--    -> Sign
--  signMult P s2 = s2
--  signMult N s2 = opposite N
--  |]

{-| Construct a @Zahlen@ from a @Sign@ and @Nat@. |-}
--singletons [d|
--  signToZ
--    :: Sign
--    -> Nat
--    -> Zahlen
--  signToZ P = Pos
--  signToZ N = Neg
--  |]

{-| Get the absolute value of a @Zahlen@ as a @Nat@. |-}
singletons [d|
  absNat
    :: Zahlen
    -> Nat
  absNat (Pos n) = n
  absNat (Neg1 n) = S n
  |]

{-| Subtract two @Nat@s to get a @Zahlen@. |-}
-- TODO: Decide if this is necessary
--singletons [d|
--  sub
--    :: Nat
--    -> Nat
--    -> Zahlen
--  sub m Z         = Pos m
--  sub Z (S n)     = Neg (S n)
--  sub (S m) (S n) = m `sub` n
--  |]

singletons [d|
  instance Ord Zahlen where
    Pos n <= Pos m = n <= m
    Neg1 _ <= Pos _ = True
    Neg1 n <= Neg1 m = m <= n
    Pos _ <= Neg1 _ = False
  |]

singletons [d|
  instance Enum Zahlen where
    fromEnum (Pos n) = fromEnum n
    fromEnum (Neg1 n) = - fromEnum n - 1

    toEnum n =
      if n >= 0
        then Pos $ toEnum n
        else Neg1 $ toEnum (-n - 1)
  |]

singletons [d|
  instance Num Zahlen where
    Pos m + Pos n = Pos (m + n)
    Neg1 m + Neg1 n = Neg1 (S (m + n))
    Neg1 m + Pos n = Pos n + Neg1 m
    Pos Z + Neg1 n = Neg1 n
    Pos (S m) + Neg1 Z = Pos m
    Pos (S m) + Neg1 (S n) = Pos m + Neg1 n

    Pos n * Pos m      = Pos (n * m)
    Pos Z * Neg1 m     = Pos Z
    Pos (S n) * Neg1 m = Neg1 (n * m + n + m)
    Neg1 n * Pos m     = Pos m * Neg1 n
    Neg1 n * Neg1 m    = Pos ((S n) * (S m))

    abs (Pos n) = Pos n
    abs (Neg1 n) = Pos (S n)

    signum (Pos Z) = Pos Z
    signum (Pos (S n)) = Pos (S Z)
    signum (Neg1 n) = Neg1 Z

    negate (Pos Z) = Pos Z
    negate (Pos (S n)) = Neg1 n
    negate (Neg1 n) = Pos (S n)

    fromInteger n =
      if n >= 0
        then Pos $ fromInteger n
        else Neg1 $ fromInteger (- n - 1)
  |]

-- TODO: Decide if necessary
--zToNat :: Sing (Pos n) -> Sing n
--zToNat (SPos n) = n
--
--zToNatNeg :: Sing (Neg n) -> Sing n
--zToNatNeg (SNeg n) = n

zahlenToInt :: Integral a => Zahlen -> a
zahlenToInt (Pos n) = natToInt n
zahlenToInt (Neg1 n) = - natToInt n - 1

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

import Data.Kind (Constraint, Type)
import Unsafe.Coerce

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Type.Natural
import Data.Typeable

{-| We represent integers with two constructors @Pos :: Nat -> Zahlen@ and
    @Neg :: Nat -> Zahlen@, such that @Pos n@ represents the integer /n/ and
    @Neg n@ represents the integer /-n/. Note that zero has two representations
    under this scheme.
-}
singletons [d|
  data Zahlen = Pos Nat | Neg1 Nat
    deriving (Show, Eq)
  |]

deriving instance Typeable 'Pos
deriving instance Typeable 'Neg1

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
-- TODO: Decide what to do with absolute'
--singletons [d|
--  absolute'
--    :: Zahlen
--    -> Nat
--  absolute' (Pos n) = n
--  absolute' (Neg n) = n
--  |]

{-| Get the absolute value of a @Zahlen@ as a @Zahlen@. |-}
-- TODO: Decide what to do with absolute
--singletons [d|
--  absolute
--    :: Zahlen
--    -> Zahlen
--  absolute (Pos n) = Pos n
--  absolute (Neg n) = Pos n
--  |]

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

-- TODO: Reimplement
--singletons [d|
--  instance Enum Zahlen where
--    fromEnum (Pos n) = fromEnum n
--    fromEnum (Neg n) = -1 * fromEnum n
--
--    toEnum n =
--      if n >= 0
--        then Pos $ toEnum n
--        else Neg $ toEnum n
--  |]

singletons [d|
  instance Num Zahlen where
    Neg1 m + Neg1 n = Neg1 (m + n + 1)
    Pos m + Pos n = Pos (m + n)
    Neg1 m + Pos n = Pos n + Neg1 m
    Pos Z + Neg1 n = Neg1 n
    Pos (S m) + Neg1 Z = Pos m
    Pos (S m) + Neg1 (S n) = Pos m + Neg1 n

    a * b =
      case (a, b) of
        (Pos n,  Pos m)  -> Pos (n * m)
        (Pos n,  Neg1 m) ->
          case n of
            Z    -> Pos Z
            S n' -> Neg1 (n * m + n')
        (Neg1 n, Pos m)  -> Pos m * Neg1 n
        (Neg1 n, Neg1 m) -> Pos ((n + 1) * (m + 1))

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

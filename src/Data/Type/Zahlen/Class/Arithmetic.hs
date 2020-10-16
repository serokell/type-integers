{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NoStarIsType        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Zahlen.Class.Arithmetic
       ( plusCong, plusCongL, plusCongR
       , multCong, multCongL, multCongR
       , minusCong, minusCongL, minusCongR
       , zeroIdL, zeroIdR, negateNegate, absIdem
       , plusComm, plusAssoc
       ) where

import Data.Singletons.Prelude (type (*), type (+), type (-), Abs, Negate, Sing)
import Data.Type.Natural (Nat (Z, S), SNat (SS, SZ))
import qualified Data.Type.Natural.Class.Arithmetic as Nat
import Data.Typeable ((:~:) (Refl))
import Proof.Equational (trans, cong)
import Data.Proxy (Proxy (Proxy))

import Unsafe.Coerce (unsafeCoerce)

import Data.Type.Zahlen.Definitions (SZahlen (SNeg1, SPos), Zahlen (Neg1, Pos))

-- Equality

-- TODO: Decide if necessary
--posInjective
--  :: forall n m. Pos n :~: Pos m
--  -> n :~: m
--posInjective Refl = Refl
--
--negInjective
--  :: forall n m. Neg n :~: Neg m
--  -> n :~: m
--negInjective Refl = Refl

posLemma
  :: forall n m. n :~: m
  -> 'Pos n :~: 'Pos m
posLemma Refl = Refl

negLemma
  :: forall n m. n :~: m
  -> 'Neg1 n :~: 'Neg1 m
negLemma Refl = Refl

plusCong
  :: forall (n :: Zahlen) (m :: Zahlen) (n' :: Zahlen) (m' :: Zahlen).
     n :~: m
  -> n' :~: m'
  -> n + n' :~: m + m'
plusCong Refl Refl = Refl

plusCongL :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             n :~: m -> Sing k -> n + k :~: m + k
plusCongL Refl _ = Refl

plusCongR :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             Sing k -> n :~: m -> k + n :~: k + m
plusCongR _ Refl = Refl

multCong :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen) (l :: Zahlen).
            n :~: m -> l :~: k -> n * l :~: m * k
multCong Refl Refl = Refl

multCongL :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             n :~: m -> Sing k -> n * k :~: m * k
multCongL Refl _ = Refl

multCongR :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             Sing k -> n :~: m -> k * n :~: k * m
multCongR _ Refl = Refl

minusCong :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen) (l :: Zahlen).
             n :~: m -> l :~: k -> n - l :~: m - k
minusCong Refl Refl = Refl

minusCongL :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
              n :~: m -> Sing k -> n - k :~: m - k
minusCongL Refl _ = Refl

minusCongR :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
              Sing k -> n :~: m -> k - n :~: k - m
minusCongR _ Refl = Refl

--plusCong'
--  :: forall (n :: Nat) (m :: Nat) (p :: Nat). Sing n
--  -> Sing m
--  -> Sing p
--  -> n + m :~: p
--  -> Pos n + Pos m :~: Pos p
--plusCong' n m p Refl = Refl

negateNegate
  :: forall n. Sing (n :: Zahlen)
  -> Negate (Negate n) :~: n
negateNegate (SPos SZ)     = Refl
negateNegate (SPos (SS n)) = Refl
negateNegate (SNeg1 n)     = Refl

absIdem
  :: forall n. Sing (n :: Zahlen)
  -> Abs (Abs n) :~: Abs n
absIdem (SPos n)  = Refl
absIdem (SNeg1 n) = Refl

zeroIdL
  :: forall (m :: Zahlen). Sing m
  -> 'Pos 'Z + m :~: m
zeroIdL (SPos n)  = Refl
zeroIdL (SNeg1 n) = Refl

zeroIdR
  :: forall (m :: Zahlen). Sing m
  -> m + 'Pos 'Z :~: m
zeroIdR sm = trans (plusComm sm (SPos SZ)) (zeroIdL sm)

plusComm :: Sing (n :: Zahlen) -> Sing (m :: Zahlen)
         -> n + m :~: m + n
plusComm (SPos a) (SPos b)   = posLemma (Nat.plusComm a b)
plusComm (SNeg1 a) (SNeg1 b) = cong (Proxy :: Proxy 'Neg1)
                             $ cong (Proxy :: Proxy 'S)
                             $ Nat.plusComm a b
plusComm (SPos a) (SNeg1 b)  = Refl
plusComm (SNeg1 a) (SPos b)  = Refl

plusAssoc
  :: forall (m :: Zahlen) (n :: Zahlen) (p :: Zahlen).
     Sing m
  -> Sing n
  -> Sing p
  -> (m + n) + p :~: m + (n + p)
plusAssoc (SPos sm) (SPos sn) (SPos sp) = posLemma $ Nat.plusAssoc sm sn sp
plusAssoc m n p                         = unsafeCoerce Refl

plusAssoc1
  :: forall (m :: Zahlen) (n :: Zahlen).
     Sing m
  -> Sing n
  -> (m + n) + ('Pos ('S 'Z)) :~: m + (n + ('Pos ('S 'Z)))
plusAssoc1 sm sn = undefined

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

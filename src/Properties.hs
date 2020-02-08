{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}

module Properties where

--import Data.Promotion.Prelude.Enum
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable

import Data.Type.Equality
import Data.Type.Natural
import Data.Type.Natural.Class.Arithmetic
import Data.Type.Natural.Class.Order (leqTrans, leqAntisymm, leqRefl)
import Data.Kind                    (Type)

import Proof.Equational
import Proof.Propositional

import Unsafe.Coerce

import Lib

-- Equality

posInjective
  :: forall n m. Pos n :~: Pos m
  -> n :~: m
posInjective Refl = Refl

posLemma
  :: forall n m. n :~: m
  -> Pos n :~: Pos m
posLemma Refl = Refl

negLemma
  :: forall n m. n :~: m
  -> Neg n :~: Neg m
negLemma Refl = Refl

negInjective
  :: forall n m. Neg n :~: Neg m
  -> n :~: m
negInjective Refl = Refl

plusCongruence
  :: forall (n :: Zahlen) (m :: Zahlen) (p :: Zahlen). Sing n
  -> Sing m
  -> Sing p
  -> n :~: m
  -> n + p :~: m + p
plusCongruence n m p Refl = Refl

plusCongruenceR
  :: forall (m :: Zahlen) (n :: Zahlen) (p :: Zahlen). Sing m
  -> Sing n
  -> Sing p
  -> n :~: p
  -> m + n :~: m + p
plusCongruenceR m n p Refl = Refl

plusCong'
  :: forall (n :: Nat) (m :: Nat) (p :: Nat). Sing n
  -> Sing m
  -> Sing p
  -> n + m :~: p
  -> Pos n + Pos m :~: Pos p
plusCong' n m p Refl = Refl

multCong
  :: forall (n :: Zahlen) (m :: Zahlen) (p :: Zahlen). n :~: m
  -> (n * p) :~: (m * p)
multCong Refl = Refl

negInv
  :: forall n. Sing n
  -> Inverse (Inverse n) :~: n
negInv (SPos n) = Refl
negInv (SNeg n) = Refl

absoluteIdem
  :: forall n. Sing n
  -> Absolute (Absolute n) :~: Absolute n
absoluteIdem (SPos n) = Refl
absoluteIdem (SNeg n) = Refl

zeroIdentity
  :: forall (m :: Zahlen). Sing m
  -> Pos Z + m :~: m
zeroIdentity (SPos n) = Refl
zeroIdentity (SNeg SZ) = unsafeCoerce Refl
zeroIdentity (SNeg (SS n)) = Refl

zeroIdentityR
  :: forall (m :: Zahlen). Sing m
  -> m + Pos Z :~: m
zeroIdentityR (SPos SZ) = Refl
zeroIdentityR (SPos (SS n)) =
  plusCong' (SS n) SZ (SS n) (plusZeroR (SS n))
zeroIdentityR (SNeg SZ) = unsafeCoerce Refl
zeroIdentityR (SNeg (SS n)) = Refl

distrSub
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> (Sub n p + Pos m) :~: Sub (n + m) p
distrSub _ SZ SZ = Refl
distrSub _ SZ (SS p) = Refl
distrSub _ (SS n) SZ = Refl
distrSub m (SS n) (SS p) = distrSub m n p

distrSubR
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Pos m + Sub n p :~: Sub (m + n) p
distrSubR = undefined

plusAssocZ
  :: forall (m :: Zahlen) (n :: Zahlen) (p :: Zahlen). Sing m
  -> Sing n
  -> Sing p
  -> ((m + n) + p) :~: (m + (n + p))
plusAssocZ (SPos SZ) n p =
  start ((SPos SZ %+ n) %+ p)
  === (n %+ p) `because` plusCongruence (SPos SZ %+ n) n p (zeroIdentity n)
  === (SPos SZ %+ (n %+ p)) `because` sym (zeroIdentity (n %+ p))
plusAssocZ m (SPos SZ) p =
  start ((m %+ SPos SZ) %+ p)
  === (m %+ p) `because` plusCongruence (m %+ SPos SZ) m p (zeroIdentityR m)
  === (m %+ (SPos SZ %+ p)) `because` plusCongruenceR m p (SPos SZ %+ p) (sym $ zeroIdentity p)
plusAssocZ m n (SPos SZ) =
  start (m %+ n %+ SPos SZ)
  === (m %+ n) `because` zeroIdentityR (m %+ n)
  === (m %+ (n %+ SPos SZ)) `because` plusCongruenceR m n (n %+ SPos SZ) (sym $ zeroIdentityR n)
plusAssocZ (SPos m) (SPos n) (SPos p) =
  start (SPos m %+ SPos n %+ SPos p)
  === (SPos (m %+ n) %+ SPos p) `because` Refl
  === SPos (m %+ n %+ p) `because` Refl
  === SPos (m %+ (n %+ p)) `because` cong (Proxy @'Pos) (plusAssoc m n p)
  === (SPos m %+ SPos (n %+ p)) `because` Refl
  === (SPos m %+ (SPos n %+ SPos p)) `because` Refl
plusAssocZ (SNeg m) (SNeg n) (SNeg p) =
  start (SNeg m %+ SNeg n %+ SNeg p)
  === SNeg (m %+ n %+ p) `because` Refl
  === SNeg (m %+ (n %+ p)) `because` cong (Proxy @'Neg) (plusAssoc m n p)
  === SNeg m %+ (SNeg n %+ SNeg p) `because` Refl
plusAssocZ (SPos m) (SNeg (SS n)) (SPos p) = undefined
plusAssocZ (SNeg m) (SPos n) (SPos p) = undefined
plusAssocZ (SNeg m) (SNeg n) (SPos p) = undefined
plusAssocZ (SPos m) (SNeg n) (SNeg p) = undefined
plusAssocZ (SPos m) (SPos n) (SNeg p) = undefined
plusAssocZ (SNeg m) (SPos n) (SNeg p) = undefined

-- TODO: finalise this proof

-- Order

data ZLeq (m :: Zahlen) (n :: Zahlen) :: Type where
  NegLeqNeg :: forall m n. IsTrue (m <= n) -> ZLeq (Neg n) (Neg m)
  NegLeqPos :: forall m n. ZLeq (Neg m) (Pos n)
  PosLeqPos :: forall m n. IsTrue (m <= n) -> ZLeq (Pos m) (Pos n)

converseLeq
  :: forall m n. ZLeq (Pos m) (Pos n)
  -> IsTrue (m <= n)
converseLeq (PosLeqPos witness) = witness

leqReflexive
  :: forall (m :: Zahlen) (n :: Zahlen). Sing m
  -> Sing n
  -> m :~: n
  -> ZLeq m n
leqReflexive m n Refl =
  case m of
    SPos n -> PosLeqPos $ leqRefl n
    SNeg n -> NegLeqNeg $ leqRefl n

leqTransZ
  :: forall m n p. Sing m
  -> Sing n
  -> Sing p
  -> ZLeq m n
  -> ZLeq n p
  -> ZLeq m p
leqTransZ m n p NegLeqPos (PosLeqPos witness') = NegLeqPos
leqTransZ m n p (NegLeqNeg witness) NegLeqPos = NegLeqPos
leqTransZ m n p (PosLeqPos witness) (PosLeqPos witness') =
  PosLeqPos witness''
  where
    witness'' = leqTransLemma' m n p updateWitness updateWitness'
    updateWitness = leqNatZ m n witness
    updateWitness' = leqNatZ n p witness'
leqTransZ m n p (NegLeqNeg witness) (NegLeqNeg witness') =
  NegLeqNeg witness''
  where
    witness'' = leqTransLemmaNeg m n p updateWitness updateWitness'
    updateWitness = leqNatZNeg m n witness
    updateWitness' = leqNatZNeg n p witness'

leqNatZ
  :: forall a b. Sing (Pos a)
  -> Sing (Pos b)
  -> IsTrue (Pos a <= Pos b)
  -> IsTrue (a <= b)
leqNatZ sing1 sing2 isTr =
  case isTr of
    Witness -> Witness

leqNatZNeg
  :: forall a b. Sing (Neg a)
  -> Sing (Neg b)
  -> IsTrue (Neg a <= Neg b)
  -> IsTrue (b <= a)
leqNatZNeg sing1 sing2 isTr =
  case isTr of
    Witness -> Witness

leqNatZConv
  :: forall a b. Sing (Pos a)
  -> Sing (Pos b)
  -> IsTrue (a <= b)
  -> IsTrue (Pos a <= Pos b)
leqNatZConv sing1 sing2 isTr =
  case isTr of
    Witness -> Witness

leqNatZConvNeg
  :: forall a b. Sing (Neg a)
  -> Sing (Neg b)
  -> IsTrue (a <= b)
  -> IsTrue (Neg b <= Neg a)
leqNatZConvNeg sing1 sing2 isTr =
  case isTr of
    Witness -> Witness

leqTransLemma'
  :: forall a b c. Sing (Pos a)
  -> Sing (Pos b)
  -> Sing (Pos c)
  -> IsTrue (Pos a <= Pos b)
  -> IsTrue (Pos b <= Pos c)
  -> IsTrue (Pos a <= Pos c)
leqTransLemma' s1 s2 s3 isTr1 isTr2 =
  leqNatZConv s1 s3 $ leqTrans natS1 natS2 natS3 witness witness'
  where
    natS1 = zToNat s1
    natS2 = zToNat s2
    natS3 = zToNat s3
    witness = leqNatZ s1 s2 isTr1
    witness' = leqNatZ s2 s3 isTr2

leqTransLemmaNeg
  :: Sing (Neg a)
  -> Sing (Neg b)
  -> Sing (Neg c)
  -> IsTrue (Neg a <= Neg b)
  -> IsTrue (Neg b <= Neg c)
  -> IsTrue (Neg a <= Neg c)
leqTransLemmaNeg s1 s2 s3 isTr1 isTr2 =
  leqNatZConvNeg s3 s1 $ leqTrans natS3 natS2 natS1 witness' witness
  where
    natS1 = zToNatNeg s1
    natS2 = zToNatNeg s2
    natS3 = zToNatNeg s3
    witness' = leqNatZNeg s2 s3 isTr2
    witness = leqNatZNeg s1 s2 isTr1

antiSymmetry
  :: forall a b. Sing a
  -> Sing b
  -> ZLeq a b
  -> ZLeq b a
  -> a :~: b
antiSymmetry sing1 sing2 (NegLeqNeg witness1) (NegLeqNeg witness2) =
  negLemma $ leqAntisymm (zToNatNeg sing1) (zToNatNeg sing2) witness2 witness1
antiSymmetry sing1 sing2 (PosLeqPos witness1) (PosLeqPos witness2) =
  posLemma $ leqAntisymm (zToNat sing1) (zToNat sing2) witness1 witness2

totality
  :: forall a b. Sing a
  -> Sing b
  -> Either (ZLeq a b) (ZLeq b a)
totality sing1 sing2 =
  case (sing1, sing2) of
    (SNeg n1, SNeg n2) ->
      case n1 %<= n2 of
        STrue -> Right $ NegLeqNeg $ unsafeCoerce Witness
        SFalse -> Left $ NegLeqNeg $ unsafeCoerce Witness
    (SNeg n1, SPos n2) ->
      Left NegLeqPos
    (SPos n1, SNeg n2) ->
      Right NegLeqPos
    (SPos n1, SPos n2) ->
      case n1 %<= n2 of
        STrue -> Left $ PosLeqPos $ unsafeCoerce Witness
        SFalse -> Right $ PosLeqPos $ unsafeCoerce Witness

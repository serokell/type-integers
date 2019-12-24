{-# LANGUAGE AllowAmbiguousTypes #-}
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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Properties where

import Data.Promotion.Prelude.Enum
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable

import Data.Type.Equality           ((:~:) (..))
import Data.Kind                    (Type)

import Lib

import Proof.Propositional

import Data.Type.Natural.Class.Order (leqTrans, leqAntisymm, leqRefl)

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

plusCong
  :: forall (n :: Zahlen) (m :: Zahlen) (p :: Zahlen). n :~: m
  -> n + p :~: m + p
plusCong Refl = Refl

multCong
  :: forall (n :: Zahlen) (m :: Zahlen) (p :: Zahlen). n :~: m
  -> n * p :~: m * p
multCong Refl = Refl

negInv
  :: forall n. Sing n
  -> Inverse (Inverse n) :~: n
negInv sing = undefined

absoluteIdem
  :: forall n. Sing n
  -> Absolute (Absolute n) :~: Absolute n
absoluteIdem sing = undefined

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
    (SNeg n1, SNeg n2) -> undefined
    (SNeg n1, SPos n2) -> Left NegLeqPos
    (SPos n1, SNeg n2) -> Right NegLeqPos
    (SPos n1, SPos n2) -> undefined

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Order where
    
import Data.Kind                     (Type)
import Data.Singletons.TH
import Data.Type.Internal.Integer
import Data.Type.Internal.Nat
import Data.Type.Natural hiding (induction, one, sOne)
import qualified Data.Type.Natural.Class.Arithmetic as A
import qualified Data.Type.Natural.Class.Order as A

import Data.Type.Integer

import Prelude hiding (Integer)

import Proof.Equational
import Proof.Propositional

import Unsafe.Coerce

data ZLeq (m :: Integer) (n :: Integer) :: Type where
  NegLeqNeg :: forall m n. IsTrue (m <= n) -> ZLeq (Neg n) (Neg m)
  NegLeqPos :: forall m n. ZLeq (Neg m) (Pos n)
  PosLeqPos :: forall m n. IsTrue (m <= n) -> ZLeq (Pos m) (Pos n)

leqIdLemma
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> IsTrue (m <= n)
  -> m :~: p
  -> IsTrue (p <= n)
leqIdLemma m n p Witness Refl = Witness

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
leqNatZNeg sing1 sing2 Witness = Witness

converseLeq
  :: forall m n. ZLeq (Pos m) (Pos n)
  -> IsTrue (m <= n)
converseLeq (PosLeqPos witness) = witness

leqReflexiveZ
  :: forall (m :: Integer) (n :: Integer). Sing m
  -> Sing n
  -> m :~: n
  -> ZLeq m n
leqReflexiveZ m n Refl =
  case m of
    SPos n -> PosLeqPos $ A.leqRefl n
    SNeg n -> NegLeqNeg $ A.leqRefl n

leqReflZ
  :: forall (m :: Integer). Sing m
  -> ZLeq m m
leqReflZ m = leqReflexiveZ m m Refl

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

leqNatZConv
  :: forall a b. Sing (Pos a)
  -> Sing (Pos b)
  -> IsTrue (a <= b)
  -> IsTrue (Pos a <= Pos b)
leqNatZConv sing1 sing2 Witness = Witness

leqNatZConvNeg
  :: forall a b. Sing (Neg a)
  -> Sing (Neg b)
  -> IsTrue (a <= b)
  -> IsTrue (Neg b <= Neg a)
leqNatZConvNeg sing1 sing2 Witness = Witness

leqTransLemma'
  :: forall a b c. Sing (Pos a)
  -> Sing (Pos b)
  -> Sing (Pos c)
  -> IsTrue (Pos a <= Pos b)
  -> IsTrue (Pos b <= Pos c)
  -> IsTrue (Pos a <= Pos c)
leqTransLemma' s1 s2 s3 isTr1 isTr2 =
  leqNatZConv s1 s3 $ A.leqTrans natS1 natS2 natS3 witness witness'
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
  leqNatZConvNeg s3 s1 $ A.leqTrans natS3 natS2 natS1 witness' witness
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

subLemmaZero
  :: forall (m :: Nat). Sing m
  -> Sub 'Z m :~: Neg m
subLemmaZero SZ = posNegZeroPostulate
subLemmaZero (SS m) = Refl

subMonoR'
  :: forall (m :: Nat) (n :: Nat). Sing m
  -> Sing n
  -> IsTrue (m <= n)
  -> ZLeq (Sub 'Z n) (Sub 'Z m)
subMonoR' m n Witness = undefined

subMonoR
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> IsTrue (m <= n)
  -> ZLeq (Sub p n) (Sub p m)
subMonoR m n SZ Witness = subMonoR' m n Witness
subMonoR m n (SS p) Witness = undefined

subMono
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> IsTrue (m <= n)
  -> ZLeq (Sub m p) (Sub n p)
subMono m n SZ Witness = PosLeqPos Witness
subMono SZ SZ (SS p) Witness = leqReflZ (SNeg (SS p))
subMono (SS m) (SS n) (SS p) Witness = subMono m n p Witness

subLemmaZ
  :: forall (m :: Nat) (n :: Nat). Sing m
  -> Sing n
  -> ZLeq (Sub m n) (Pos m)
subLemmaZ m SZ =
  leqReflZ (SPos m)
subLemmaZ SZ (SS _) =
  NegLeqPos
subLemmaZ (SS m) (SS n) =
  leqTransZ (sSub m n) (SPos m) (SPos (SS m))
    (subLemmaZ m n) (PosLeqPos $ leqSuccStepR m m $ A.leqRefl m)

subLemmaRight
  :: forall (m :: Nat) (n :: Nat). Sing m
  -> Sing n
  -> ZLeq (Neg m) (Sub n m)
subLemmaRight SZ n = NegLeqPos
subLemmaRight (SS m) SZ = NegLeqNeg (A.leqRefl (SS m))
subLemmaRight (SS m) (SS n) =
  leqTransZ (SNeg (SS m)) (SNeg m) (sSub n m) 
  (NegLeqNeg $ leqSuccStepR m m $ A.leqRefl m) 
  (subLemmaRight m n)

plusMonotoneZ
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> ZLeq m n
  -> ZLeq (m + p) (n + p)
plusMonotoneZ (SPos m) (SPos n) (SPos p) (PosLeqPos witness) =
  PosLeqPos (plusMonotoneL m n p witness)
plusMonotoneZ (SNeg m) (SNeg n) (SNeg p) (NegLeqNeg witness) =
  NegLeqNeg (plusMonotoneL n m p witness)
plusMonotoneZ (SPos m) (SPos n) (SNeg p) (PosLeqPos witness) =
  subMono m n p witness
plusMonotoneZ (SNeg m) (SPos n) (SNeg p) NegLeqPos =
  undefined
plusMonotoneZ (SNeg m) (SPos n) (SPos p) NegLeqPos =
  undefined
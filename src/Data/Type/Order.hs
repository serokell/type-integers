{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Order where
    
import Data.Kind                     (Type)
import Data.Singletons.TH
import Data.Void

import Data.Type.Internal.Integer
import Data.Type.Natural hiding (induction, one, sOne)
import qualified Data.Type.Natural.Class.Order as A

import Data.Type.Integer

import Prelude hiding (Integer)

-- import Proof.Equational
import Proof.Propositional

import Unsafe.Coerce

data ZLeq (m :: Integer) (n :: Integer) :: Type where
  NegLeqNeg :: forall m n. IsTrue (m <= n) -> ZLeq ('Neg n) ('Neg m)
  NegLeqPos :: forall m n. ZLeq ('Neg m) ('Pos n)
  PosLeqPos :: forall m n. IsTrue (m <= n) -> ZLeq ('Pos m) ('Pos n)

posNegAbsurd
  :: forall (m :: Nat) (n :: Nat).
  ZLeq ('Pos m) ('Neg n) -> Void
posNegAbsurd = \case { }

leqIdLemma
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> IsTrue (m <= n)
  -> m :~: p
  -> IsTrue (p <= n)
leqIdLemma _ _ _ Witness Refl = Witness

leqNatZ
  :: forall a b. Sing ('Pos a)
  -> Sing ('Pos b)
  -> IsTrue ('Pos a <= 'Pos b)
  -> IsTrue (a <= b)
leqNatZ _ _ Witness = Witness

leqNatZNeg
  :: forall a b. Sing ('Neg a)
  -> Sing ('Neg b)
  -> IsTrue ('Neg a <= 'Neg b)
  -> IsTrue (b <= a)
leqNatZNeg _ _ Witness = Witness

converseLeq
  :: forall m n. ZLeq ('Pos m) ('Pos n)
  -> IsTrue (m <= n)
converseLeq (PosLeqPos witness) = witness

leqReflexiveZ
  :: forall (m :: Integer) (n :: Integer). Sing m
  -> Sing n
  -> m :~: n
  -> ZLeq m n
leqReflexiveZ m _ Refl =
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
leqTransZ _ _ _ NegLeqPos (PosLeqPos _) = NegLeqPos
leqTransZ _ _ _ (NegLeqNeg _) NegLeqPos = NegLeqPos
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
  :: forall a b. Sing ('Pos a)
  -> Sing ('Pos b)
  -> IsTrue (a <= b)
  -> IsTrue ('Pos a <= 'Pos b)
leqNatZConv _ _ Witness = Witness

leqNatZConvNeg
  :: forall a b. Sing ('Neg a)
  -> Sing ('Neg b)
  -> IsTrue (a <= b)
  -> IsTrue ('Neg b <= 'Neg a)
leqNatZConvNeg _ _ Witness = Witness

leqTransLemma'
  :: forall a b c. Sing ('Pos a)
  -> Sing ('Pos b)
  -> Sing ('Pos c)
  -> IsTrue ('Pos a <= 'Pos b)
  -> IsTrue ('Pos b <= 'Pos c)
  -> IsTrue ('Pos a <= 'Pos c)
leqTransLemma' s1 s2 s3 isTr1 isTr2 =
  leqNatZConv s1 s3 $ A.leqTrans natS1 natS2 natS3 witness witness'
  where
    natS1 = zToNat s1
    natS2 = zToNat s2
    natS3 = zToNat s3
    witness = leqNatZ s1 s2 isTr1
    witness' = leqNatZ s2 s3 isTr2

leqTransLemmaNeg
  :: Sing ('Neg a)
  -> Sing ('Neg b)
  -> Sing ('Neg c)
  -> IsTrue ('Neg a <= 'Neg b)
  -> IsTrue ('Neg b <= 'Neg c)
  -> IsTrue ('Neg a <= 'Neg c)
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
antiSymmetry _ _ NegLeqPos p = (absurd . posNegAbsurd) p

totality
  :: forall a b. Sing a
  -> Sing b
  -> Either (ZLeq a b) (ZLeq b a)
totality sing1 sing2 =
  case (sing1, sing2) of
    (SNeg n, SNeg m) ->
      case n %<= m of
        STrue -> Right $ NegLeqNeg $ unsafeCoerce Witness
        SFalse -> Left $ NegLeqNeg $ unsafeCoerce Witness
    (SNeg _, SPos _) ->
      Left NegLeqPos
    (SPos _, SNeg _) ->
      Right NegLeqPos
    (SPos n, SPos m) ->
      case n %<= m of
        STrue -> Left $ PosLeqPos $ unsafeCoerce Witness
        SFalse -> Right $ PosLeqPos $ unsafeCoerce Witness

subLemmaZero
  :: forall (m :: Nat). Sing m
  -> Sub 'Z m :~: 'Neg m
subLemmaZero SZ = posNegZeroPostulate
subLemmaZero (SS _) = Refl

subMonoR'
  :: forall (m :: Nat) (n :: Nat). Sing m
  -> Sing n
  -> IsTrue (m <= n)
  -> ZLeq (Sub 'Z n) (Sub 'Z m)
subMonoR' _ _ Witness = undefined

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
subMono _ _ SZ Witness = 
  PosLeqPos Witness
subMono SZ SZ (SS p) Witness = 
  leqReflZ (SNeg (SS p))
subMono (SS m) (SS n) (SS p) Witness = 
  subMono m n p Witness
subMono SZ n'@(SS n) p'@(SS p) Witness =
  case sSub n' p' of
    (SPos _) -> NegLeqPos
    (SNeg _) -> undefined
subMono m@(SS _) SZ (SS _) w = 
  absurd $ succLeqZeroAbsurd m w

subLemmaZ
  :: forall (m :: Nat) (n :: Nat). Sing m
  -> Sing n
  -> ZLeq (Sub m n) ('Pos m)
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
  -> ZLeq ('Neg m) (Sub n m)
subLemmaRight SZ _ = NegLeqPos
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
plusMonotoneZ m'@(SNeg m) n'@(SPos n) p'@(SNeg p) NegLeqPos =
  case (m' %+ p', n' %+ p') of
    (SNeg q, SNeg s) -> NegLeqNeg _
    (SNeg _, SPos _) -> NegLeqPos
plusMonotoneZ m'@(SNeg m) n'@(SPos n) p'@(SPos p) NegLeqPos =
  case (m' %+ p', n' %+ p') of
    (SPos _, _) -> PosLeqPos _
    (SNeg _, SPos _) -> NegLeqPos
plusMonotoneZ (SPos m) (SNeg n) _ p = absurd $ posNegAbsurd p
plusMonotoneZ (SNeg m) (SNeg n) (SPos p) (NegLeqNeg Witness) = undefined
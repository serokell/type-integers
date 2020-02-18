{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

posNegZeroPostulate
  :: Pos Z :~: Neg Z
posNegZeroPostulate = unsafeCoerce Refl

cong2
  :: forall f a a' b b'. Proxy f
  -> a :~: a'
  -> b :~: b'
  -> f a b :~: f a' b'
cong2 _ Refl Refl = Refl

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
zeroIdentity (SNeg SZ) = posNegZeroPostulate
zeroIdentity (SNeg (SS n)) = Refl

zeroIdentityR
  :: forall (m :: Zahlen). Sing m
  -> m + Pos Z :~: m
zeroIdentityR (SPos SZ) = 
  start (SPos SZ %+ SPos SZ)
  === SPos (SZ %+ SZ) `because` Refl
  === SPos SZ `because` Refl
zeroIdentityR (SPos (SS n)) =
  plusCong' (SS n) SZ (SS n) (plusZeroR (SS n))
zeroIdentityR (SNeg SZ) = posNegZeroPostulate
zeroIdentityR (SNeg (SS n)) = Refl

zeroIdentityRNeg
  :: forall (m :: Zahlen). Sing m
  -> m + Neg Z :~: m
zeroIdentityRNeg m = 
  trans (plusCongruenceR m (SNeg SZ) (SPos SZ) (sym posNegZeroPostulate)) (zeroIdentityR m)

subLemma
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> n :~: p
  -> Sub m n :~: Sub m p
subLemma m n p Refl = Refl

subLemma'
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> m :~: n
  -> Sub m p :~: Sub n p
subLemma' m n p Refl = Refl

commZ
  :: forall (m :: Zahlen) (n :: Zahlen). Sing m
  -> Sing n
  -> m + n :~: n + m
commZ (SPos m) (SPos n) =
  start (SPos m %+ SPos n)
  === SPos (m %+ n) `because` Refl
  === SPos (n %+ m) `because` cong (Proxy @'Pos) (plusComm m n)
  === SPos n %+ SPos m `because` Refl
commZ (SNeg m) (SNeg n) =
  start (SNeg m %+ SNeg n)
  === SNeg (m %+ n) `because` Refl
  === SNeg (n %+ m) `because` cong (Proxy @'Neg) (plusComm m n)
  === SNeg n %+ SNeg m `because` Refl
commZ (SPos m) (SNeg n) = Refl
commZ (SNeg m) (SPos n) = Refl

distrSub
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> (Sub m n + Pos p) :~: Sub (m + p) n
distrSub _ SZ SZ = Refl
distrSub _ SZ (SS p) = Refl
distrSub m (SS n) SZ = 
  start (sSub m (SS n) %+ SPos SZ)
  === sSub m (SS n) `because` zeroIdentityR (sSub m (SS n))
  === sSub (m %+ SZ) (SS n) `because` subLemma' m (m %+ SZ) (SS n) (sym (plusZeroR m))
distrSub m (SS n) (SS p) = distrSub m (SS n) (SS p)

distrSubLNeg
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Sub m n + Neg p :~: Sub m (n + p)
distrSubLNeg _ SZ SZ = Refl
distrSubLNeg _ SZ (SS _) = Refl
distrSubLNeg m (SS n) SZ =
  start (sSub m (SS n) %+ SNeg SZ)
  === sSub m (SS n) `because` zeroIdentityRNeg (sSub m (SS n))
  === sSub m ((SS n) %+ SZ) `because` subLemma m (SS n) (SS n %+ SZ) (sym $ plusZeroR (SS n))
distrSubLNeg (SS m) (SS n) (SS p) = unsafeCoerce $ distrSubLNeg m n p

distrNeg
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Neg m + Sub n p :~: Sub n (m + p)
distrNeg m n p =
  start (SNeg m %+ sSub n p)
  === (sSub n p %+ SNeg m) `because` commZ (SNeg m) (sSub n p)
  === sSub n (p %+  m) `because` distrSubLNeg n p m
  === sSub n (m %+ p) `because` subLemma n (p %+ m) (m %+ p) (plusComm p m)

distrSubL
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Sub m n + Pos p :~: Sub (m + p) n
distrSubL _ SZ SZ = Refl
distrSubL _ SZ (SS _) = Refl
distrSubL m (SS n) SZ =
  start (sSub m (SS n) %+ SPos SZ)
  === sSub m (SS n) `because` zeroIdentityR (sSub m (SS n))
  === sSub (m %+ SZ) (SS n) `because` subLemma' m (m %+ SZ) (SS n) (sym (plusZeroR m))
distrSubL m (SS n) (SS p) = unsafeCoerce $ distrSubL m n p


distrSubR
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Pos m + Sub n p :~: Sub (m + n) p
distrSubR m n p =
  start (SPos m %+ sSub n p)
  === sSub n p %+ SPos m `because` commZ (SPos m) (sSub n p)
  === sSub (n %+ m) p `because` distrSubL n p m
  === sSub (m %+ n) p `because` subLemma' (n %+ m) (m %+ n) p (plusComm n m)

plusAssocZ
  :: forall (m :: Zahlen) (n :: Zahlen) (p :: Zahlen). Sing m
  -> Sing n
  -> Sing p
  -> ((m + n) + p) :~: (m + (n + p))
plusAssocZ (SPos SZ) n p =
  start ((SPos SZ %+ n) %+ p)
  === (n %+ p) `because`
    plusCongruence (SPos SZ %+ n) n p (zeroIdentity n)
  === (SPos SZ %+ (n %+ p)) `because` sym (zeroIdentity (n %+ p))
plusAssocZ m (SPos SZ) p =
  start ((m %+ SPos SZ) %+ p)
  === (m %+ p) `because`
    plusCongruence (m %+ SPos SZ) m p (zeroIdentityR m)
  === (m %+ (SPos SZ %+ p)) `because`
    plusCongruenceR m p (SPos SZ %+ p) (sym $ zeroIdentity p)
plusAssocZ m n (SPos SZ) =
  start (m %+ n %+ SPos SZ)
  === (m %+ n) `because` zeroIdentityR (m %+ n)
  === (m %+ (n %+ SPos SZ)) `because`
    plusCongruenceR m n (n %+ SPos SZ) (sym $ zeroIdentityR n)
plusAssocZ (SPos m) (SPos n) (SPos p) =
  start (SPos m %+ SPos n %+ SPos p)
  === (SPos (m %+ n) %+ SPos p) `because` Refl
  === SPos (m %+ n %+ p) `because` Refl
  === SPos (m %+ (n %+ p)) `because`
    cong (Proxy @'Pos) (plusAssoc m n p)
  === (SPos m %+ SPos (n %+ p)) `because` Refl
  === (SPos m %+ (SPos n %+ SPos p)) `because` Refl
plusAssocZ (SNeg m) (SNeg n) (SNeg p) =
  start (SNeg m %+ SNeg n %+ SNeg p)
  === SNeg (m %+ n %+ p) `because` Refl
  === SNeg (m %+ (n %+ p)) `because`
    cong (Proxy @'Neg) (plusAssoc m n p)
  === SNeg m %+ (SNeg n %+ SNeg p) `because` Refl
plusAssocZ (SPos m) (SNeg n) (SPos p) =
  start (SPos m %+ SNeg n %+ SPos p)
  === (sSub m n %+ SPos p) `because` Refl
  === sSub (m %+ p) n `because` distrSubL m n p
  === SPos m %+ sSub p n `because` sym (distrSubR m p n)
  === SPos m %+ (SNeg n %+ SPos p) `because` Refl
plusAssocZ (SNeg m) (SPos n) (SPos p) =
  start (SNeg m %+ SPos n %+ SPos p)
  === sSub n m %+ SPos p `because` Refl
  === sSub (n %+ p) m `because` distrSubL n m p
  === (SNeg m %+ (SPos n %+ SPos p)) `because` Refl
plusAssocZ (SNeg m) (SNeg n) (SPos p) =
  start (SNeg m %+ SNeg n %+ SPos p)
  === SNeg (m %+ n) %+ SPos p `because` Refl
  === sSub p (m %+ n) `because` Refl
  === (SNeg m %+ sSub p n) `because` sym (distrNeg m p n)
plusAssocZ (SPos m) (SNeg n) (SNeg p) =
  start (SPos m %+ SNeg n %+ SNeg p)
  === (sSub m n %+ SNeg p) `because` undefined
  === (sSub m (n %+ p)) `because` distrSubLNeg m n p
  === SPos m %+ SNeg (n %+ p) `because` Refl
  === SPos m %+ (SNeg n %+ SNeg p) `because` Refl
plusAssocZ (SPos m) (SPos n) (SNeg p) =
  start (SPos m %+ SPos n %+ SNeg p)
  === SPos (m %+ n) %+ SNeg p `because` Refl
  === sSub (m %+ n) p `because` Refl
  === SPos m %+ sSub n p `because` sym (distrSubR m n p)
  === SPos m %+ (SPos n %+ SNeg p) `because` Refl
plusAssocZ (SNeg m) (SPos n) (SNeg p) =
  start (SNeg m %+ SPos n %+ SNeg p)
  === (sSub n m %+ SNeg p) `because` Refl
  === sSub n (m %+ p) `because` distrSubLNeg n m p
  === SNeg m %+ sSub n p `because` sym (distrNeg m n p)
  === SNeg m %+ (SPos n %+ SNeg p) `because` Refl

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
leqNatZNeg sing1 sing2 Witness = Witness

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

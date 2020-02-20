{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
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

import Data.Type.Equality           ((:~:) (..), sym)
import Data.Type.Natural as A hiding (induction, plusAssoc)
import Data.Type.Natural.Class.Arithmetic hiding (induction, plusAssoc)
import Data.Type.Natural.Class.Order (leqTrans, leqAntisymm, leqRefl)
import Data.Kind                    (Type)

import Proof.Propositional
import Proof.Equational ((===), because, cong, start, withRefl)

import Unsafe.Coerce

import Lib

import Nat

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
  -> (Pos Z) + m :~: m
zeroIdentity (SPos n) = Refl
zeroIdentity (SNeg SZ) = unsafeCoerce Refl
zeroIdentity (SNeg (SS n)) = Refl

zeroIdentityR
  :: forall (m :: Zahlen). Sing m
  -> m + (Pos Z) :~: m
zeroIdentityR (SPos SZ) = Refl
zeroIdentityR (SPos (SS n)) =
  plusCong' (SS n) SZ (SS n) (plusZeroR (SS n))
zeroIdentityR (SNeg SZ) = unsafeCoerce Refl
zeroIdentityR (SNeg (SS n)) = Refl

plusAssoc
  :: forall (m :: Zahlen) (n :: Zahlen) (p :: Zahlen). Sing m
  -> Sing n
  -> Sing p
  -> m + n + p :~: m + (n + p)
plusAssoc (SPos SZ) (SPos SZ) (SPos SZ) = Refl
plusAssoc (SPos SZ) (SPos (SS n)) (SPos SZ) = Refl
plusAssoc (SPos SZ) (SPos (SS n)) (SPos (SS p)) = Refl
plusAssoc (SPos (SS n)) (SPos SZ) (SPos SZ) = undefined
plusAssoc m n p = undefined
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

subMinus 
  :: forall (a :: Nat) (b :: Nat). ((a <= b) ~ 'True) => Sing a 
  -> Sing b  
  -> Sub a b :~: ('Neg (b - a))
subMinus SZ SZ = unsafeCoerce Refl
subMinus SZ (SS n) = Refl
subMinus (SS n) (SS m) = subMinus n m

subMinus2 
  :: forall (a :: Nat) (b :: Nat). IsTrue (b <= a) -> Sing a 
  -> Sing b  
  -> Sub a b :~: ('Pos (a - b))
subMinus2 Witness SZ SZ = Refl
subMinus2 Witness (SS n) SZ = Refl
subMinus2 Witness (SS n) (SS m) = subMinus2 Witness n m

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

class IsCommutativeRing z where
  type Zero' :: z
  type One' :: z
  type Inv (m :: z) :: z

  oneIsNotZero :: One' :~: Zero' -> Void
  associativity
    :: Sing (x :: z)
    -> Sing y
    -> Sing n
    -> (x + y) + n :~: x + (y + n)
  commutativity
    :: forall (x :: z) (y :: z). Sing x
    -> Sing y
    -> x + y :~: y + x
  multRightDistrib
    :: forall (x :: z) (y :: z) (u :: z). Sing x
    -> Sing y
    -> Sing u
    -> (x * (y + u)) :~: ((x * y) + (x * u))
  zeroNeutral
    :: forall (x :: z). Sing x
    -> Zero' + x :~: x
  oneNeutral
    :: forall x. Sing x
    -> x * One' :~: x
  inverseAxiom
    :: forall x. Sing x
    -> (x + Inv x) :~: Zero'

instance IsCommutativeRing Zahlen where
  type Zero' = ('Pos 'Z)
  type One' = ('Pos (S Z))
  type Inv m = Inverse m

  oneIsNotZero = \case {}

  associativity = plusAssoc

  commutativity (SPos n) (SPos m) = cong (Proxy @'Pos) (plusComm n m)
  commutativity (SNeg n) (SNeg m) = cong (Proxy @'Neg) (plusComm n m)
  commutativity (SNeg n) (SPos m) = Refl 
  commutativity (SPos n) (SNeg m) = Refl

  multRightDistrib (SPos l) (SPos m) (SPos n) = cong (Proxy @'Pos) (A.multPlusDistrib l m n)
  multRightDistrib (SNeg l) (SNeg m) (SNeg n) = cong (Proxy @'Pos) (A.multPlusDistrib l m n)
  multRightDistrib (SNeg l) (SPos m) (SPos n) = cong (Proxy @'Neg) (A.multPlusDistrib l m n)
  multRightDistrib (SPos l) (SNeg m) (SNeg n) = cong (Proxy @'Neg) (A.multPlusDistrib l m n)
  multRightDistrib sl@(SPos l) sm@(SNeg m) sn@(SPos n) = case (n %<= m) of 
    (STrue) -> start (sl %* (sm %+ sn)) 
                === (sl %* (n `sSub` m)) `because` Refl 
                === (sl %* (SNeg (m %- n))) `because` multCongR sl (subMinus n m)
                === (SNeg ((l %* (m %- n)))) `because` Refl
                === (SNeg ((l %* m) %- (l %* n))) `because` cong (Proxy @'Neg) (multMinusDistrib m n l)
                === ((l %* n) `sSub` (l %* m)) `because` (sym (withRefl (multLeq Witness l n m) $ subMinus (l %* n) (l %* m)))
                === ((SNeg $ l %* m) %+ (SPos $ l %* n)) `because` Refl
                === (((SPos l) %* (SNeg m)) %+ ((SPos l) %* (SPos n))) `because` Refl
    (SFalse) ->   start (sl %* (sm %+ sn)) 
                  === (sl %* (n `sSub` m)) `because` Refl
                  === (sl %* (SPos (n %- m))) `because` multCongR sl (subMinus2 (notLeqToLeq n m) n m)
                  === (SPos ((l %* (n %- m)))) `because` Refl
                  === (SPos ((l %* n) %- (l %* m))) `because` cong (Proxy @'Pos) (withWitness (notLeqToLeq n m) $ multMinusDistrib n m l)
                  === ((l %* n) `sSub` (l %* m)) `because` (sym $ subMinus2 (reflToWitness $ multLeq (notLeqToLeq n m) l m n) (l %* n) (l %* m))
                  === ((sl %* sm) %+ (sl %* sn)) `because` Refl
  multRightDistrib sl@(SNeg l) sm@(SNeg m) sn@(SPos n) = case (n %<= m) of 
    (STrue) -> start (sl %* (sm %+ sn)) 
                === (sl %* (n `sSub` m)) `because` Refl 
                === (sl %* (SNeg (m %- n))) `because` multCongR sl (subMinus n m)
                === (SPos ((l %* (m %- n)))) `because` Refl
                === (SPos ((l %* m) %- (l %* n))) `because` cong (Proxy @'Pos) (multMinusDistrib m n l)
                === ((l %* m) `sSub` (l %* n)) `because` (sym $ subMinus2 (reflToWitness $ multLeq Witness l n m) (l %* m) (l %* n))
                === ((SPos $ l %* m) %+ (SNeg $ l %* n)) `because` Refl
                === (((SNeg l) %* (SNeg m)) %+ ((SNeg l) %* (SPos n))) `because` Refl
    (SFalse) ->   start (sl %* (sm %+ sn)) 
                  === (sl %* (n `sSub` m)) `because` Refl
                  === (sl %* (SPos (n %- m))) `because` multCongR sl (subMinus2 (notLeqToLeq n m) n m)
                  === (SNeg ((l %* (n %- m)))) `because` Refl
                  === (SNeg ((l %* n) %- (l %* m))) `because` cong (Proxy @'Neg) (withWitness (notLeqToLeq n m) $ multMinusDistrib n m l)
                  === ((l %* m) `sSub` (l %* n)) `because` (sym $ withRefl (multLeq (notLeqToLeq n m) l m n) $ subMinus (l %* m) (l %* n))
                  === ((sl %* sm) %+ (sl %* sn)) `because` Refl
  multRightDistrib sl sm@(SPos m) sn@(SNeg n) = 
    start (sl %* (sm %+ sn)) 
      === (sl %* (sn %+ sm)) `because` multCongR sl (commutativity sm sn)
      === ((sl %* sn) %+ (sl %* sm)) `because` multRightDistrib sl sn sm 
      === ((sl %* sm) %+ (sl %* sn)) `because` commutativity (sl %* sn) (sl %* sm)


class IsCommutativeRing z => IsInteger z where
  type Signum (m :: z) :: Sign
  type Absolute'' (m :: z) :: Nat

  zeroEquality :: (Absolute'' x ~ Absolute'' y, Absolute'' x ~ 'Z) => x :~: y
  zeroEquality = unsafeCoerce Refl
  zeroEquality' :: Absolute'' x :~: Absolute'' y -> Absolute'' x :~: 'Z -> x :~: y
  zeroEquality' Refl Refl = unsafeCoerce Refl

  induction  :: forall k p. p Zero'
             -> (forall (n :: z). ((Zero' <= n) ~ 'True) => Sing n -> p n -> p (One' + n))
             -> (forall (n :: z). ((Zero' <= n) ~ 'True) => Sing (Inv n) -> p n -> p (Inv n))
             -> Sing k -> p k

instance IsInteger Zahlen where
  type Signum ('Pos n) = P
  type Signum ('Neg n) = N
  type Absolute'' (_ n) = n

  induction base _ _ (SPos SZ) = base
  induction base step neg (SPos (SS n)) = step (SPos n) $ induction base step neg (SPos n)
  induction base step neg sn@(SNeg n) = neg sn $ induction base step neg (SPos n)
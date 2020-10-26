{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NoStarIsType        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Zahlen.Class.Order
       ( leqReflexive, leqTrans, leqPosZNat, leqNegZNat, leqNatPosZ, leqNatNegZ
       , antiSymmetry, totality
       ) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:) (..))
import Data.Typeable
import Unsafe.Coerce

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import qualified Data.Type.Natural as Nat
import qualified Data.Type.Natural.Class.Arithmetic as Nat
import qualified Data.Type.Natural.Class.Order as Nat
import Proof.Propositional

-- TODO: Remove comment
--import Data.Type.Zahlen.Class.Arithmetic (negLemma, posLemma)
import Data.Type.Zahlen.Definitions

-- Order

-- TODO: Remove comment
--data ZLeq (m :: Zahlen) (n :: Zahlen) :: Type where
--  NegLeqNeg :: forall m n. IsTrue (m <= n) -> ZLeq (Neg n) (Neg m)
--  NegLeqPos :: forall m n. ZLeq (Neg m) (Pos n)
--  PosLeqPos :: forall m n. IsTrue (m <= n) -> ZLeq (Pos m) (Pos n)
--
--converseLeq
--  :: forall m n. ZLeq (Pos m) (Pos n)
--  -> IsTrue (m <= n)
--converseLeq (PosLeqPos witness) = undefined

leqReflexive :: Sing (m :: Zahlen)
             -> Sing (n :: Zahlen)
             -> m :~: n
             -> IsTrue (m <= n)
leqReflexive = undefined

--leqReflexive
--  :: forall (m :: Zahlen) (n :: Zahlen). Sing m
--  -> Sing n
--  -> m :~: n
--  -> ZLeq m n
--leqReflexive m n Refl =
--  case m of
--    SPos n -> PosLeqPos $ leqRefl n
--    SNeg n -> NegLeqNeg $ leqRefl n

leqTrans :: Sing (m :: Zahlen)
         -> Sing (n :: Zahlen)
         -> Sing (p :: Zahlen)
         -> IsTrue (m <= n)
         -> IsTrue (n <= p)
         -> IsTrue (m <= p)
leqTrans = undefined

--leqTransZ
--  :: forall m n p. Sing m
--  -> Sing n
--  -> Sing p
--  -> ZLeq m n
--  -> ZLeq n p
--  -> ZLeq m p
--leqTransZ m n p NegLeqPos (PosLeqPos witness') = NegLeqPos
--leqTransZ m n p (NegLeqNeg witness) NegLeqPos = NegLeqPos
--leqTransZ m n p (PosLeqPos witness) (PosLeqPos witness') =
--  PosLeqPos witness''
--  where
--    witness'' = leqTransLemma' m n p updateWitness updateWitness'
--    updateWitness = leqNatZ m n witness
--    updateWitness' = leqNatZ n p witness'
--leqTransZ m n p (NegLeqNeg witness) (NegLeqNeg witness') =
--  NegLeqNeg witness''
--  where
--    witness'' = leqTransLemmaNeg m n p updateWitness updateWitness'
--    updateWitness = leqNatZNeg m n witness
--    updateWitness' = leqNatZNeg n p witness'
--
--leqNatZ
--  :: forall a b. Sing (Pos a)
--  -> Sing (Pos b)
--  -> IsTrue (Pos a <= Pos b)
--  -> IsTrue (a <= b)
--leqNatZ sing1 sing2 isTr =
--  case isTr of
--    Witness -> Witness

leqPosZNat :: Sing (Pos a :: Zahlen)
       -> Sing (Pos b :: Zahlen)
       -> IsTrue (Pos a <= Pos b)
       -> IsTrue (a <= b)
leqPosZNat = undefined

leqNegZNat :: Sing (Neg1 a :: Zahlen)
       -> Sing (Neg1 b :: Zahlen)
       -> IsTrue (Neg1 a <= Neg1 b)
       -> IsTrue (b <= a)
leqNegZNat = undefined

--leqNatZNeg
--  :: forall a b. Sing (Neg a)
--  -> Sing (Neg b)
--  -> IsTrue (Neg a <= Neg b)
--  -> IsTrue (b <= a)
--leqNatZNeg sing1 sing2 isTr =
--  case isTr of
--    Witness -> Witness
--
leqNatPosZ :: Sing (Pos a :: Zahlen)
           -> Sing (Pos b :: Zahlen)
           -> IsTrue (a <= b)
           -> IsTrue (Pos a <= Pos b)
leqNatPosZ = undefined
--leqNatZConv
--  :: forall a b. Sing (Pos a)
--  -> Sing (Pos b)
--  -> IsTrue (a <= b)
--  -> IsTrue (Pos a <= Pos b)
--leqNatZConv sing1 sing2 isTr =
--  case isTr of
--    Witness -> Witness

leqNatNegZ :: Sing (Neg1 a :: Zahlen)
           -> Sing (Neg1 b :: Zahlen)
           -> IsTrue (a <= b)
           -> IsTrue (Neg1 b <= Neg1 a)
leqNatNegZ = undefined

--leqNatZConvNeg
--  :: forall a b. Sing (Neg a)
--  -> Sing (Neg b)
--  -> IsTrue (a <= b)
--  -> IsTrue (Neg b <= Neg a)
--leqNatZConvNeg sing1 sing2 isTr =
--  case isTr of
--    Witness -> Witness
--
--leqTransLemma'
--  :: forall a b c. Sing (Pos a)
--  -> Sing (Pos b)
--  -> Sing (Pos c)
--  -> IsTrue (Pos a <= Pos b)
--  -> IsTrue (Pos b <= Pos c)
--  -> IsTrue (Pos a <= Pos c)
--leqTransLemma' s1 s2 s3 isTr1 isTr2 =
--  leqNatZConv s1 s3 $ leqTrans natS1 natS2 natS3 witness witness'
--  where
--    natS1 = zToNat s1
--    natS2 = zToNat s2
--    natS3 = zToNat s3
--    witness = leqNatZ s1 s2 isTr1
--    witness' = leqNatZ s2 s3 isTr2
--
--leqTransLemmaNeg
--  :: Sing (Neg a)
--  -> Sing (Neg b)
--  -> Sing (Neg c)
--  -> IsTrue (Neg a <= Neg b)
--  -> IsTrue (Neg b <= Neg c)
--  -> IsTrue (Neg a <= Neg c)
--leqTransLemmaNeg s1 s2 s3 isTr1 isTr2 =
--  leqNatZConvNeg s3 s1 $ leqTrans natS3 natS2 natS1 witness' witness
--  where
--    natS1 = zToNatNeg s1
--    natS2 = zToNatNeg s2
--    natS3 = zToNatNeg s3
--    witness' = leqNatZNeg s2 s3 isTr2
--    witness = leqNatZNeg s1 s2 isTr1

antiSymmetry :: Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> IsTrue (a <= b)
             -> IsTrue (b <= a)
             -> a :~: b
antiSymmetry = undefined

--antiSymmetry
--  :: forall a b. Sing a
--  -> Sing b
--  -> ZLeq a b
--  -> ZLeq b a
--  -> a :~: b
--antiSymmetry sing1 sing2 (NegLeqNeg witness1) (NegLeqNeg witness2) =
--  negLemma $ leqAntisymm (zToNatNeg sing1) (zToNatNeg sing2) witness2 witness1
--antiSymmetry sing1 sing2 (PosLeqPos witness1) (PosLeqPos witness2) =
--  posLemma $ leqAntisymm (zToNat sing1) (zToNat sing2) witness1 witness2

totality :: Sing (a :: Zahlen)
         -> Sing (b :: Zahlen)
         -> Either (IsTrue (a <= b)) (IsTrue (b <= a))
totality = undefined

--totality
--  :: forall a b. Sing a
--  -> Sing b
--  -> Either (ZLeq a b) (ZLeq b a)
--totality sing1 sing2 =
--  case (sing1, sing2) of
--    (SNeg n1, SNeg n2) ->
--      case n1 %<= n2 of
--        STrue  -> Right $ NegLeqNeg $ unsafeCoerce Witness
--        SFalse -> Left $ NegLeqNeg $ unsafeCoerce Witness
--    (SNeg n1, SPos n2) ->
--      Left NegLeqPos
--    (SPos n1, SNeg n2) ->
--      Right NegLeqPos
--    (SPos n1, SPos n2) ->
--      case n1 %<= n2 of
--        STrue  -> Left $ PosLeqPos $ unsafeCoerce Witness
--        SFalse -> Right $ PosLeqPos $ unsafeCoerce Witness
-- end TODO

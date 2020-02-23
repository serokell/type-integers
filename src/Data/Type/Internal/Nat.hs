{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -fplugin Data.Singletons.TypeNats.Presburger #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase#-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Data.Type.Internal.Nat where

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable

import Data.Type.Equality           ((:~:) (..), sym)
import Data.Type.Natural as A hiding (induction, plusAssoc)
import Data.Type.Natural.Class.Arithmetic hiding (plusAssoc)
import Data.Type.Natural.Class.Order (leqTrans, leqAntisymm, leqRefl, minusSucc, sLeqCong)
import Data.Kind                    (Type)

import Proof.Propositional
import Proof.Equational ((===), (=~=), because, cong, start, withRefl)

import Unsafe.Coerce

newtype MinusMultDistrib (n :: Nat) =
  MinusMultDistrib { minusMultDistribProof :: forall m l. (m <= n) ~ 'True => Sing m -> Sing l
                                         -> l * (n - m) :~: (l * n) - (l * m)
                   }

zeroMinus :: Sing n -> 'Z - n :~: 'Z
zeroMinus SZ = Refl
zeroMinus (SS n) = Refl

multMinusDistrib :: forall n m l. (m <= n) ~ 'True => Sing (n :: Nat) -> Sing m -> Sing (l :: Nat)
                -> l * (n - m) :~: (l * n) - (l * m)
multMinusDistrib sn0 = minusMultDistribProof $ induction base step sn0
    where
      base :: MinusMultDistrib 'Z
      base = MinusMultDistrib $ \sm sl ->
        start (sl %* (SZ %- sm))
          === (sl %* SZ) `because` multCongR sl (zeroMinus sm)
          === SZ `because` multZeroR sl
          === (SZ %- (sl %* sm)) `because` (sym $ zeroMinus (sl %* sm))
          === ((sl %* SZ) %- (sl %* sm))`because` minusCongL (sym $ multZeroR sl) (sl %* sm)

      step :: forall n1. Sing n1 -> MinusMultDistrib n1 -> MinusMultDistrib (S n1)
      step sn (MinusMultDistrib ih) = MinusMultDistrib $ \sm sl -> case (sm %<= sn) of
        STrue ->
          start (sl %* ((SS sn) %- sm))
            === (sl %* (SS (sn %- sm))) `because` multCongR sl (minusSucc sn sm Witness)
            === (sl %* (sn %- sm) %+ sl) `because` multSuccR sl (sn %- sm)
            === (((sl %* sn) %- (sl %* sm)) %+ sl) `because` plusCongL (ih sm sl) sl
            === (sl %+ ((sl %* sn) %- (sl %* sm))) `because` plusComm ((sl %* sn) %- (sl %* sm)) sl
            === ((sl %+ (sl %* sn)) %- (sl %* sm)) `because` undefined -- to do - prove n + (a - b) == (n + a) - b)
            === (((sl %* sn) %+ sl) %- (sl %* sm)) `because` minusCongL (plusComm sl (sl %* sn)) (sl %* sm)
            === ((sl %* (SS sn)) %- (sl %* sm)) `because` minusCongL (sym $ multSuccR sl sn) (sl %* sm)
        SFalse ->
          start (sl %* ((SS sn) %- sm))
            === (sl %* ((SS sn) %- (SS sn))) `because` multCongR sl (minusCongR (SS sn) (eq1 sm sn))
            === (sl %* SZ) `because` multCongR sl (minusNilpotent (SS sn))
            === SZ `because` multZeroR sl
            === (SZ %+ (sl %* (SS sn))) %- (sl %* (SS sn)) `because` (sym $ plusMinus SZ (sl %* (SS sn)))
            === ((sl %* (SS sn)) %- (sl %* (SS sn))) `because` minusCongL (plusZeroL (sl %* (SS sn))) (sl %* (SS sn))
            === ((sl %* (SS sn)) %- (sl %* sm)) `because` minusCongR (sl %* (SS sn)) (multCongR sl (sym $ eq1 sm sn))

eq1 ::forall m n. ((m <= n) ~ False, (m <= S n) ~ True) => Sing m -> Sing (n :: Nat) -> m :~: S n
eq1 sm sn = case (sCompare sm (SS sn)) of
  SLT -> eliminate $ ltToSuccLeq sm (SS sn) Refl
  SEQ -> eqToRefl sm (SS sn) Refl
  SGT -> case leqToCmp sm (SS sn) Witness of               -- todo: make it shorter 
    Left Refl -> eliminate $ eqlCmpEQ sm (SS sn) Refl
  --  Right Refl -> error "test"                           If I enanble this case, the compiler shows a warning about inaccesible case. 


-- prove n + (a - b) == (n + a) - b 

newtype MultiAssoc op1 op2 n = MultiAssoc { multiAssocProof :: forall k l. Sing k -> Sing l ->
                               Apply (op1 (Apply (op2 n) k)) l :~:
                               Apply (op2 n) (Apply (op1 k) l)
                               }

type PlusMinusAssoc = MultiAssoc (-@#@$$) (+@#@$$)

plusMinusComm :: forall n k (l :: Nat). 
  Sing n -> Sing k -> Sing l -> IsTrue (l <= k) -> ((n + k) - l) :~: (n + (k - l))
plusMinusComm sn sk sl Witness = multiAssocProof (induction base step sn) sk sl 
  where 
    base :: PlusMinusAssoc 'Z
    base = MultiAssoc $ \sk sl -> Refl
    
    step :: forall (n1 :: Nat). Sing n1 -> PlusMinusAssoc n1 -> PlusMinusAssoc (S n1) 
    step sn1 (MultiAssoc ih) = MultiAssoc $ \sk sl -> case (sl %<= sk) of 
      STrue -> start (((SS sn1) %+ sk) %- sl) 
                 === ((SS (sn1 %+ sk)) %- sl) `because` minusCongL (plusSuccL sn1 sk) sl
                 === (SS ((sn1 %+ sk) %- sl)) `because` minusSucc (sn1 %+ sk) sl undefined
                 === undefined 

witnessToRefl :: IsTrue a -> a :~: 'True
witnessToRefl = \case
  Witness -> Refl

reflToWitness :: a :~: 'True -> IsTrue a
reflToWitness = \case
  Refl -> Witness


multLeq :: forall l m (n :: Nat). IsTrue (m <= n) -> Sing l -> Sing m -> Sing n -> (l*m <= l*n) :~: 'True
multLeq Witness SZ sm sn = Refl
multLeq Witness (SS sl) sm sn = case multLeq Witness sl sm sn of
  Refl -> start (((SS sl) %* sm) %<= ((SS sl) %* sn))
            === (((sl %* sm) %+ sm) %<= ((sl %* sn) %+ sn)) `because` sLeqCong (multSuccL sl sm) (multSuccL sl sn)
            === STrue `because` (witnessToRefl $ plusMonotone (sl %* sm) (sl %* sn) sm sn Witness Witness)
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}

module Data.Type.Zahlen.Class.Arithmetic where
 
--import Data.Promotion.Prelude.Enum
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable

import Data.Type.Equality           ((:~:) (..))
import Data.Type.Natural
import Data.Type.Natural.Class.Arithmetic
import Data.Type.Natural.Class.Order (leqTrans, leqAntisymm, leqRefl)
import Data.Kind                    (Type)

import Proof.Propositional

import Unsafe.Coerce

import Data.Type.Zahlen.Definitions

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
  plusCong' (SS n) (SZ) (SS n) (plusZeroR (SS n))
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

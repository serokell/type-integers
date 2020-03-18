{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Data.Type.Integer where

import Data.Singletons.TH

import Data.Type.Equality
import Data.Type.Natural hiding (induction, one, sOne)
import qualified Data.Type.Natural.Class.Arithmetic as A
-- import Data.Kind                     (Type)

import Proof.Equational
import Proof.Propositional

import Unsafe.Coerce

import Data.Type.Internal.Integer
import Data.Type.Internal.Nat
import Data.Type.Class.Arithmetic

import Prelude hiding (Integer)

-- Equality

posNegZeroPostulate
  :: 'Pos 'Z :~: 'Neg 'Z
posNegZeroPostulate = unsafeCoerce Refl

cong2
  :: forall f a a' b b'. Proxy f
  -> a :~: a'
  -> b :~: b'
  -> f a b :~: f a' b'
cong2 _ Refl Refl = Refl

posInjective
  :: forall n m. 'Pos n :~: 'Pos m
  -> n :~: m
posInjective Refl = Refl

posLemma
  :: forall n m. n :~: m
  -> 'Pos n :~: 'Pos m
posLemma Refl = Refl

negLemma
  :: forall n m. n :~: m
  -> 'Neg n :~: 'Neg m
negLemma Refl = Refl

negInjective
  :: forall n m. 'Neg n :~: 'Neg m
  -> n :~: m
negInjective Refl = Refl

plusCongruence
  :: forall (n :: Integer) (m :: Integer) (p :: Integer). Sing n
  -> Sing m
  -> Sing p
  -> n :~: m
  -> n + p :~: m + p
plusCongruence _ _ _ Refl = Refl

plusCongruenceR
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> n :~: p
  -> m + n :~: m + p
plusCongruenceR _ _ _ Refl = Refl

plusCong'
  :: forall (n :: Nat) (m :: Nat) (p :: Nat). Sing n
  -> Sing m
  -> Sing p
  -> n + m :~: p
  -> 'Pos n + 'Pos m :~: 'Pos p
plusCong' _ _ _ Refl = Refl

multCongInt
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> m :~: n
  -> m * p :~: n * p
multCongInt _ _ _ Refl = Refl

multCongInt'
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> n :~: p
  -> m * n :~: m * p
multCongInt' _ _ _ Refl = Refl

negInv
  :: forall n. Sing n
  -> Inverse (Inverse n) :~: n
negInv (SPos _) = Refl
negInv (SNeg _) = Refl

subTrivialLemma
  :: forall (m :: Nat). Sing m
  -> Sub m m :~: 'Pos 'Z
subTrivialLemma SZ = Refl
subTrivialLemma (SS m) = subTrivialLemma m

inverseZero
  :: forall (m :: Integer). Sing m
  -> m + Inverse m :~: 'Pos 'Z
inverseZero (SPos m) = subTrivialLemma m
inverseZero (SNeg m) = subTrivialLemma m

absoluteIdem
  :: forall n. Sing n
  -> Absolute (Absolute n) :~: Absolute n
absoluteIdem (SPos _) = Refl
absoluteIdem (SNeg _) = Refl

zeroIdentity
  :: forall (m :: Integer). Sing m
  -> 'Pos 'Z + m :~: m
zeroIdentity (SPos _) = Refl
zeroIdentity (SNeg SZ) = posNegZeroPostulate
zeroIdentity (SNeg (SS _)) = Refl

zeroIdentityR
  :: forall (m :: Integer). Sing m
  -> m + 'Pos 'Z :~: m
zeroIdentityR (SPos SZ) = Refl
zeroIdentityR (SPos (SS n)) =
  plusCong' (SS n) SZ (SS n) (plusZeroR (SS n))
zeroIdentityR (SNeg SZ) =
  posNegZeroPostulate
zeroIdentityR (SNeg (SS _)) = Refl

zeroIdentityRNeg
  :: forall (m :: Integer). Sing m
  -> m + 'Neg 'Z :~: m
zeroIdentityRNeg m =
  trans
    (plusCongruenceR m (SNeg SZ) (SPos SZ) $ sym posNegZeroPostulate) $
    zeroIdentityR m

subLemma
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> n :~: p
  -> Sub m n :~: Sub m p
subLemma _ _ _ Refl = Refl

subLemma'
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> m :~: n
  -> Sub m p :~: Sub n p
subLemma' _ _ _ Refl = Refl

commZ
  :: forall (m :: Integer) (n :: Integer). Sing m
  -> Sing n
  -> m + n :~: n + m
commZ (SPos m) (SPos n) = cong (Proxy @'Pos) (plusComm m n)
commZ (SNeg m) (SNeg n) = cong (Proxy @'Neg) (plusComm m n)
commZ (SPos _) (SNeg _) = Refl
commZ (SNeg _) (SPos _) = Refl

distrSub
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> (Sub m n + 'Pos p) :~: Sub (m + p) n
distrSub _ SZ SZ = Refl
distrSub _ SZ (SS _) = Refl
distrSub m (SS n) SZ =
  trans
    (zeroIdentityR $ sSub m (SS n))
    (subLemma' m (m %+ SZ) (SS n) (sym (plusZeroR m)))
distrSub m (SS n) (SS p) = distrSub m (SS n) (SS p)

distrSubLNeg
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Sub m n + 'Neg p :~: Sub m (n + p)
distrSubLNeg _ SZ SZ = Refl
distrSubLNeg _ SZ (SS _) = Refl
distrSubLNeg m (SS n) SZ =
  trans
    (zeroIdentityRNeg $ sSub m (SS n))
    (subLemma m (SS n) (SS n %+ SZ) (sym $ plusZeroR (SS n)))
distrSubLNeg (SS m) (SS n) (SS p) = unsafeCoerce $ distrSubLNeg m n p
distrSubLNeg SZ (SS _) (SS _) = undefined

distrNeg
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> 'Neg m + Sub n p :~: Sub n (m + p)
distrNeg m n p =
  start (SNeg m %+ sSub n p)
  === (sSub n p %+ SNeg m) `because` commZ (SNeg m) (sSub n p)
  === sSub n (p %+  m) `because` distrSubLNeg n p m
  === sSub n (m %+ p) `because` subLemma n (p %+ m) (m %+ p) (plusComm p m)

distrSubL
  :: forall (m :: Nat) (n :: Nat) (p :: Nat). Sing m
  -> Sing n
  -> Sing p
  -> Sub m n + 'Pos p :~: Sub (m + p) n
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
  -> 'Pos m + Sub n p :~: Sub (m + n) p
distrSubR m n p =
  start (SPos m %+ sSub n p)
  === sSub n p %+ SPos m `because` commZ (SPos m) (sSub n p)
  === sSub (n %+ m) p `because` distrSubL n p m
  === sSub (m %+ n) p `because` subLemma' (n %+ m) (m %+ n) p (plusComm n m)

plusAssocZ
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> ((m + n) + p) :~: (m + (n + p))
plusAssocZ (SPos SZ) n p =
  trans
    (plusCongruence (SPos SZ %+ n) n p $ zeroIdentity n)
    (sym $ zeroIdentity $ n %+ p)
plusAssocZ m (SPos SZ) p =
  trans
    (plusCongruence (m %+ SPos SZ) m p (zeroIdentityR m))
    (plusCongruenceR m p (SPos SZ %+ p) (sym $ zeroIdentity p))
plusAssocZ m n (SPos SZ) =
  trans
    (zeroIdentityR (m %+ n))
    (plusCongruenceR m n (n %+ SPos SZ) (sym $ zeroIdentityR n))
plusAssocZ (SPos m) (SPos n) (SPos p) =
  cong (Proxy @'Pos) (plusAssoc m n p)
plusAssocZ (SNeg m) (SNeg n) (SNeg p) =
  cong (Proxy @'Neg) (plusAssoc m n p)
plusAssocZ (SPos m) (SNeg n) (SPos p) =
  trans (distrSubL m n p) (sym (distrSubR m p n))
plusAssocZ (SNeg m) (SPos n) (SPos p) =
  distrSubL n m p
plusAssocZ (SNeg m) (SNeg n) (SPos p) =
  sym (distrNeg m p n)
plusAssocZ (SPos m) (SNeg n) (SNeg p) =
  distrSubLNeg m n p
plusAssocZ (SPos m) (SPos n) (SNeg p) =
  sym (distrSubR m n p)
plusAssocZ (SNeg m) (SPos n) (SNeg p) =
  trans (distrSubLNeg n m p) (sym (distrNeg m n p))

zeroMult
  :: forall (m :: Integer). Sing m
  -> 'Pos 'Z * m :~: 'Pos 'Z
zeroMult (SPos _) = Refl
zeroMult (SNeg _) = sym posNegZeroPostulate

zeroMult'
  :: forall (m :: Integer). Sing m
  -> m * 'Pos 'Z :~: 'Pos 'Z
zeroMult' (SPos m) = posLemma (multZeroR m)
zeroMult' (SNeg m) =
  start (SNeg m %* SPos SZ)
  === SNeg SZ `because` negLemma (multZeroR m)
  === SPos SZ `because` sym posNegZeroPostulate

prodComm
  :: forall (m :: Integer) (n :: Integer). Sing m
  -> Sing n
  -> m * n :~: n * m
prodComm (SPos m) (SPos n) = posLemma $ multComm m n
prodComm (SNeg m) (SNeg n) = posLemma $ multComm m n
prodComm (SNeg m) (SPos n) = negLemma $ multComm m n
prodComm (SPos m) (SNeg n) = negLemma $ multComm m n

prodAssoc
  :: forall (m :: Integer) (n :: Integer) (p :: Integer). Sing m
  -> Sing n
  -> Sing p
  -> (m * n) * p :~: m * (n * p)
prodAssoc (SPos m) (SPos n) (SPos p) = posLemma $ multAssoc m n p
prodAssoc (SNeg m) (SNeg n) (SNeg p) = negLemma $ multAssoc m n p
prodAssoc (SNeg m) (SPos n) (SPos p) = negLemma $ multAssoc m n p
prodAssoc (SNeg m) (SPos n) (SNeg p) = posLemma $ multAssoc m n p
prodAssoc (SPos m) (SNeg n) (SNeg p) = posLemma $ multAssoc m n p
prodAssoc (SPos m) (SNeg n) (SPos p) = negLemma $ multAssoc m n p
prodAssoc (SPos m) (SPos n) (SNeg p) = negLemma $ multAssoc m n p
prodAssoc (SNeg m) (SNeg n) (SPos p) = posLemma $ multAssoc m n p

subMinus
  :: forall (a :: Nat) (b :: Nat). ((a <= b) ~ 'True) => Sing a
  -> Sing b
  -> Sub a b :~: 'Neg (b - a)
subMinus SZ SZ = unsafeCoerce Refl
subMinus SZ (SS _) = Refl
subMinus (SS n) (SS m) = subMinus n m

subMinus2
  :: forall (a :: Nat) (b :: Nat). IsTrue (b <= a) -> Sing a
  -> Sing b
  -> Sub a b :~: 'Pos (a - b)
subMinus2 Witness SZ SZ = Refl
subMinus2 Witness (SS _) SZ = Refl
subMinus2 Witness (SS n) (SS m) = subMinus2 Witness n m

--- orphan instances 

instance IsCommutativeRing Integer where
  type Zero' = ('Pos 'Z)
  type One' = ('Pos ('S 'Z))
  type Inv m = Inverse m

  oneIsNotZero :: forall (x :: Integer) y. (x ~ One', y ~ ('Pos 'Z)) => (x :~: y) -> Void
  oneIsNotZero = \case {}

  associativity :: Sing (x :: Integer) -> Sing y -> Sing n -> (x + y) + n :~: x + (y + n)
  associativity = plusAssocZ
  
  commutativity :: Sing (x :: Integer) -> Sing y -> x + y :~: y + x
  commutativity = commZ
  
  associativityProduct :: Sing (m :: Integer) -> Sing n -> Sing p -> (m * n) * p :~: m * (n * p)
  associativityProduct = prodAssoc
  
  commutativityProduct :: Sing (m :: Integer) -> Sing n -> m * n :~: n * m
  commutativityProduct = prodComm

  zeroNeutral :: Sing (x :: Integer) -> Zero' + x :~: x
  zeroNeutral = zeroIdentity

  inverseAxiom :: Sing (x :: Integer) -> (x + Inv x) :~: Zero'
  inverseAxiom (SPos m) = inverseZero (SPos m)
  inverseAxiom (SNeg m) = inverseZero (SPos m)

  oneNeutral :: Sing (x :: Integer) -> x * One' :~: x
  oneNeutral (SPos m) = cong (Proxy @'Pos) (multOneR m) 
  oneNeutral (SNeg m) = cong (Proxy @'Neg) (multOneR m)

  multRightDistrib :: Sing (x :: Integer) -> Sing (y :: Integer) -> Sing (u :: Integer)
    -> (x * (y + u)) :~: ((x * y) + (x * u))
  multRightDistrib (SPos l) (SPos m) (SPos n) = cong (Proxy @'Pos) (A.multPlusDistrib l m n)
  multRightDistrib (SNeg l) (SNeg m) (SNeg n) = cong (Proxy @'Pos) (A.multPlusDistrib l m n)
  multRightDistrib (SNeg l) (SPos m) (SPos n) = cong (Proxy @'Neg) (A.multPlusDistrib l m n)
  multRightDistrib (SPos l) (SNeg m) (SNeg n) = cong (Proxy @'Neg) (A.multPlusDistrib l m n)
  multRightDistrib sl@(SPos l) sm@(SNeg m) sn@(SPos n) = case (n %<= m) of
    STrue -> start (sl %* (sm %+ sn))
                === (sl %* (n `sSub` m)) `because` Refl
                === (sl %* (SNeg (m %- n))) `because` multCongR sl (subMinus n m)
                === (SNeg ((l %* (m %- n)))) `because` Refl
                === (SNeg ((l %* m) %- (l %* n))) `because` cong (Proxy @'Neg) (multMinusDistrib m n l)
                === ((l %* n) `sSub` (l %* m)) `because` (sym (withRefl (multLeq Witness l n m) $ subMinus (l %* n) (l %* m)))
                === ((SNeg $ l %* m) %+ (SPos $ l %* n)) `because` Refl
                === (((SPos l) %* (SNeg m)) %+ ((SPos l) %* (SPos n))) `because` Refl
    SFalse ->   start (sl %* (sm %+ sn))
                  === (sl %* (n `sSub` m)) `because` Refl
                  === (sl %* (SPos (n %- m))) `because` multCongR sl (subMinus2 (notLeqToLeq n m) n m)
                  === (SPos ((l %* (n %- m)))) `because` Refl
                  === (SPos ((l %* n) %- (l %* m))) `because` cong (Proxy @'Pos) (withWitness (notLeqToLeq n m) $ multMinusDistrib n m l)
                  === ((l %* n) `sSub` (l %* m)) `because` (sym $ subMinus2 (reflToWitness $ multLeq (notLeqToLeq n m) l m n) (l %* n) (l %* m))
                  === ((sl %* sm) %+ (sl %* sn)) `because` Refl
  multRightDistrib sl@(SNeg l) sm@(SNeg m) sn@(SPos n) = case (n %<= m) of
    STrue -> start (sl %* (sm %+ sn))
                === (sl %* (n `sSub` m)) `because` Refl
                === (sl %* (SNeg (m %- n))) `because` multCongR sl (subMinus n m)
                === (SPos ((l %* (m %- n)))) `because` Refl
                === (SPos ((l %* m) %- (l %* n))) `because` cong (Proxy @'Pos) (multMinusDistrib m n l)
                === ((l %* m) `sSub` (l %* n)) `because` (sym $ subMinus2 (reflToWitness $ multLeq Witness l n m) (l %* m) (l %* n))
                === ((SPos $ l %* m) %+ (SNeg $ l %* n)) `because` Refl
                === (((SNeg l) %* (SNeg m)) %+ ((SNeg l) %* (SPos n))) `because` Refl
    SFalse ->   start (sl %* (sm %+ sn))
                  === (sl %* (n `sSub` m)) `because` Refl
                  === (sl %* (SPos (n %- m))) `because` multCongR sl (subMinus2 (notLeqToLeq n m) n m)
                  === (SNeg ((l %* (n %- m)))) `because` Refl
                  === (SNeg ((l %* n) %- (l %* m))) `because` cong (Proxy @'Neg) (withWitness (notLeqToLeq n m) $ multMinusDistrib n m l)
                  === ((l %* m) `sSub` (l %* n)) `because` (sym $ withRefl (multLeq (notLeqToLeq n m) l m n) $ subMinus (l %* m) (l %* n))
                  === ((sl %* sm) %+ (sl %* sn)) `because` Refl
  multRightDistrib sl sm@(SPos _) sn@(SNeg _) =
    start (sl %* (sm %+ sn))
      === (sl %* (sn %+ sm)) `because` multCongR sl (commutativity sm sn)
      === ((sl %* sn) %+ (sl %* sm)) `because` multRightDistrib sl sn sm
      === ((sl %* sm) %+ (sl %* sn)) `because` commutativity (sl %* sn) (sl %* sm)

instance IsInteger Integer where
  type Signum ('Pos n) = 'P
  type Signum ('Neg n) = 'N
  type Absolute'' (_ n) = n

  induction base _ _ (SPos SZ) = base
  induction base step neg (SPos (SS n)) = step (SPos n) $ induction base step neg (SPos n)
  induction base step neg sn@(SNeg n) = neg sn $ induction base step neg (SPos n)
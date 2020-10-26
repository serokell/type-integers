{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NoStarIsType        #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE LambdaCase          #-}

module Data.Type.Zahlen.Class.Arithmetic
       ( Zero, One, sZero, sOne
       , plusCong, plusCongL, plusCongR
       , multCong, multCongL, multCongR
       , minusCong, minusCongL, minusCongR
       , plusZeroL, plusZeroR
       , multZeroL, multZeroR, multOneL, multOneR
       , negateNegate, absIdem
       , plusComm, plusAssoc, plusMultDistrib, multPlusDistrib
       , multComm, multAssoc
       ) where

import Data.Singletons.Prelude (type (*), type (+), type (-), Abs, Negate, Sing, (%+), (%*), sNegate)
import Data.Type.Natural (Nat (Z, S), SNat (SS, SZ))
import qualified Data.Type.Natural.Class.Arithmetic as Nat
import Data.Typeable ((:~:) (Refl))
import Proof.Equational (trans, cong, start, (===), because, sym)
import Data.Proxy (Proxy (Proxy))

import Unsafe.Coerce (unsafeCoerce)

import Data.Type.Zahlen.Definitions (SZahlen (SNeg1, SPos), Zahlen (Neg1, Pos))

type Zero = 'Pos 'Z
type One  = 'Pos ('S 'Z)

sZero :: Sing ('Pos 'Z)
sZero = SPos SZ

sOne :: Sing ('Pos ('S 'Z))
sOne = SPos (SS SZ)

-- Equality

posLemma
  :: forall n m. n :~: m
  -> 'Pos n :~: 'Pos m
posLemma Refl = Refl

negLemma
  :: forall n m. n :~: m
  -> 'Neg1 n :~: 'Neg1 m
negLemma Refl = Refl

plusCong
  :: forall (n :: Zahlen) (m :: Zahlen) (n' :: Zahlen) (m' :: Zahlen).
     n :~: m
  -> n' :~: m'
  -> n + n' :~: m + m'
plusCong Refl Refl = Refl

plusCongL :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             n :~: m -> Sing k -> n + k :~: m + k
plusCongL Refl _ = Refl

plusCongR :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             Sing k -> n :~: m -> k + n :~: k + m
plusCongR _ Refl = Refl

multCong :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen) (l :: Zahlen).
            n :~: m -> l :~: k -> n * l :~: m * k
multCong Refl Refl = Refl

multCongL :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             n :~: m -> Sing k -> n * k :~: m * k
multCongL Refl _ = Refl

multCongR :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
             Sing k -> n :~: m -> k * n :~: k * m
multCongR _ Refl = Refl

minusCong :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen) (l :: Zahlen).
             n :~: m -> l :~: k -> n - l :~: m - k
minusCong Refl Refl = Refl

minusCongL :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
              n :~: m -> Sing k -> n - k :~: m - k
minusCongL Refl _ = Refl

minusCongR :: forall (n :: Zahlen) (m :: Zahlen) (k :: Zahlen).
              Sing k -> n :~: m -> k - n :~: k - m
minusCongR _ Refl = Refl

negateNegate
  :: forall n. Sing (n :: Zahlen)
  -> Negate (Negate n) :~: n
negateNegate (SPos SZ)     = Refl
negateNegate (SPos (SS n)) = Refl
negateNegate (SNeg1 n)     = Refl

absIdem
  :: forall n. Sing (n :: Zahlen)
  -> Abs (Abs n) :~: Abs n
absIdem (SPos n)  = Refl
absIdem (SNeg1 n) = Refl

plusZeroL :: Sing (n :: Zahlen) -> 'Pos 'Z + n :~: n
plusZeroL (SPos _)  = Refl
plusZeroL (SNeg1 _) = Refl

plusZeroR :: Sing (n :: Zahlen) -> n + 'Pos 'Z :~: n
plusZeroR sm = trans (plusComm sm (SPos SZ)) (plusZeroL sm)

multZeroL :: Sing (a :: Zahlen) -> Zero * a :~: Zero
multZeroL (SPos sn)  =
    start (sZero %* (SPos sn))
    === SPos (SZ %* sn) `because` Refl
    === sZero `because` cong (Proxy :: Proxy 'Pos) (Nat.multZeroL sn)
multZeroL (SNeg1 sn) = Refl

multZeroR :: Sing (a :: Zahlen) -> a * Zero :~: Zero
multZeroR sa = trans (multComm sa sZero) (multZeroL sa) 

multOneL :: Sing (a :: Zahlen) -> One * a :~: a
multOneL (SPos sn) =
    start (sOne %* (SPos sn))
    === SPos ((SS SZ) %* sn) `because` Refl
    === SPos sn `because` cong (Proxy :: Proxy 'Pos) (Nat.multOneL sn)
multOneL (SNeg1 sn) =
    start (sOne %* (SNeg1 sn))
    === SNeg1 (SZ %* sn %+ SZ %+ sn) `because` Refl
    === SNeg1 (SZ %+ SZ %+ sn)
        `because` (cong (Proxy :: Proxy 'Neg1) 
                  $ flip Nat.plusCongL sn
                  $ flip Nat.plusCongL SZ
                  $ Nat.multZeroL sn)
    === SNeg1 (SZ %+ sn)
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ flip Nat.plusCongL sn
                  $ Nat.plusZeroL SZ)
    === SNeg1 sn
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ Nat.plusZeroL sn)

multOneR :: Sing (a :: Zahlen) -> a * One :~: a
multOneR sa = trans (multComm sa sOne) (multOneL sa)

plusComm :: Sing (n :: Zahlen) -> Sing (m :: Zahlen) -> n + m :~: m + n
plusComm (SPos a) (SPos b)   = posLemma (Nat.plusComm a b)
plusComm (SNeg1 a) (SNeg1 b) = cong (Proxy :: Proxy 'Neg1)
                             $ cong (Proxy :: Proxy 'S)
                             $ Nat.plusComm a b
plusComm (SPos a) (SNeg1 b)  = Refl
plusComm (SNeg1 a) (SPos b)  = Refl

multComm :: Sing (a :: Zahlen) -> Sing (b :: Zahlen) -> a * b :~: b * a
multComm (SPos sn) (SPos sm) = posLemma (Nat.multComm sn sm)
multComm (SNeg1 sn) (SPos sm) = Refl
multComm (SPos sn) (SNeg1 sm) = Refl
multComm (SNeg1 sn) (SNeg1 sm) = posLemma (Nat.multComm (SS sn) (SS sm))

negatePlusDistrib :: Sing (a :: Zahlen)
                  -> Sing (b :: Zahlen)
                  -> Negate (a + b) :~: Negate a + Negate b
negatePlusDistrib sa sb = undefined

negateNegOneMult :: Sing (a :: Zahlen)
                 -> Negate a :~: 'Neg1 'Z * a
negateNegOneMult sa = undefined

negateMultL :: Sing (a :: Zahlen)
            -> Sing (b :: Zahlen)
            -> Negate (a * b) :~: (Negate a) * b
negateMultL = undefined

negateMultR :: Sing (a :: Zahlen)
            -> Sing (b :: Zahlen)
            -> Negate (a * b) :~: a * (Negate b)
negateMultR = undefined

plusMultDistrib :: Sing (a :: Zahlen)
                -> Sing (b :: Zahlen)
                -> Sing (c :: Zahlen)
                -> (a + b) * c :~: (a * c) + (b * c)
plusMultDistrib sa sb sc =
    start ((sa %+ sb) %* sc)
    === sc %* (sa %+ sb) `because` multComm (sa %+ sb) sc
    === sc %* sa %+ sc %* sb `because` multPlusDistrib sc sa sb
    === sa %* sc %+ sb %* sc
        `because` plusCong (multComm sc sa) (multComm sc sb)

multPlusDistrib :: Sing (a :: Zahlen)
                -> Sing (b :: Zahlen)
                -> Sing (c :: Zahlen)
                -> a * (b + c) :~: a * b + a * c
multPlusDistrib sa sb sc = case sa of
    SPos sn  -> multPlusDistribPos sn sb sc
    SNeg1 sn -> multPlusDistribNeg sn sb sc

multPlusDistribPos :: Sing (n :: Nat)
                   -> Sing (a :: Zahlen)
                   -> Sing (b :: Zahlen)
                   -> 'Pos n * (a + b) :~: 'Pos n * a + 'Pos n * b
multPlusDistribPos sn sa sb = case sn of
    SZ    ->
        start (sZero %* (sa %+ sb))
        === sZero `because` multZeroL (sa %+ sb)
        === sZero %+ sZero `because` plusZeroL sZero
        === (sZero %* sa) %+ (sZero %* sb)
            `because` plusCong (sym $ multZeroL sa) (sym $ multZeroL sb)
    SS sp ->
        start (SPos (SS sp) %* (sa %+ sb))
        === SPos sp %* (sa %+ sb) %+ (sa %+ sb)
            `because` multPosSucc sp (sa %+ sb)
        === (SPos sp %* sa %+ SPos sp %* sb) %+ (sa %+ sb)
            `because` plusCongL (multPlusDistribPos sp sa sb) (sa %+ sb)
        === ((SPos sp %* sa %+ SPos sp %* sb) %+ sa) %+ sb
            `because` sym (plusAssoc (SPos sp %* sa %+ SPos sp %* sb) sa sb)
        === (SPos sp %* sa %+ (SPos sp %* sb %+ sa)) %+ sb
            `because` (flip plusCongL sb
                      $ plusAssoc (SPos sp %* sa) (SPos sp %* sb) sa)
        === (SPos sp %* sa %+ (sa %+ SPos sp %* sb)) %+ sb
            `because` (flip plusCongL sb 
                      $ plusCongR (SPos sp %* sa)
                      $ plusComm (SPos sp %* sb) sa)
        === ((SPos sp %* sa %+ sa) %+ SPos sp %* sb) %+ sb
            `because` (flip plusCongL sb 
                      $ sym
                      $ plusAssoc (SPos sp %* sa) sa (SPos sp %* sb))
        === (SPos sp %* sa %+ sa) %+ (SPos sp %* sb %+ sb)
            `because` plusAssoc (SPos sp %* sa %+ sa) (SPos sp %* sb) sb
        === SPos (SS sp) %* sa %+ SPos (SS sp) %* sb
            `because` plusCong (sym $ multPosSucc sp sa)
                               (sym $ multPosSucc sp sb)

multPlusDistribNeg :: Sing (n :: Nat)
                   -> Sing (a :: Zahlen)
                   -> Sing (b :: Zahlen)
                   -> 'Neg1 n * (a + b) :~: 'Neg1 n * a + 'Neg1 n * b
multPlusDistribNeg sn sa sb = case sn of
    SZ    ->
        start (SNeg1 SZ %* (sa %+ sb))
        === sNegate (sa %+ sb) `because` (sym $ negateNegOneMult (sa %+ sb))
        === sNegate sa %+ sNegate sb `because` (negatePlusDistrib sa sb)
        === SNeg1 SZ %* sa %+ SNeg1 SZ %* sb
            `because` plusCong (negateNegOneMult sa) (negateNegOneMult sb)
    SS sp ->
        start (SNeg1 (SS sp) %* (sa %+ sb))
        === SNeg1 sp %* (sa %+ sb) %+ SNeg1 SZ %* (sa %+ sb)
            `because` multNegSucc sp (sa %+ sb)
        === (SNeg1 sp %* sa %+ SNeg1 sp %* sb) %+ (SNeg1 SZ %* sa %+ SNeg1 SZ %* sb)
            `because` plusCong (multPlusDistribNeg sp sa sb)
                               (multPlusDistribNeg SZ sa sb)
        === SNeg1 sp %* sa %+ SNeg1 sp %* sb %+ SNeg1 SZ %* sa %+ SNeg1 SZ %* sb
            `because` sym (plusAssoc (SNeg1 sp %* sa %+ SNeg1 sp %* sb)
                                (SNeg1 SZ %* sa)
                                (SNeg1 SZ %* sb))
        === SNeg1 sp %* sa %+ (SNeg1 sp %* sb %+ SNeg1 SZ %* sa) %+ SNeg1 SZ %* sb
            `because` (flip plusCongL (SNeg1 SZ %* sb)
                      $ plusAssoc (SNeg1 sp %* sa)
                                  (SNeg1 sp %* sb)
                                  (SNeg1 SZ %* sa))
        === SNeg1 sp %* sa %+ (SNeg1 SZ %* sa %+ SNeg1 sp %* sb) %+ SNeg1 SZ %* sb
            `because` (flip plusCongL (SNeg1 SZ %* sb)
                      $ plusCongR (SNeg1 sp %* sa)
                      $ plusComm (SNeg1 sp %* sb) (SNeg1 SZ %* sa))
        === SNeg1 sp %* sa %+ SNeg1 SZ %* sa %+ SNeg1 sp %* sb %+ SNeg1 SZ %* sb
            `because` (flip plusCongL (SNeg1 SZ %* sb)
                      $ sym
                      $ plusAssoc (SNeg1 sp %* sa)
                                  (SNeg1 SZ %* sa)
                                  (SNeg1 sp %* sb))
        === (SNeg1 sp %* sa %+ SNeg1 SZ %* sa) %+ (SNeg1 sp %* sb %+ SNeg1 SZ %* sb)
            `because` plusAssoc (SNeg1 sp %* sa %+ SNeg1 SZ %* sa)
                                (SNeg1 sp %* sb)
                                (SNeg1 SZ %* sb)
        === SNeg1 (SS sp) %* sa %+ SNeg1 (SS sp) %* sb
            `because` plusCong (sym $ multNegSucc sp sa)
                               (sym $ multNegSucc sp sb)

multPosSucc :: Sing (n :: Nat)
            -> Sing (a :: Zahlen)
            -> 'Pos ('S n) * a :~: 'Pos n * a + a
multPosSucc sn (SPos sm) =
    start (SPos (SS sn) %* (SPos sm))
    === SPos ((SS sn) %* sm) `because` Refl
    === SPos (sn %* sm %+ sm) `because` Refl
    === SPos (sn %* sm) %+ SPos sm `because` Refl
    === SPos sn %* SPos sm %+ SPos sm `because` Refl
multPosSucc SZ (SNeg1 sm) =
    start (SPos (SS SZ) %* (SNeg1 sm))
    === SNeg1 sm `because` multOneL (SNeg1 sm)
    === sZero %+ SNeg1 sm `because` plusZeroL (SNeg1 sm)
    === sZero %* SNeg1 sm %+ SNeg1 sm
        `because` plusCongL (sym $ multZeroL (SNeg1 sm)) (SNeg1 sm)
multPosSucc (SS sn) (SNeg1 sm) =
    start (SPos (SS (SS sn)) %* SNeg1 sm)
    === SNeg1 (SS sn %* sm %+ SS sn %+ sm) `because` Refl
    === SNeg1 (sn %* sm %+ sm %+ SS sn %+ sm) `because` Refl
    === SNeg1 (SS (sn %* sm %+ sm %+ sn) %+ sm)
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ flip Nat.plusCongL sm
                  $ Nat.plusSuccR (sn %* sm %+ sm) sn)
    === SNeg1 (SS (sn %* sm %+ sm %+ sn %+ sm))
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ Nat.plusSuccL (sn %* sm %+ sm %+ sn) sm)
    === SNeg1 (SS (sn %* sm %+ (sm %+ sn) %+ sm))
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ cong (Proxy :: Proxy 'S)
                  $ flip Nat.plusCongL sm
                  $ Nat.plusAssoc (sn %* sm) sm sn)
    === SNeg1 (SS (sn %* sm %+ (sn %+ sm) %+ sm))
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ cong (Proxy :: Proxy 'S)
                  $ flip Nat.plusCongL sm
                  $ Nat.plusCongR (sn %* sm)
                  $ Nat.plusComm sm sn
                  )
    === SNeg1 (SS (sn %* sm %+ sn %+ sm %+ sm))
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ cong (Proxy :: Proxy 'S)
                  $ flip Nat.plusCongL sm
                  $ sym $ Nat.plusAssoc (sn %* sm) sn sm
                  )
    === SNeg1 (sn %* sm %+ sn %+ sm) %+ SNeg1 sm `because` Refl
    === SPos (SS sn) %* SNeg1 sm %+ SNeg1 sm `because` Refl

multNegSucc :: Sing (n :: Nat)
            -> Sing (a :: Zahlen)
            -> 'Neg1 ('S n) * a :~: 'Neg1 n * a + 'Neg1 'Z * a
multNegSucc sn sa = undefined

{-
   ASSOCIATIVITY OF ADDITION
-}
plusAssoc :: Sing (a :: Zahlen)
          -> Sing (b :: Zahlen)
          -> Sing (c :: Zahlen)
          -> (a + b) + c :~: a + (b + c)
plusAssoc sa sb = \case
   SPos sn  -> plusAssocPos sa sb sn
   SNeg1 sn -> plusAssocNeg sa sb sn

plusAssocPos :: Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> Sing (n :: Nat)
             -> (a + b) + 'Pos n :~: a + (b + 'Pos n)
plusAssocPos sa sb SZ =
    start ((sa %+ sb) %+ sZero)
    === sa %+ sb `because` plusZeroR (sa %+ sb)
    === sa %+ (sb %+ sZero) `because` plusCongR sa (sym (plusZeroR sb))
plusAssocPos sa sb (SS sn) =
    start ((sa %+ sb) %+ SPos (SS sn))
    === ((sa %+ sb) %+ (SPos sn %+ sOne))
        `because` (Nat.plusCongR (sa %+ sb) (oneLemma sn))
    === ((sa %+ sb) %+ SPos sn) %+ sOne
        `because` (sym $ plusAssocOne (sa %+ sb) (SPos sn))
    === (sa %+ (sb %+ SPos sn)) %+ sOne
        `because` Nat.plusCongL (plusAssocPos sa sb sn) sOne
    === sa %+ ((sb %+ SPos sn) %+ sOne)
        `because` plusAssocOne sa (sb %+ SPos sn)
    === sa %+ (sb %+ (SPos sn %+ sOne))
        `because` Nat.plusCongR sa (plusAssocOne sb (SPos sn))
    === sa %+ (sb %+ SPos (SS sn))
        `because` Nat.plusCongR sa (Nat.plusCongR sb (sym $ oneLemma sn))

plusAssocNeg :: Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> Sing (n :: Nat)
             -> (a + b) + 'Neg1 n :~: a + (b + 'Neg1 n)
plusAssocNeg sa sb SZ      = plusAssocNegOne sa sb
plusAssocNeg sa sb (SS sn) =
    start (sa %+ sb %+ SNeg1 (SS sn))
    === (sa %+ sb) %+ (SNeg1 sn %+ SNeg1 SZ)
        `because` plusCongR (sa %+ sb) (negOneLemma sn)
    === ((sa %+ sb) %+ SNeg1 sn) %+ SNeg1 SZ
        `because` sym (plusAssocNegOne (sa %+ sb) (SNeg1 sn))
    === (sa %+ (sb %+ SNeg1 sn)) %+ SNeg1 SZ
        `because` plusCongL (plusAssocNeg sa sb sn) (SNeg1 SZ)
    === sa %+ ((sb %+ SNeg1 sn) %+ SNeg1 SZ)
        `because` plusAssocNegOne sa (sb %+ SNeg1 sn)
    === sa %+ (sb %+ (SNeg1 sn %+ SNeg1 SZ))
        `because` plusCongR sa (plusAssocNegOne sb (SNeg1 sn))
    === sa %+ (sb %+ SNeg1 (SS sn))
        `because` plusCongR sa (plusCongR sb (sym (negOneLemma sn)))

oneLemma :: forall n. Sing (n :: Nat) -> 'Pos ('S n) :~: 'Pos n + One
oneLemma sn =
    start (SPos (SS sn))
      === SPos (sn %+ SS SZ) `because` cong (Proxy :: Proxy 'Pos) lemma
      === SPos sn %+ SPos (SS SZ) `because` Refl
  where
    lemma :: 'S n :~: n + 'S 'Z
    lemma =
        start (SS sn)
        === SS (sn %+ SZ)
            `because` cong (Proxy :: Proxy 'S) (sym (Nat.plusZeroR sn))
        === sn %+ SS SZ
            `because` sym (Nat.plusSuccR sn SZ)

negOneLemma :: forall n. Sing (n :: Nat) -> 'Neg1 ('S n) :~: 'Neg1 n + 'Neg1 'Z
negOneLemma sn =
    start (SNeg1 (SS sn))
    === SNeg1 (SS (sn %+ SZ))
        `because` (cong (Proxy :: Proxy 'Neg1)
                  $ cong (Proxy :: Proxy 'S)
                  $ sym $ Nat.plusZeroR sn)
    === SNeg1 sn %+ SNeg1 SZ `because` Refl

plusAssocOne :: Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> (a + b) + One :~: a + (b + One)
plusAssocOne sa sb = case (sa, sb) of
    (SPos sn, SPos sm)   -> plusAssocOnePP sn sm
    (SPos sn, SNeg1 sm)  -> plusAssocOnePN sn sm
    (SNeg1 sn, SPos sm)  -> plusAssocOneNP sn sm
    (SNeg1 sn, SNeg1 sm) -> plusAssocOneNN sn sm
  where
    plusAssocOnePP :: Sing (n :: Nat)
                   -> Sing (m :: Nat)
                   -> ('Pos n + 'Pos m) + One :~: 'Pos n + ('Pos m + One)
    plusAssocOnePP sn sm =
        start ((SPos sn %+ SPos sm) %+ sOne)
        === SPos (sn %+ sm) %+ sOne `because` Nat.plusCongL (posLemma sn sm) sOne
        === SPos (sn %+ sm %+ SS SZ) `because` Refl
        === SPos (sn %+ (sm %+ SS SZ))
            `because` cong (Proxy :: Proxy 'Pos) (Nat.plusAssoc sn sm (SS SZ))
        === SPos sn %+ SPos (sm %+ SS SZ) `because` (sym $ posLemma sn (sm %+ SS SZ))
        === SPos sn %+ (SPos sm %+ sOne)
            `because` Nat.plusCongR (SPos sn) (sym $ posLemma sm (SS SZ))
      where
        posLemma :: Sing (p :: Nat) -> Sing (q :: Nat) -> 'Pos p + 'Pos q :~: 'Pos (p + q)
        posLemma _ _ = Refl

    plusAssocOnePN :: Sing (n :: Nat)
                   -> Sing (m :: Nat)
                   -> ('Pos n + 'Neg1 m) + One :~: 'Pos n + ('Neg1 m + One)
    plusAssocOnePN SZ sm =
        start ((sZero %+ SNeg1 sm) %+ sOne)
          === SNeg1 sm %+ sOne `because` Nat.plusCongL (plusZeroL (SNeg1 sm)) sOne
          === sZero %+ (SNeg1 sm %+ sOne) `because` (sym $ plusZeroL (SNeg1 sm %+ sOne))
    plusAssocOnePN (SS sn) SZ =
        start ((SPos (SS sn) %+ SNeg1 SZ) %+ sOne)
        === SPos sn %+ sOne `because` plusCongL (lemma sn) sOne
        === SPos (SS sn) `because` sym (oneLemma sn)
        === SPos (SS sn) %+ sZero `because` sym (plusZeroR (SPos (SS sn)))
        === SPos (SS sn) %+ (sOne %+ SNeg1 SZ)
            `because` plusCongR (SPos (SS sn)) (sym (lemma SZ))
        === SPos (SS sn) %+ (SNeg1 SZ %+ sOne)
            `because` plusCongR (SPos (SS sn)) (plusComm sOne (SNeg1 SZ))
      where
        lemma :: Sing p -> 'Pos ('S p) + 'Neg1 'Z :~: 'Pos p
        lemma _ = Refl
    plusAssocOnePN (SS sn) (SS SZ) =
        start ((SPos (SS sn) %+ SNeg1 (SS SZ)) %+ sOne)
        === (SPos sn %+ SNeg1 SZ) %+ sOne `because` plusCongL (lemma1 sn) sOne
        === SPos sn %+ (SNeg1 SZ %+ sOne) `because` plusAssocOnePN sn SZ
        === SPos sn %+ (sOne %+ SNeg1 SZ)
            `because` plusCongR (SPos sn) (plusComm (SNeg1 SZ) sOne)
        === SPos sn %+ sZero
            `because` plusCongR (SPos sn) lemma2
        === SPos sn
            `because` plusZeroR (SPos sn)
        === SPos (SS sn) %+ SNeg1 SZ
            `because` sym (lemma3 sn)
        === SPos (SS sn) %+ (sZero %+ SNeg1 SZ)
            `because` plusCongR (SPos (SS sn)) (plusZeroL (SNeg1 SZ))
        === SPos (SS sn) %+ (sOne %+ SNeg1 (SS SZ))
            `because` plusCongR (SPos (SS sn)) (sym (lemma1 SZ))
        === SPos (SS sn) %+ (SNeg1 (SS SZ) %+ sOne)
            `because` plusCongR (SPos (SS sn)) (plusComm sOne (SNeg1 (SS SZ)))
      where
        lemma1 :: Sing (p :: Nat)
               -> 'Pos ('S p) + 'Neg1 ('S 'Z) :~: 'Pos p + 'Neg1 'Z
        lemma1 _ = Refl

        lemma2 :: One + 'Neg1 'Z :~: Zero
        lemma2 = Refl

        lemma3 :: Sing (p :: Nat) -> 'Pos ('S p) + 'Neg1 'Z :~: 'Pos p
        lemma3 _ = Refl
    plusAssocOnePN (SS sn) (SS (SS sm)) =
        start ((SPos (SS sn) %+ SNeg1 (SS (SS sm))) %+ sOne)
        === (SPos sn %+ SNeg1 (SS sm)) %+ sOne `because` Refl
        === SPos sn %+ (SNeg1 (SS sm) %+ sOne) `because` plusAssocOnePN sn (SS sm)
        === SPos sn %+ (sOne %+ SNeg1 (SS sm)) `because` Refl
        === SPos sn %+ (sZero %+ SNeg1 sm) `because` Refl
        === SPos sn %+ SNeg1 sm `because` plusCongR (SPos sn) (plusZeroL (SNeg1 sm))
        === SPos (SS sn) %+ SNeg1 (SS sm) `because` Refl
        === SPos (SS sn) %+ (sZero %+ SNeg1 (SS sm))
            `because` plusCongR (SPos (SS sn)) (plusZeroL (SNeg1 (SS sm)))
        === SPos (SS sn) %+ (sOne %+ SNeg1 (SS (SS sm)))
            `because` plusCongR (SPos (SS sn)) (lemma (SS sm))
        === SPos (SS sn) %+ (SNeg1 (SS (SS sm)) %+ sOne)
            `because` plusCongR (SPos (SS sn)) (plusComm sOne (SNeg1 (SS (SS sm))))
      where
        lemma :: Sing (p :: Nat) -> 'Pos 'Z + 'Neg1 p :~: 'Pos ('S 'Z) + 'Neg1 ('S p) 
        lemma _ = Refl

    plusAssocOneNP :: forall n m.
                   Sing (n :: Nat)
                -> Sing (m :: Nat)
                -> ('Neg1 n + 'Pos m) + 'Pos ('S 'Z) :~: 'Neg1 n + ('Pos m + 'Pos ('S 'Z))
    plusAssocOneNP sn sm = trans part1 part2
      where
        part1 :: ('Neg1 n + 'Pos m) + 'Pos ('S 'Z) :~: 'Pos m + ('Neg1 n + 'Pos ('S 'Z))
        part1 =
            start ((SNeg1 sn %+ SPos sm) %+ sOne)
            === (SPos sm %+ SNeg1 sn) %+ sOne
                `because` plusCongL (plusComm (SNeg1 sn) (SPos sm)) sOne
            === SPos sm %+ (SNeg1 sn %+ sOne) `because` plusAssocOnePN sm sn

        part2 :: 'Pos m + ('Neg1 n + One) :~: 'Neg1 n + ('Pos m + One)
        part2 = case sn of
            SZ    ->
                start (SPos sm %+ (SNeg1 SZ %+ sOne))
                === SPos sm %+ (sOne %+ SNeg1 SZ)
                    `because` plusCongR (SPos sm) (plusComm (SNeg1 SZ) sOne)
                === SPos sm %+ sZero `because` Refl
                === SPos sm `because` plusZeroR (SPos sm)
                === SPos (SS sm) %+ SNeg1 SZ `because` Refl
                === SNeg1 SZ %+ SPos (SS sm)
                    `because` plusComm (SPos (SS sm)) (SNeg1 SZ)
                === SNeg1 SZ %+ (SPos sm %+ sOne)
                    `because` plusCongR (SNeg1 SZ) (oneLemma sm)
            SS sp ->
                start (SPos sm %+ (SNeg1 (SS sp) %+ sOne))
                === SPos sm %+ (SNeg1 sp %+ sZero) `because` Refl
                === SPos sm %+ SNeg1 sp
                    `because` plusCongR (SPos sm) (plusZeroR (SNeg1 sp))
                === SPos (SS sm) %+ SNeg1 (SS sp) `because` Refl
                === SNeg1 (SS sp) %+ SPos (SS sm)
                    `because` plusComm (SPos (SS sm)) (SNeg1 (SS sp))
                === SNeg1 (SS sp) %+ (SPos sm %+ sOne)
                    `because` plusCongR (SNeg1 (SS sp)) (oneLemma sm)

    plusAssocOneNN :: forall n m.
                   Sing (n :: Nat)
                -> Sing (m :: Nat)
                -> 'Neg1 n + 'Neg1 m + One :~: 'Neg1 n + ('Neg1 m + One)
    plusAssocOneNN sn sm = trans part1 part2
      where
        part1 :: 'Neg1 n + 'Neg1 m + One :~: 'Neg1 (n + m)
        part1 =
            start (SNeg1 sn %+ SNeg1 sm %+ sOne)
            === SNeg1 (SS (sn %+ sm)) %+ sOne
                `because` Nat.plusCongL (lemma sn sm) sOne
            === sOne %+ SNeg1 (SS (sn %+ sm)) `because` Refl
            === sZero %+ SNeg1 (sn %+ sm) `because` Refl
            === SNeg1 (sn %+ sm) `because` plusZeroL (SNeg1 (sn %+ sm))
          where
            lemma :: Sing (p :: Nat)
                  -> Sing (q :: Nat)
                  -> 'Neg1 p + 'Neg1 q :~: 'Neg1 (S (p + q))
            lemma _ _ = Refl

        part2 :: 'Neg1 (n + m) :~: 'Neg1 n + ('Neg1 m + One)
        part2 = case sm of
            SZ    ->
                start (SNeg1 (sn %+ SZ))
                === SNeg1 sn `because` cong (Proxy :: Proxy 'Neg1) (Nat.plusZeroR sn)
                === SNeg1 sn %+ sZero `because` plusZeroR (SNeg1 sn)
                === SNeg1 sn %+ (sOne %+ SNeg1 SZ)
                    `because` plusCongR (SNeg1 sn) (Refl :: 'Pos 'Z :~: 'Pos ('S 'Z) + 'Neg1 'Z)
                === SNeg1 sn %+ (SNeg1 SZ %+ sOne)
                    `because` plusCongR (SNeg1 sn) (plusComm sOne (SNeg1 SZ))
            SS sp ->
                start (SNeg1 (sn %+ (SS sp)))
                === SNeg1 (SS (sn %+ sp))
                    `because` cong (Proxy :: Proxy 'Neg1) (Nat.plusSuccR sn sp) 
                === SNeg1 sn %+ SNeg1 sp
                    `because` Refl
                === SNeg1 sn %+ (sZero %+ SNeg1 sp)
                    `because` plusCongR (SNeg1 sn) (plusZeroL (SNeg1 sp))
                === SNeg1 sn %+ (sOne %+ SNeg1 (SS sp))
                    `because` plusCongR (SNeg1 sn) (lemma SZ sp)
                === SNeg1 sn %+ (SNeg1 (SS sp) %+ sOne)
                    `because` plusCongR (SNeg1 sn) (plusComm sOne (SNeg1 (SS sp)))
              where
                lemma :: Sing (k :: Nat)
                      -> Sing (l :: Nat)
                      -> 'Pos k + 'Neg1 l :~: 'Pos ('S k) + 'Neg1 ('S l)
                lemma sk sl = Refl

plusAssocNegOne :: Sing (a :: Zahlen)
                -> Sing (b :: Zahlen)
                -> (a + b) + 'Neg1 'Z :~: a + (b + 'Neg1 'Z)
plusAssocNegOne sa sb = case (sa, sb) of
    (SPos sn,  SPos sm)  -> plusAssocNegOnePP sn sm
    (SPos sn,  SNeg1 sm) -> plusAssocNegOnePN sn sm
    (SNeg1 sn, SPos sm)  -> plusAssocNegOneNP sn sm
    (SNeg1 sn, SNeg1 sm) -> plusAssocNegOneNN sn sm
  where
    plusAssocNegOnePP :: Sing (n :: Nat)
                      -> Sing (m :: Nat)
                      -> ('Pos n + 'Pos m) + 'Neg1 'Z :~: 'Pos n + ('Pos m + 'Neg1 'Z)
    plusAssocNegOnePP sn SZ =
        start ((SPos sn %+ sZero) %+ SNeg1 SZ)
        === SPos sn %+ SNeg1 SZ
            `because` plusCongL (plusZeroR (SPos sn)) (SNeg1 SZ)
        === SPos sn %+ (sZero %+ SNeg1 SZ)
            `because` plusCongR (SPos sn) (plusZeroL (SNeg1 SZ))
    plusAssocNegOnePP sn (SS sm) =
        start ((SPos sn %+ SPos (SS sm)) %+ SNeg1 SZ)
        === SPos (sn %+ SS sm) %+ SNeg1 SZ `because` plusCongL (lemma1 sn sm) (SNeg1 SZ)
        === SPos (SS (sn %+ sm)) %+ SNeg1 SZ
            `because` plusCongL (cong (Proxy :: Proxy 'Pos) (Nat.plusSuccR sn sm)) (SNeg1 SZ)
        === SPos (sn %+ sm) `because` Refl
        === SPos sn %+ SPos sm `because` Refl
        === SPos sn %+ (SPos (SS sm) %+ SNeg1 SZ) `because` plusCongR (SPos sn) (lemma2 sm)
      where
        lemma1 :: Sing (p :: Nat)
               -> Sing (q :: Nat)
               -> 'Pos p + 'Pos ('S q) :~: 'Pos (p + 'S q)
        lemma1 _ _ = Refl

        lemma2 :: Sing (p :: Nat)
               -> 'Pos p :~: 'Pos ('S p) + 'Neg1 'Z
        lemma2 _ = Refl

    plusAssocNegOnePN :: Sing (n :: Nat)
                      -> Sing (m :: Nat)
                      -> ('Pos n + 'Neg1 m) + 'Neg1 'Z :~: 'Pos n + ('Neg1 m + 'Neg1 'Z)
    plusAssocNegOnePN SZ sm =
        start ((SPos SZ %+ SNeg1 sm) %+ SNeg1 SZ)
        === SNeg1 sm %+ SNeg1 SZ `because` plusCongL (plusZeroL (SNeg1 sm)) (SNeg1 SZ)
        === SPos SZ %+ (SNeg1 sm %+ SNeg1 SZ) `because` plusZeroL (SNeg1 sm %+ SNeg1 SZ)
    plusAssocNegOnePN (SS sn) SZ =
        start ((SPos (SS sn) %+ SNeg1 SZ) %+ SNeg1 SZ)
        === SPos sn %+ SNeg1 SZ `because` plusCongL (lemma1 sn) (SNeg1 SZ)
        === SPos (SS sn) %+ SNeg1 (SS SZ) `because` Refl
        === SPos (SS sn) %+ (SNeg1 (SS (SZ %+ SZ)))
            `because` (plusCongR (SPos (SS sn))
                      $ cong (Proxy :: Proxy 'Neg1)
                      $ cong (Proxy :: Proxy 'S)
                      $ Nat.plusZeroR SZ)
        === SPos (SS sn) %+ (SNeg1 SZ %+ SNeg1 SZ)
            `because` plusCongR (SPos (SS sn)) (sym $ lemma2 SZ SZ)
      where
        lemma1 :: Sing (p :: Nat)
              -> 'Pos ('S p) + 'Neg1 'Z :~: 'Pos p 
        lemma1 _ = Refl

        lemma2 :: Sing (p :: Nat)
               -> Sing (q :: Nat)
               -> 'Neg1 p + 'Neg1 q :~: 'Neg1 ('S (p + q))
        lemma2 _ _ = Refl
    plusAssocNegOnePN (SS sn) (SS sm) =
        start ((SPos (SS sn) %+ SNeg1 (SS sm)) %+ SNeg1 SZ)
        === (SPos sn %+ SNeg1 sm) %+ SNeg1 SZ `because` plusCongL (lemma1 sn sm) (SNeg1 SZ)
        === SPos sn %+ (SNeg1 sm %+ SNeg1 SZ) `because` plusAssocNegOnePN sn sm
        === SPos sn %+ (SNeg1 (SS (sm %+ SZ))) `because` plusCongR (SPos sn) (lemma2 sm SZ)
        === SPos sn %+ SNeg1 (SS sm)
            `because` (plusCongR (SPos sn)
                      $ cong (Proxy :: Proxy 'Neg1)
                      $ cong (Proxy :: Proxy 'S)
                      $ Nat.plusZeroR sm)
        === SPos (SS sn) %+ SNeg1 (SS (SS sm)) `because` sym (lemma1 sn (SS sm))
        === SPos (SS sn) %+ (SNeg1 (SS sm) %+ SNeg1 SZ)
            `because` (plusCongR (SPos (SS sn))
                      $ negOneLemma (SS sm))
      where
        lemma1 :: Sing (p :: Nat)
              -> Sing (q :: Nat)
              -> 'Pos ('S p) + 'Neg1 ('S q) :~: 'Pos p + 'Neg1 q
        lemma1 _ _ = Refl

        lemma2 :: Sing (p :: Nat)
               -> Sing (q :: Nat)
               -> 'Neg1 p + 'Neg1 q :~: 'Neg1 ('S (p + q))
        lemma2 _ _ = Refl

    plusAssocNegOneNP :: Sing (n :: Nat)
                      -> Sing (m :: Nat)
                      -> ('Neg1 n + 'Pos m) + 'Neg1 'Z :~: 'Neg1 n + ('Pos m + 'Neg1 'Z)
    plusAssocNegOneNP sn sm =
        start ((SNeg1 sn %+ SPos sm) %+ SNeg1 SZ)
        === (SPos sm %+ SNeg1 sn) %+ SNeg1 SZ
            `because` plusCongL (plusComm (SNeg1 sn) (SPos sm)) (SNeg1 SZ)
        === SPos sm %+ (SNeg1 sn %+ SNeg1 SZ)
            `because` plusAssocNegOnePN sm sn
        === SPos sm %+ SNeg1 (SS sn)
            `because` plusCongR (SPos sm) (sym $ negOneLemma sn)
        === SNeg1 (SS sn) %+ SPos sm
            `because` plusComm (SPos sm) (SNeg1 (SS sn))
        === (SNeg1 sn %+ SNeg1 SZ) %+ SPos sm
            `because` plusCongL (negOneLemma sn) (SPos sm)
        === SNeg1 sn %+ (SNeg1 SZ %+ SPos sm)
            `because` plusAssocPos (SNeg1 sn) (SNeg1 SZ) sm
        === SNeg1 sn %+ (SPos sm %+ SNeg1 SZ)
            `because` plusCongR (SNeg1 sn) (plusComm (SNeg1 SZ) (SPos sm))

    plusAssocNegOneNN :: Sing (n :: Nat)
                      -> Sing (m :: Nat)
                      -> ('Neg1 n + 'Neg1 m) + 'Neg1 'Z :~: 'Neg1 n + ('Neg1 m + 'Neg1 'Z)
    plusAssocNegOneNN sn sm =
        start ((SNeg1 sn %+ SNeg1 sm) %+ SNeg1 SZ)
        === SNeg1 (SS (sn %+ sm)) %+ SNeg1 SZ `because` plusCongL (lemma1 sn sm) (SNeg1 SZ)
        === SNeg1 (SS ((SS (sn %+ sm)) %+ SZ)) `because` lemma1 (SS (sn %+ sm)) SZ
        === SNeg1 (SS (SS (sn %+ sm)))
            `because` lemma2 (Nat.plusZeroR (SS (sn %+ sm)))
        === SNeg1 (SS (sn %+ SS sm))
            `because` lemma2 (sym $ Nat.plusSuccR sn sm)
        === SNeg1 sn %+ SNeg1 (SS sm) `because` sym (lemma1 sn (SS sm))
        === SNeg1 sn %+ SNeg1 (SS (sm %+ SZ))
            `because` plusCongR (SNeg1 sn) (lemma2 (sym $ Nat.plusZeroR sm))
        === SNeg1 sn %+ (SNeg1 sm %+ SNeg1 SZ)
            `because` plusCongR (SNeg1 sn) (sym $ lemma1 sm SZ)
      where
        lemma1 :: Sing (p :: Nat)
               -> Sing (q :: Nat)
               -> 'Neg1 p + 'Neg1 q :~: 'Neg1 ('S (p + q))
        lemma1 _ _ = Refl

        lemma2 :: a :~: b
               -> 'Neg1 ('S a) :~: 'Neg1 ('S b)
        lemma2 = cong (Proxy :: Proxy 'Neg1) . cong (Proxy :: Proxy 'S)

{-
   ASSOCIATIVITY OF MULTIPLICATION
-}
multAssoc :: Sing (a :: Zahlen)
          -> Sing (b :: Zahlen)
          -> Sing (c :: Zahlen)
          -> (a * b) * c :~: a * (b * c)
multAssoc = undefined

--class IsCommutativeRing z where
--  type Zero' :: z
--  type One' :: z
--  type Inv (m :: z) :: z
--
--  oneIsNotZero :: One' :~: Zero' -> Void
--  associativity
--    :: forall x y z. Sing x
--    -> Sing y
--    -> Sing z
--    -> (x + y) + z :~: x + (y + z)
--  commutativity
--    :: forall x y. Sing x
--    -> Sing y
--    -> x + y :~: y + z
--  distr
--    :: forall x y z. Sing x
--    -> Sing y
--    -> Sing z
--    -> (x * (y + z)) :~: ((x * y) + (x * z))
--  zeroNeutral
--    :: forall x. Sing x
--    -> x + Zero' :~: x
--  oneNeutral
--    :: forall x. Sing x
--    -> x * One' :~: x
--  inverseAxiom
--    :: forall x. Sing x
--    -> (x + Inv x) :~: Zero'
-- end TODO

--class IsCommutativeRing z => IsInteger z where
--  type Signum (m :: z) :: Sign
--  type Absolute'' (m :: z) :: Nat
--
--  zeroEquality :: (Absolute'' x ~ Absolute'' y, Absolute'' x ~ 'Z) => x :~: y
--  zeroEquality = unsafeCoerce Refl
--  zeroEquality' :: Absolute'' x :~: Absolute'' y -> Absolute'' x :~: 'Z -> x :~: y
--  zeroEquality' Refl Refl = unsafeCoerce Refl

--  zeroIdentity :: forall x m. Absolute'' x :~: 'Z -> x + m :~: m
--  zeroIdentity = Refl

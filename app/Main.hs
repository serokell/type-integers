{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
module Main (main) where

import Data.Singletons
import Data.Singletons.Prelude
import Data.Type.Natural (Nat (..), SNat (..))
import qualified Data.Type.Natural.Class.Arithmetic as Nat
import Data.Typeable

import Data.Proxy (Proxy (Proxy))
import Proof.Equational

import Data.Type.Zahlen.Class.Arithmetic
import Data.Type.Zahlen.Definitions

type Zero = 'Pos 'Z
type One  = 'Pos ('S 'Z)

sOne = SPos (SS SZ)
sZero = SPos SZ

plusAssoc :: forall a b c.
             Sing (a :: Zahlen)
          -> Sing (b :: Zahlen)
          -> Sing (c :: Zahlen)
          -> (a + b) + c :~: a + (b + c)
plusAssoc sa sb = \case
   SPos sn  -> plusAssocPos sa sb sn
   SNeg1 sn -> plusAssocNeg1 sa sb sn

plusAssocPos :: Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> Sing (n :: Nat)
             -> (a + b) + 'Pos n :~: a + (b + 'Pos n)
plusAssocPos sa sb SZ =
    start ((sa %+ sb) %+ sZero)
    === sa %+ sb `because` zeroIdR (sa %+ sb)
    === sa %+ (sb %+ sZero) `because` plusCongR sa (sym (zeroIdR sb))
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

oneLemma :: forall n. Sing (n :: Nat)
         -> 'Pos ('S n) :~: 'Pos n + One
oneLemma sn =
    start (SPos (SS sn))
      === SPos (sn %+ SS SZ) `because` cong (Proxy :: Proxy 'Pos) oneLemmaNat
      === SPos sn %+ SPos (SS SZ) `because` Refl
  where
    oneLemmaNat :: 'S n :~: n + 'S 'Z
    oneLemmaNat =
        start (SS sn)
        === SS (sn %+ SZ)
            `because` cong (Proxy :: Proxy 'S) (sym (Nat.plusZeroR sn))
        === sn %+ SS SZ
            `because` sym (Nat.plusSuccR sn SZ)

plusAssocOne :: Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> (a + b) + One :~: a + (b + One)
plusAssocOne = undefined

plusAssocPP :: forall n m. Sing (n :: Nat)
            -> Sing (m :: Nat)
            -> ('Pos n + 'Pos m) + One :~: 'Pos n + ('Pos m + One)
plusAssocPP sn sm =
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

plusAssocPN :: Sing (n :: Nat)
            -> Sing (m :: Nat)
            -> ('Pos n + 'Neg1 m) + 'Pos ('S 'Z) :~: 'Pos n + ('Neg1 m + 'Pos ('S 'Z))
plusAssocPN sn sm = undefined

plusAssocNP :: Sing (n :: Nat)
            -> Sing (m :: Nat)
            -> ('Neg1 n + 'Pos m) + 'Pos ('S 'Z) :~: 'Neg1 n + ('Pos m + 'Pos ('S 'Z))
plusAssocNP sn sm = undefined

plusAssocNN :: Sing (n :: Nat)
            -> Sing (m :: Nat)
            -> 'Neg1 n + 'Neg1 m + 'Pos ('S 'Z) :~: 'Neg1 (n + m)
plusAssocNN sn sm =
    start (SNeg1 sn %+ SNeg1 sm %+ sOne)
    === SNeg1 (SS (sn %+ sm)) %+ sOne
        `because` Nat.plusCongL (negLemma sn sm) sOne
    === sOne %+ SNeg1 (SS (sn %+ sm)) `because` Refl
    === sZero %+ SNeg1 (sn %+ sm) `because` Refl
    === SNeg1 (sn %+ sm) `because` zeroIdL (SNeg1 (sn %+ sm))
  where
    negLemma :: Sing (p :: Nat)
             -> Sing (q :: Nat)
             -> 'Neg1 p + 'Neg1 q :~: 'Neg1 (S (p + q))
    negLemma _ _ = Refl

plusAssocNeg1 :: forall a b n.
                Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> Sing (n :: Nat)
             -> (a + b) + 'Neg1 n :~: a + (b + 'Neg1 n)
plusAssocNeg1 = undefined

main :: IO ()
main = putStrLn "Hello, World!\n"

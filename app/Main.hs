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
plusAssocOne sa sb = case (sa, sb) of
    (SPos sn, SPos sm)   -> plusAssocPP sn sm
    (SPos sn, SNeg1 sm)  -> plusAssocPN sn sm
    (SNeg1 sn, SPos sm)  -> plusAssocNP sn sm
    (SNeg1 sn, SNeg1 sm) -> plusAssocNN sn sm

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
            -> ('Pos n + 'Neg1 m) + One :~: 'Pos n + ('Neg1 m + One)
plusAssocPN SZ sm =
    start ((sZero %+ SNeg1 sm) %+ sOne)
      === SNeg1 sm %+ sOne `because` Nat.plusCongL (zeroIdL (SNeg1 sm)) sOne
      === sZero %+ (SNeg1 sm %+ sOne) `because` (sym $ zeroIdL (SNeg1 sm %+ sOne))
plusAssocPN (SS sn) SZ =
    start ((SPos (SS sn) %+ SNeg1 SZ) %+ sOne)
    === SPos sn %+ sOne `because` plusCongL (lemma sn) sOne
    === SPos (SS sn) `because` sym (oneLemma sn)
    === SPos (SS sn) %+ sZero `because` sym (zeroIdR (SPos (SS sn)))
    === SPos (SS sn) %+ (sOne %+ SNeg1 SZ)
        `because` plusCongR (SPos (SS sn)) (sym (lemma SZ))
    === SPos (SS sn) %+ (SNeg1 SZ %+ sOne)
        `because` plusCongR (SPos (SS sn)) (plusComm sOne (SNeg1 SZ))
  where
    lemma :: Sing p -> 'Pos ('S p) + 'Neg1 'Z :~: 'Pos p
    lemma _ = Refl
plusAssocPN (SS sn) (SS SZ) =
    start ((SPos (SS sn) %+ SNeg1 (SS SZ)) %+ sOne)
    === (SPos sn %+ SNeg1 SZ) %+ sOne `because` plusCongL (lemma1 sn) sOne
    === SPos sn %+ (SNeg1 SZ %+ sOne) `because` plusAssocPN sn SZ
    === SPos sn %+ (sOne %+ SNeg1 SZ)
        `because` plusCongR (SPos sn) (plusComm (SNeg1 SZ) sOne)
    === SPos sn %+ sZero
        `because` plusCongR (SPos sn) lemma2
    === SPos sn
        `because` zeroIdR (SPos sn)
    === SPos (SS sn) %+ SNeg1 SZ
        `because` sym (lemma3 sn)
    === SPos (SS sn) %+ (sZero %+ SNeg1 SZ)
        `because` plusCongR (SPos (SS sn)) (zeroIdL (SNeg1 SZ))
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
plusAssocPN (SS sn) (SS (SS sm)) =
    start ((SPos (SS sn) %+ SNeg1 (SS (SS sm))) %+ sOne)
    === (SPos sn %+ SNeg1 (SS sm)) %+ sOne `because` Refl
    === SPos sn %+ (SNeg1 (SS sm) %+ sOne) `because` plusAssocPN sn (SS sm)
    === SPos sn %+ (sOne %+ SNeg1 (SS sm)) `because` Refl
    === SPos sn %+ (sZero %+ SNeg1 sm) `because` Refl
    === SPos sn %+ SNeg1 sm `because` plusCongR (SPos sn) (zeroIdL (SNeg1 sm))
    === SPos (SS sn) %+ SNeg1 (SS sm) `because` Refl
    === SPos (SS sn) %+ (sZero %+ SNeg1 (SS sm))
        `because` plusCongR (SPos (SS sn)) (zeroIdL (SNeg1 (SS sm)))
    === SPos (SS sn) %+ (sOne %+ SNeg1 (SS (SS sm)))
        `because` plusCongR (SPos (SS sn)) (lemma (SS sm))
    === SPos (SS sn) %+ (SNeg1 (SS (SS sm)) %+ sOne)
        `because` plusCongR (SPos (SS sn)) (plusComm sOne (SNeg1 (SS (SS sm))))
  where
    lemma :: Sing (p :: Nat) -> 'Pos 'Z + 'Neg1 p :~: 'Pos ('S 'Z) + 'Neg1 ('S p) 
    lemma _ = Refl

plusAssocNP :: forall n m.
               Sing (n :: Nat)
            -> Sing (m :: Nat)
            -> ('Neg1 n + 'Pos m) + 'Pos ('S 'Z) :~: 'Neg1 n + ('Pos m + 'Pos ('S 'Z))
plusAssocNP sn sm = trans part1 part2
  where
    part1 :: ('Neg1 n + 'Pos m) + 'Pos ('S 'Z) :~: 'Pos m + ('Neg1 n + 'Pos ('S 'Z))
    part1 =
        start ((SNeg1 sn %+ SPos sm) %+ sOne)
        === (SPos sm %+ SNeg1 sn) %+ sOne
            `because` plusCongL (plusComm (SNeg1 sn) (SPos sm)) sOne
        === SPos sm %+ (SNeg1 sn %+ sOne) `because` plusAssocPN sm sn

    part2 :: 'Pos m + ('Neg1 n + One) :~: 'Neg1 n + ('Pos m + One)
    part2 = case sn of
        SZ    ->
            start (SPos sm %+ (SNeg1 SZ %+ sOne))
            === SPos sm %+ (sOne %+ SNeg1 SZ)
                `because` plusCongR (SPos sm) (plusComm (SNeg1 SZ) sOne)
            === SPos sm %+ sZero `because` Refl
            === SPos sm `because` zeroIdR (SPos sm)
            === SPos (SS sm) %+ SNeg1 SZ `because` Refl
            === SNeg1 SZ %+ SPos (SS sm)
                `because` plusComm (SPos (SS sm)) (SNeg1 SZ)
            === SNeg1 SZ %+ (SPos sm %+ sOne)
                `because` plusCongR (SNeg1 SZ) (oneLemma sm)
        SS sp ->
            start (SPos sm %+ (SNeg1 (SS sp) %+ sOne))
            === SPos sm %+ (SNeg1 sp %+ sZero) `because` Refl
            === SPos sm %+ SNeg1 sp
                `because` plusCongR (SPos sm) (zeroIdR (SNeg1 sp))
            === SPos (SS sm) %+ SNeg1 (SS sp) `because` Refl
            === SNeg1 (SS sp) %+ SPos (SS sm)
                `because` plusComm (SPos (SS sm)) (SNeg1 (SS sp))
            === SNeg1 (SS sp) %+ (SPos sm %+ sOne)
                `because` plusCongR (SNeg1 (SS sp)) (oneLemma sm)

plusAssocNN :: forall n m.
               Sing (n :: Nat)
            -> Sing (m :: Nat)
            -> 'Neg1 n + 'Neg1 m + One :~: 'Neg1 n + ('Neg1 m + One)
plusAssocNN sn sm = trans part1 part2
  where
    part1 :: 'Neg1 n + 'Neg1 m + One :~: 'Neg1 (n + m)
    part1 =
        start (SNeg1 sn %+ SNeg1 sm %+ sOne)
        === SNeg1 (SS (sn %+ sm)) %+ sOne
            `because` Nat.plusCongL (lemma sn sm) sOne
        === sOne %+ SNeg1 (SS (sn %+ sm)) `because` Refl
        === sZero %+ SNeg1 (sn %+ sm) `because` Refl
        === SNeg1 (sn %+ sm) `because` zeroIdL (SNeg1 (sn %+ sm))
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
            === SNeg1 sn %+ sZero `because` zeroIdR (SNeg1 sn)
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
                `because` plusCongR (SNeg1 sn) (zeroIdL (SNeg1 sp))
            === SNeg1 sn %+ (sOne %+ SNeg1 (SS sp))
                `because` plusCongR (SNeg1 sn) (lemma SZ sp)
            === SNeg1 sn %+ (SNeg1 (SS sp) %+ sOne)
                `because` plusCongR (SNeg1 sn) (plusComm sOne (SNeg1 (SS sp)))
          where
            lemma :: Sing (k :: Nat)
                  -> Sing (l :: Nat)
                  -> 'Pos k + 'Neg1 l :~: 'Pos ('S k) + 'Neg1 ('S l)
            lemma sk sl = Refl

plusAssocNeg1 :: forall a b n.
                Sing (a :: Zahlen)
             -> Sing (b :: Zahlen)
             -> Sing (n :: Nat)
             -> (a + b) + 'Neg1 n :~: a + (b + 'Neg1 n)
plusAssocNeg1 = undefined

main :: IO ()
main = putStrLn "Hello, World!\n"

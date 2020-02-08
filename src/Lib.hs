-- {-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes#-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses#-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes#-}
{-# LANGUAGE PartialTypeSignatures #-}

module Lib where

--import Data.Promotion.Prelude.Enum
import Data.Type.Natural hiding (induction, plusSuccL, plusSuccR)
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable
import Data.Type.Equality
import Proof.Equational

import Unsafe.Coerce

import Data.Kind                    (Type, Constraint)

$(singletons [d|
  data Zahlen = Pos Nat | Neg Nat
    deriving (Show, Eq)
  |])

deriving instance Typeable 'Neg
deriving instance Typeable 'Pos

singletons [d|
  data Sign = P | N
    deriving (Show, Eq)

  opposite
    :: Sign
    -> Sign
  opposite P = N
  opposine N = P

  signZ
    :: Zahlen
    -> Zahlen
  signZ (Pos (S n)) = Pos (S Z)
  signZ (Neg (S n)) = Neg (S Z)
  signZ (Pos Z) = Pos Z
  signZ (Neg Z) = Pos Z

  signOf
    :: Zahlen
    -> Sign
  signOf (Pos _) = P
  singOf (Neg _) = N

  signMult
    :: Sign
    -> Sign
    -> Sign
  signMult P s2 = s2
  signMult N s2 = opposite N

  signToZ
    :: Sign
    -> Nat
    -> Zahlen
  signToZ P = Pos
  signToZ N = Neg
  |]

singletons [d|

  absolute'
    :: Zahlen
    -> Nat
  absolute' (Pos n) = n
  absolute' (Neg n) = n

  absolute
    :: Zahlen
    -> Zahlen
  absolute (Pos n) = Pos n
  absolute (Neg n) = Pos n

  inverse
    :: Zahlen
    -> Zahlen
  inverse (Pos n) = Neg n
  inverse (Neg n) = Pos n
  |]

singletons [d|
  instance Ord Zahlen where
    Pos n <= Pos m = n <= m
    Neg _ <= Pos _ = True
    Neg n <= Neg m = m <= n
    Pos _ <= Neg _ = False
  |]

singletons [d|
  instance Enum Zahlen where
    fromEnum (Pos n) = fromEnum n
    fromEnum (Neg n) = -1 * fromEnum n

    toEnum n =
      case (n >= 0) of
        True ->  Pos $ toEnum n
        False -> Neg $ toEnum n
  |]

singletons [d|
  sub
    :: Nat
    -> Nat
    -> Zahlen
  sub m Z = Pos m
  sub Z (S n) = Neg (S n)
  sub (S m) (S n) = m `sub` n
  |]

singletons [d|
  instance Num Zahlen where
    Neg m + Neg n = Neg (m + n)
    Pos m + Pos n = Pos (m + n)
    Pos m + Neg (S n) = m `sub` S n
    Neg (S m) + Pos n = n `sub` S m

    n * m = case (signOf n, signOf m) of
      (s1, s2) -> signToZ (s1 `signMult` s2) prodNat
      where
        prodNat = absolute' n * absolute' m

    abs = absolute

    signum = signZ

    negate = inverse

    fromInteger n =
      case (n >= 0) of
        True -> Pos $ fromInteger n
        False -> Neg $ fromInteger n
  |]

newtype IdentityR op e n = IdentityR { idRProof :: Apply (op n) e :~: n }
newtype IdentityL op e n = IdentityL { idLProof :: Apply (op e) n :~: n }

class IsCommutativeRing z where
  type Zero' :: z
  type One' :: z
  type Inv (m :: z) :: z

  oneIsNotZero :: One' :~: Zero' -> Void
  associativity
    :: forall x y z. Sing x
    -> Sing y
    -> Sing z
    -> (x + y) + z :~: x + (y + z)
  commutativity
    :: forall x y. Sing x
    -> Sing y
    -> x + y :~: y + z
  distr
    :: forall x y z. Sing x
    -> Sing y
    -> Sing z
    -> (x * (y + z)) :~: ((x * y) + (x * z))
  zeroNeutral
    :: forall (x :: z). Sing x
    -> Zero' + x :~: x
  oneNeutral
    :: forall x. Sing x
    -> x * One' :~: x
  inverseAxiom
    :: forall x. Sing x
    -> (x + Inv x) :~: Zero'
  induction  :: forall k p. p (Zero')
             -> (forall (n :: z). ((n >= Zero') ~ 'True) => Sing n -> p n -> p (Succ n))
             -> (forall (n :: z). ((n >= Zero') ~ 'True) => Sing (Inv n) -> p n -> p (Inv n))
             -> Sing k -> p k

instance IsCommutativeRing Zahlen where
  type Zero' = ('Pos 'Z)
  type One' = ('Pos (S Z))
  type Inv m = Inverse m
  zeroNeutral :: Sing (m :: Zahlen) -> Zero' + m :~: m
  zeroNeutral sm = idLProof $ induction base step neg sm where
    base :: PlusZeroL (Zero' :: Zahlen)
    base = IdentityL $ zeroNeutral (SPos SZ)

    step :: forall (n :: Zahlen). ((n >= Zero') ~ 'True) => Sing n -> PlusZeroL n -> PlusZeroL (Succ n)
    step sn (IdentityL ih) = IdentityL $
            start (Proxy @(Zero' + Succ n))
              === Proxy @(Succ (Zero' + n))  `because` undefined (Proxy @Zero') (Proxy @n)
              === Proxy @(Succ n)            `because` succCong ih

    neg :: forall (n :: Zahlen). ((n >= Zero') ~ 'True) => Sing (Inv n) -> PlusZeroL n -> PlusZeroL (Inv n)
    neg sInv (IdentityL ih) = IdentityL $
         start (Proxy @(Zero' + Inv n))
           === Proxy @(Inv n) `because` zeroNeutral sInv
--   zeroIdentity :: forall x m. Absolute'' x :~: 'Z -> x + m :~: m
--   zeroIdentity Refl = Refl `because` (Proxy )
  induction base _ _ (SPos SZ) = base
  induction base step neg (SPos (SS n)) = undefined $ (induction base step neg (SPos n))

type PlusZeroR (n :: k) = IdentityR (+@#@$$) (Zero') n
type PlusZeroL (n :: k) = IdentityL (+@#@$$) (Zero') n
newtype PlusSuccL (m :: k) =
  PlusSuccL { plusSuccLProof :: forall n. Proxy n -> Succ n + m :~: Succ (n + m) }
newtype PlusSuccR (n :: k) =
  PlusSuccR { plusSuccRProof :: forall m. Proxy m -> n + Succ m :~: Succ (n + m) }

succCong :: n :~: m -> Succ n :~: Succ m
succCong Refl = Refl

class IsCommutativeRing z => IsInteger z where
  type Signum (m :: z) :: Sign
  type Absolute'' (m :: z) :: Nat

  zeroEquality :: (Absolute'' x ~ Absolute'' y, Absolute'' x ~ 'Z) => x :~: y
  zeroEquality = unsafeCoerce Refl
  zeroEquality' :: Absolute'' x :~: Absolute'' y -> Absolute'' x :~: 'Z -> x :~: y
  zeroEquality' Refl Refl = unsafeCoerce Refl

  {- zeroIdentityL :: forall (m :: z) (x :: z). x ~ Zero' => Sing m -> Zero' + m :~: m
  zeroIdentityL sm = idLProof $ induction base step neg sm where 
    base :: PlusZeroL x
    base = IdentityL $ zeroIdentityR (SPos SZ)
    
    step :: forall (n :: z). Sing n -> PlusZeroL n -> PlusZeroL (Succ n)
    step sn (IdentityL ih) = IdentityL $
            start (Proxy @(Zero' + Succ n))
              === Proxy @(Succ (Zero' + n)) `because` plusSuccR (Proxy @Zero') (Proxy @n)
              === Proxy @(Succ n)            `because` succCong ih

    neg :: forall (n :: z). Sing (Inv n) -> PlusZeroL n -> PlusZeroL (Inv n)
    neg sInv (IdentityL ih) = IdentityL $ 
            start (Proxy @(Zero' + Inv n)) 
            === Proxy @(Inv n) `because` zeroIdentityL sInv
--           === Proxy @(Inv (Zero' + Inv n)) `because` plusSuccR (Proxy @Zero') (Proxy @(Inv n))
--           === Proxy @(Inv n)               `because` succCong ih
  
  zeroIdentityR :: forall (m :: z) (x :: z). x ~ Zero' => Sing m -> m + Zero' :~: m
  zeroIdentityR sm = idRProof $ induction base step neg sm where -- Refl ---start (Proxy :: Proxy (x + m)) === undefined 
    base :: PlusZeroR x
    base = IdentityR $ zeroIdentityL (SPos SZ)
    
    step :: Sing n -> PlusZeroR n -> PlusZeroR (Succ n)
    step = undefined 

    neg :: Sing (Inv n) -> PlusZeroR n -> PlusZeroR (Inv n)
    neg = undefined

  plusSuccL :: forall n m. Proxy n -> Proxy m -> Succ n + m :~: Succ (n + m :: z)
  plusSuccL pn pm = plusSuccLProof (induction base step neg (_ :: Sing m)) pn
    where
      base :: PlusSuccL (Zero' :: z)
      base = PlusSuccL $ \(p :: Proxy n1) ->
          start (Proxy @(Succ n1 + Zero')) 
            === (Proxy @(Succ n1)) `because` zeroIdentityR (Proxy @(Succ n1))
            === (Proxy @(Succ (n1 + Zero'))) `because` succCong (sym $ zeroIdentityR p)

      step :: forall (n :: z). PlusSuccL n -> PlusSuccL (Succ n)
      step (PlusSuccL ih) = PlusSuccL $ \sn -> undefined {-
        start (sS sn %+ sS sm)
        === sS (sS sn %+ sm)   `because` plusSuccR (sS sn) sm
        === sS (sS (sn %+ sm)) `because` succCong (ih sn)
        === sS (sn %+ sS sm)   `because` succCong (sym $ plusSuccR sn sm)-}
      
      neg :: forall (n :: z). PlusSuccL n -> PlusSuccL (Inv n)
      neg = undefined

  plusSuccR :: forall n m. Proxy n -> Proxy m -> n + Succ m :~: Succ (n + m :: z)
  plusSuccR pn pm = plusSuccRProof (induction base step neg (_ :: Sing n)) pm
    where
      base :: PlusSuccR (Zero' :: z)
      base = PlusSuccR $ \(p :: Proxy m1) ->
        start (Proxy @(Zero' + Succ m1))
          === (Proxy @(Succ m1)) `because` zeroIdentityL (Proxy @(Succ m1))
          ===  Proxy @(Succ (Zero' + m1)) `because` succCong (sym $ zeroIdentityL p)

      step :: forall (n :: z). PlusSuccR n -> PlusSuccR (Succ n)
      step (PlusSuccR ih) = undefined {- PlusSuccR $ \sk ->
        start (sS sn %+ sS sk)
        === sS (sn %+ sS sk)    `because` plusSuccL sn (sS sk)
        === sS (sS (sn %+ sk))  `because` succCong (ih sk)
        === sS (sS sn %+ sk)    `because` succCong (sym $ plusSuccL sn sk) -} 
      neg :: forall (n :: z). PlusSuccR n -> PlusSuccR (Inv n)
      neg = undefined -}

instance IsInteger Zahlen where
  type Signum ('Pos n) = P
  type Signum ('Neg n) = N
  type Absolute'' (_ n) = n
--  zeroIdentity Refl = undefined --start (Proxy :: Proxy (x + m)) === undefined 

natToZ :: Sing n -> Sing (Pos n)
natToZ SZ = SPos SZ
natToZ (SS n) = SPos (SS n)

zToNat :: Sing (Pos n) -> Sing n
zToNat (SPos n) = n

zToNatNeg :: Sing (Neg n) -> Sing n
zToNatNeg (SNeg n) = n

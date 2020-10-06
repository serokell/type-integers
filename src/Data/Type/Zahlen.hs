{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Type.Zahlen
    ( module Data.Type.Zahlen.Class
    , module Data.Type.Zahlen.Definitions
    ) where

import Data.Type.Natural (Nat (S, Z))

import Data.Type.Zahlen.Class
import Data.Type.Zahlen.Definitions

--instance IsCommutativeRing Zahlen where
--  type Zero' = ('Pos 'Z)
--  type One' = ('Pos (S Z))
--  type Inv m = Inverse m
--   zeroIdentity :: forall x m. Absolute'' x :~: 'Z -> x + m :~: m
--   zeroIdentity Refl = Refl `because` (Proxy )

--instance IsInteger Zahlen where
--  type Signum ('Pos m) = P
--  type Signum ('Neg m) = N
--  type Absolute'' (_ m) = m

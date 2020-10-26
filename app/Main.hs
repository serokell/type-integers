{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
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

main :: IO ()
main = putStrLn "Hello, World!\n"

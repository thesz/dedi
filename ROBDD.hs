-- |ROBDD.hs
--
-- Naive implementation of reduced ordered binary decision diagrams.
--
-- Copyright (C) 2022 Serguey Zefirov
module ROBDD where

import Control.Monad
import Control.Monad.State

import Data.Bits

import qualified Data.List as List

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Word

data ID = ID !Int
	deriving (Eq, Ord, Show)

id0, id1 :: ID
id0 = ID 0
id1 = ID 1

type Var = Word32
type OVar = Word64

data IDP = IDP !OVar !ID !ID
	deriving (Eq, Ord, Show)


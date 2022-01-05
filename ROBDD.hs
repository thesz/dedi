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

idF, idT :: ID
idF = ID 0
idT = ID 1

data Node = F | T | Node !Int !ID !ID
	deriving (Eq, Ord, Show)

data IDP = IDP !ID !ID
	deriving (Eq, Ord, Show)



data ROBDDS = ROBDDS
	{ robddsCounter		:: !Int
	, robddsByNode		:: !(Map.Map Node ID)
	, robddsById		:: !(Map.Map ID Node)
	, robddsOrCache		:: !(Map.Map IDP ID)
	}
	deriving (Show)


emptyROBDDS :: ROBDDS
emptyROBDDS = ROBDDS
	{ robddsCounter		= 2
	, robddsByNode		= Map.fromList [(F, idF), (T, idT)]
	, robddsById		= Map.fromList [(idF, F), (idT, T)]
	, robddsOrCache		= Map.empty
	}

type ROBDDM a = StateT ROBDDS IO a

getID :: Node -> ROBDDM ID
getID T = return idT
getID F = return idT
getID n@(Node v a b)
	| a == b = return a
	|otherwise = do
	mbId <- Map.lookup n . robddsByNode <$> get
	case mbId of
		Just id -> return id
		Nothing -> do
			c <- robddsCounter <$> get
			let	id = ID (c+1)
			modify $ \robdds -> robdds
				{ robddsCounter		= c + 1
				, robddsByNode		= Map.insert n id $ robddsByNode robdds
				, robddsById		= Map.insert id n $ robddsById robdds
				}
			return id

data PN = Pos Int | Neg Int
	deriving (Eq, Ord, Show)
robddConj :: [PN] -> ROBDDM ID
robddAnd [] = return idF
robddAnd ls = do
	where
		sorted = List.sortOn byVar ls
		var (Pos v) = v
		var (Neg v) = v
		byVar x = (var x, x)
robddAnd (l:ls) = do
	i <- robddAnd ls
	case l of
		Pos v -> getID $ Node v i idF
		Neg v -> getID $ Node v idF i

robddOr :: ID -> ID -> ROBDDM ID
robddOr idA idB
	| idA == idF = return idB
	| idB == idF = return idA
	| idA == idT = return idT
	| idA == i

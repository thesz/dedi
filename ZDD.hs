-- |ZDD.hs
--
-- Naive ZDD implementation.
--
-- Node must have IDs that point to nodes with smaller variables.
--
-- Copyright (C) 2021 Serguey Zefirov
module ZDD where

import Control.Monad
import Control.Monad.State

import Data.Bits

import qualified Data.List as List

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Word

data ID = ID Int
	deriving (Eq, Ord, Show)

id0, id1 :: ID
id0 = ID 0
id1 = ID 1

data ZDDN = Empty | One | Node !Int !ID !ID -- Node var present absent
	deriving (Eq, Ord, Show)

data IDP = IDP !ID !ID
	deriving (Eq, Ord, Show)

data ZDDS = ZDDS
	{ zddsCounter		:: !Int
	, zddsByID		:: !(Map.Map ID ZDDN)
	, zddsByNode		:: !(Map.Map ZDDN ID)
	, zddsByVar		:: !(Map.Map Int (Set.Set ID))
	, zddsReferredBy	:: !(Map.Map ID (Set.Set ID))
	, zddsUnionCache
	, zddsDiffCache
	, zddsDistributeCache
	, zddsIntersectCache	:: !(Map.Map IDP ID)
	}
	deriving (Show)

emptyZDDS :: ZDDS
emptyZDDS = ZDDS
	{ zddsCounter		= 2
	, zddsByID		= Map.fromList [(id0, Empty), (id1, One)]
	, zddsByNode		= Map.fromList [(Empty, id0), (One, id1)]
	, zddsByVar		= Map.empty
	, zddsReferredBy	= Map.empty
	, zddsUnionCache	= Map.empty
	, zddsDiffCache		= Map.empty
	, zddsDistributeCache	= Map.empty
	, zddsIntersectCache	= Map.empty
	}

type ZDDM a = StateT ZDDS IO a

getID :: ZDDN -> ZDDM ID
getID Empty = return id0
getID One = return id1
getID node@(Node var p a)
	| p == id0 = return a
	| otherwise = do
		mbID <- Map.lookup node . zddsByNode <$> get
		case mbID of
			Just id -> return id
			Nothing -> do
				zdds <- get
				let	new = zddsCounter zdds
					newID = ID new
				when True $ do
					let check i = do
						when (i /= id0 && i /= id1) $ do
							Node v' _ _ <- fetchNode i
							when (v' >= var) $ error "variable ordering has been violated"
					check p
					check a
				put $ zdds
					{ zddsCounter = new + 1
					, zddsByID = Map.insert newID node $ zddsByID zdds
					, zddsByNode = Map.insert node newID $ zddsByNode zdds
					, zddsByVar = Map.insertWith Set.union var (Set.singleton newID) $
						zddsByVar zdds
					, zddsReferredBy = Map.insertWith Set.union p (Set.singleton newID) $
							Map.insertWith Set.union a (Set.singleton newID) $
							zddsReferredBy zdds
					}
				return newID

fetchNode :: ID -> ZDDM ZDDN
fetchNode id = do
	Map.findWithDefault (error "unable to find node by ID") id . zddsByID <$> get

mkSet :: [Int] -> ZDDM ID
mkSet elems' = loop id1 elems
	where
		elems = List.sort elems'
		loop id [] = return id
		loop id (v:vs) = do
			id <- getID (Node v id id0)
			loop id vs

cached :: (ZDDS -> Map.Map IDP ID, IDP -> ID -> ZDDS -> ZDDS)
	-> ID -> ID -> ZDDM ID -> ZDDM ID
cached (fetch, set) a b compute = do
	mbCached <- Map.lookup (IDP a b) . fetch <$> get
	case mbCached of
		Just result -> return result
		_ -> do
			r <- compute
			modify' $ set (IDP a b) r
			return r

displayAllSets' :: (Int -> Int) -> String -> ID -> ZDDM ()
displayAllSets' interpret msg root = do
	liftIO $ putStrLn $ msg ++ ": root "++show root++":"
	(sets, _) <- enumerate Map.empty root
	liftIO $ case sets of
		[] -> putStrLn $ "    <empty>"
		_ -> forM_ sets $ \set -> putStrLn $ "    " ++ show set
	where
		enumerate visited id
			| id == id0 = return ([], visited)
			| id == id1 = return ([[]], visited)
			| Just sets <- Map.lookup id visited = return (sets, visited)
			| otherwise = do
				Node var present absent <- fetchNode id
				(setsp, visitedp) <- enumerate visited present
				(setsa, visiteda) <- enumerate visitedp absent
				return (setsa ++ map (interpret var:) setsp, visiteda)

displayAllSets :: String -> ID -> ZDDM ()
displayAllSets = displayAllSets' id

-- |Returns the set of shortest subsets.
shortest :: ID -> ZDDM ID
shortest root = do
	(distancesTo1, rootDistance) <- computeDistances (Map.singleton id1 0) root
	(_, id) <- walk Map.empty distancesTo1 root rootDistance
	return id
	where
		walk cache distances root rootd
			| root == id1 || root == id0 = return (cache, root)
			| Just computed <- Map.lookup root cache = return (cache, computed)
			| otherwise = do
				Node var p a <- fetchNode root
				let	pd = getD p
					ad = getD a
				(cachep, p') <- if pd + 1 == rootd
					then walk cache distances p pd
					else return (cache, id0)
				(cachea, a') <- if a /= id0 && ad == rootd
					then walk cache distances a ad
					else return (cache, id0)
				id <- getID $ Node var p' a'
				return (Map.insert root id cachea, id)
			where
				getD x = Map.findWithDefault (error $ "cannot get distance "++show x) x distances
		computeDistances distances root
			| root == id1 = return (distances, 0 :: Int)
			| root == id0 = return (distances, maxBound - 1)
			| otherwise = do
				Node _ p a <- fetchNode root
				(dp, pd) <- computeDistances distances p
				let	pd1 = pd + 1
				if a == id0
					then return (Map.insert root pd1 dp, pd1)
					else do
						(da, ad) <- computeDistances dp a
						let	d = min ad pd1
						return (Map.insert root d da, d)

union :: ID -> ID -> ZDDM ID
union a b
	| a > b = union b a
	| a == b = return a
	| a == id0 = return b
	| otherwise = cached (fetch, set) a b $ do
		if a == id1
			then do
				Node var present absent <- fetchNode b
				p1 <- union present a
				a1 <- union absent a
				getID $ Node var p1 a1
			else do
				Node vara pa aa <- fetchNode a
				Node varb pb ab <- fetchNode b
				case compare vara varb of
					EQ -> do
						pab <- union pa pb
						aab <- union aa ab
						getID $ Node vara pab aab
					GT -> do
						-- we construct pseudonode Node vara id0 b
						pab <- union pa id0
						aab <- union aa b
						getID $ Node vara pab aab
					LT -> do
						-- here pseudonode is Node varb id0 a
						pab <- union id0 pb
						aab <- union a ab
						getID $ Node varb pab aab
	where
		fetch = zddsUnionCache
		set idp id zdds = zdds { zddsUnionCache = Map.insert idp id $ zddsUnionCache zdds }

intersection :: ID -> ID -> ZDDM ID
intersection a b
	| a > b = intersection b a
	| a == b = return a
	| a == id0 = return id0
	| otherwise = cached (fetch, set) a b $ do
		if a == id1
			then do
				Node _ _ absent <- fetchNode b
				intersection absent a
			else do
				Node vara pa aa <- fetchNode a
				Node varb pb ab <- fetchNode b
				case compare vara varb of
					EQ -> do
						pab <- intersection pa pb
						aab <- intersection aa ab
						getID $ Node vara pab aab
					GT -> intersection aa b
					LT -> intersection ab a
	where
		fetch = zddsIntersectCache
		set idp id zdds = zdds { zddsIntersectCache = Map.insert idp id $ zddsIntersectCache zdds }

difference :: ID -> ID -> ZDDM ID
difference a b
	| a == b = return id0
	| a == id0 = return id0
	| b == id0 = return a
	| otherwise = cached (fetch, set) a b $ do
		case (a == id1, b == id1) of
			(True, _) -> do
				Node var present absent <- fetchNode b
				difference a absent
			(_, True) -> do
				Node var present absent <- fetchNode a
				da <- difference absent b
				getID $ Node var present absent
			_ -> do
				Node vara pa aa <- fetchNode a
				Node varb pb ab <- fetchNode b
				case compare vara varb of
					EQ -> do
						pab <- difference pa pb
						aab <- difference aa ab
						getID $ Node vara pab aab
					GT -> do
						aab <- difference aa b
						getID $ Node vara pa aab
					LT -> do
						difference a ab
	where
		fetch = zddsDiffCache
		set idp id zdds = zdds { zddsDiffCache = Map.insert idp id $ zddsDiffCache zdds }

distribute :: ID -> ID -> ZDDM ID
distribute a b
	| a == b = return a
	| a > b = distribute b a
	| a == id0 = return id0
	| a == id1 = return b
	| otherwise = cached (fetch, set) a b $ do
		Node vara pa aa <- fetchNode a
		Node varb pb ab <- fetchNode b
		(var, pa, aa, pb, ab) <- case compare vara varb of
			EQ -> return (vara, pa, aa, pb, ab)
			LT -> return (varb, id0, a, pb, ab)
			GT -> return (vara, pa, aa, id0, b)
		da <- distribute aa ab
		x <- distribute pa pb
		y <- distribute aa pb
		z <- distribute pa ab
		xy <- union x y
		xyz <- union xy z
		xyz'da <- difference xyz da
		getID $ Node var xyz'da da
	where
		fetch = zddsDistributeCache
		set idp id zdds = zdds { zddsDistributeCache = Map.insert idp id $ zddsDistributeCache zdds }

usedSet :: [ID] -> ZDDM (Set.Set ID)
usedSet roots = foldM down Set.empty roots
	where
		down visited root
			| root == id0 || root == id1 || Set.member root visited = return visited
			| otherwise = do
				Node _ p a <- fetchNode root
				onP <- down (Set.insert root visited) p
				down onP a

-- | the operation "(w, wo) <- split var root" will return pair w, wo (with, without) such that
-- union (insert var w) wo === root where insert operation equips all subsets with the additional
-- element.
--
-- so bear in mind that variable is not present in either of sets.
split :: Bool -> Int -> ID -> ZDDM (ID, ID)
split withVar var root = do
	snd <$> walk Map.empty root
	where
		walk visited root
			| root == id0 || root == id1 = return (visited, (id0, root))
			| Just (IDP w wo) <- Map.lookup root visited =
				return (visited, (w, wo))
			| otherwise = do
				Node var' p a <- fetchNode root
				case compare var var' of
					EQ -> do
						w <- if withVar
							then getID $ Node var p id0
							else return p
						return (Map.insert root (IDP w a) visited, (w, a))
					GT -> do
						return (visited, (id0, root))
					LT -> do
						(visitedp, (wp, wop)) <- walk visited p
						(visiteda, (wa, woa)) <- walk visitedp a
						w <- union wp wa
						wo <- union wop woa
						return (Map.insert root (IDP w wo) visiteda, (w, wo))

t = do
	flip evalStateT emptyZDDS $ do
		s1 <- mkSet [1, 2]
		displayAllSets "s1" s1
		s2 <- mkSet [2,3]
		displayAllSets "s2" s2
		u <- union s1 s2
		displayAllSets "u" u
		d <- distribute s1 s2
		displayAllSets "d" d
		ud <- union u d
		displayAllSets "union u d" ud
		sh <- shortest ud
		displayAllSets "shortest in union u d" sh
		d1 <- difference u s1
		displayAllSets "d1=s2" d1
		d2 <- difference u s2
		displayAllSets "d2=s1" d2
		i1 <- intersection u s1
		displayAllSets "as s1" i1
		i2 <- intersection u s2
		displayAllSets "as s2" i2
		(w2, wo2) <- split True 2 u
		displayAllSets "w2" w2
		displayAllSets "wo2" wo2
		--get >>= liftIO . print


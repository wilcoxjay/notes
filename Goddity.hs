{-# LANGUAGE TupleSections #-}

module Main where

import Prelude hiding (init)
import qualified Prelude

import Control.Applicative
import Control.Monad  
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
--import Data.Tree (Tree)
--import qualified Data.Tree as Tree
-- import Data.Tree.Zipper (TreePos)
--import qualified Data.Tree.Zipper as Tree.Zipper

import Data.ListTrie.Patricia.Map (TrieMap)
import qualified Data.ListTrie.Patricia.Map as TrieMap

-- import Data.Set (Set)
-- import qualified Data.Set as Set

type Graph v e = Map v [(v, e)]

data City = Seattle | Chicago | NYC | Montreal | Burlington |
  -- LA |
  Nashville | StLouis | DC
  deriving (Eq, Ord, Show)

theGraph :: Graph City Int
theGraph =
  Map.fromListWith (++)
    (concatMap (\ (s, d, c) -> [(s, [(d, c)]), (d, [(s, c)])])
      [ (Seattle, Chicago, 1000)
--      , (Seattle, LA, 500)
      , (Chicago, NYC, 700)
      , (Chicago, StLouis, 250)
      , (NYC, Burlington, 150)
      , (Burlington, Montreal, 200)
--      , (LA, StLouis, 1200)
      , (StLouis, Nashville, 300)
      , (Nashville, DC, 225)
      , (DC, NYC, 350)
      ])
  
newtype State = State (Map City Int)
  deriving Show
             
init :: State
init = State (Map.fromList [(Seattle, 0)])

type Action = (City, City)

type Error a = Either String a

guardErr :: Bool -> String -> Error ()
guardErr b s = if b then Right () else Left s

fromJustErr :: Maybe a -> String -> Error a
fromJustErr (Just a) _ = Right a
fromJustErr Nothing msg = Left msg

step :: State -> Action -> Error State
step (State m) (v, next) = do 
    let l = theGraph Map.! v
    cv <- fromJustErr (Map.lookup v m) (show v ++ " is not yet visited!")
    ce <- fromJustErr (lookup next l) (show next ++ " is not adjacent to " ++ show v ++ "!")
    let c' = cv + ce
    return . State $ Map.alter (Just . maybe c' (min c')) next m

actions :: State -> [Action]
actions (State m) =
  Map.foldMapWithKey (\ k _ -> map ((k,) . fst) . concat . maybeToList $ Map.lookup k theGraph) m
  
-- for updr: bipartite state space alternating between queries and answers

heuristic :: State -> Maybe Action
heuristic s =
  case actions s of
    [x] -> Just x
    _ -> Nothing

drive :: State -> Error State
drive s =
  case heuristic s of
    Nothing -> Right s
    Just a -> step s a >>= drive

type Goddity = TrieMap Map Action State

-- type TreeZipper a = Tree.Zipper.TreePos Tree.Zipper.Full a  
-- 
-- findZipper :: (a -> Bool) -> TreeZipper a -> Maybe (TreeZipper a)
-- findZipper p t = go t
--   where go t = if p (Tree.Zipper.label t) then Just t
--                else Tree.Zipper.firstChild t >>= goF
--         goF t = go t <|> Tree.Zipper.next t >>= goF

goddity_init :: Goddity
--goddity_init = Tree.Zipper.fromTree $ Tree.Node init []
goddity_init = TrieMap.singleton [] init

type GState = (Goddity, [Action], State)

ginit :: GState
ginit = (goddity_init, [], init)

current :: GState -> State
current (_, _, s) = s

switchTo :: [Action] -> GState -> Error GState
switchTo k (g, _, _) = do
  s <- fromJustErr (TrieMap.lookup k g) ("Unknown trace " ++ show k)
  return (g, k, s)
  
forward :: Action -> GState -> Error GState
forward a (gs@(g, k, s)) =
  let k' = (k ++ [a]) in
  switchTo k' gs <> do
    s' <- step s a
    return (TrieMap.insert k' s' g, k', s')
  
backward :: GState -> Error GState
backward (g, [], _) = Left "Can't go backward from initial state"
backward gs@(g, k, _) = switchTo (Prelude.init k) gs
  
main :: IO ()
main = go ginit
  where
    go s = do
      print s
      c <- getLine
      return ()
        

  
          


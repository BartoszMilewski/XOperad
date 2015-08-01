{-# LANGUAGE OverlappingInstances #-} -- for show
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.Foldable
import Data.Traversable
import Data.Monoid
import Data.Maybe
import Control.Comonad
import Prelude hiding (concat, sum, foldr, any, all)

-- Vector

ixV :: Int -> [a] -> a
ixV n l = l !! n

atV :: a -> Int -> [a] -> [a]
atV a 0 (x:xs) = a : xs
atV a n (x:xs) = x : atV a (n-1) xs

splitV :: Int -> Int -> [a] -> ([a], [a])
splitV 0 _ v = ([], v)
splitV n m (h : t) = (h : t1, t2)
  where
      (t1, t2) = splitV (n - 1) m t

split3V :: Int -> Int -> Int -> [a] -> ([a], [a], [a])
split3V n m k v = (vn, vm, vk)
   where (vn, t) = splitV n (m + k) v
         (vm, vk) = splitV m k t

middleV :: Int -> Int -> Int -> [a] -> [a]
middleV n m k v = mid
  where (_, mid, _) = split3V n m k v

-- Matrix

newtype Matrix a = Matrix { unMatrix :: [[a]] }

getM :: Int -> Int -> Matrix a -> a
getM x y m = unMatrix m !! y !! x

transpose :: [[a]] -> [[a]]
transpose = sequenceA

setM :: a -> Int -> Int -> Matrix a -> Matrix a
setM a x y m = Matrix $ atV newCol y (unMatrix m)
  where newCol = atV a x (ixV y (unMatrix m))

instance Functor Matrix where
    fmap f = Matrix . fmap (fmap f) . unMatrix

instance Foldable Matrix where
    foldMap f = foldMap (foldMap f) . unMatrix

instance Traversable Matrix where
    traverse g = fmap Matrix . traverse (traverse g) . unMatrix

instance Show a => Show (Matrix a) where
    show = concat . fmap (\v -> ln v ++ "\n") . rows
      where
          ln  :: Show a => [a] -> String
          ln = concat . toList . fmap (\x -> show x ++ " ")

rows :: Matrix a -> [[a]]
rows = toList . unMatrix

cols :: Matrix a -> [[a]]
cols = toList . transpose . unMatrix

getRow :: Int -> Matrix a -> [a]
getRow k (Matrix vv) = ixV k vv

getCol :: Int -> Matrix a -> [a]
getCol k (Matrix vv) = fmap (ixV k) vv

getDiagL :: Matrix a ->  [a]
getDiagL (Matrix vv) = diag vv
  where
    diag :: [[a]] -> [a]
    diag [[a]] = [a]
    diag ((a : _) : vs) = a : (diag $ fmap tail vs)

getDiagR :: Matrix a -> [a]
getDiagR (Matrix vv) = antidiag vv
  where
    antidiag :: [[a]] -> [a]
    antidiag [[a]] = [a]
    antidiag (v : vs) = (last v) : (antidiag $ fmap init vs)

-- Forest

type Forest f = [f]

class Graded f where
    grade :: f -> Int

inputs :: (f -> Int) -> Forest f -> Int
inputs g fs = getSum . foldMap (Sum . g) $ fs

replicateF :: Int -> f -> Forest f
replicateF n f = replicate n f

splitForest :: Int -> Forest f -> (Forest f, Forest f)
splitForest n = splitAt n

-- Operad

class (Graded f) => Operad f where
  ident :: f
  compose :: f -> Forest f -> f

idents :: Operad f => Int -> Forest f
idents n = replicateF n ident


plantTreeAt :: Operad f => Int -> Int -> f -> Forest f
plantTreeAt k m f = idents k ++ [f] ++ idents m

-- Comonad
newtype W f a = W { runW :: f -> [a] }

instance Functor (W f) where
    fmap g (W act) = W $ \f -> fmap g (act f)

instance Operad f => Comonad (W f) where
  extract (W act) = case act ident of [a] -> a
  duplicate (W act) = W $ \f -> go f 0 (grade f)
    where
      -- n increases, m decreases, n starts as zero, m starts as (grade f)
      -- go :: f -> Int -> Int -> [W f a]
      go _ _ 0 = []
      go f1 n m =  W act' : go f1 (n + 1) (m - 1)
        where
          act' f2 = middleV n (grade f2) (m - 1) (act (f1 `compose` plantTreeAt n (m - 1) f2))


-- Tic Tac Toe

data Player = Cross | Circle
  deriving Eq

instance Show Player where
    show Cross  = " X "
    show Circle = " O "

type Board = Matrix (Maybe Player)

instance Show Board where
    show = concat . fmap (\v -> ln v ++ "\n") . rows
      where
          ln  :: Show a => [Maybe a] -> String
          ln v = (concat . toList . fmap (\x -> maybe " - " show x ++ " ")) v

get :: Int -> Int -> Board -> Maybe Player
get x y = getM x y

set :: Player -> Int -> Int -> Board -> Board
set pl x y = setM (Just pl) x y

emptyBoard :: Board
emptyBoard = Matrix $ replicate 3 $ replicate 3 $ Nothing

scoreBoard :: Matrix Int
scoreBoard = Matrix [[1, 0, 1], [0, 2, 0], [1, 0, 1]]

-- Moves and MoveTrees

data Move = Move Player Int Int

instance Show Move where
    show (Move pl x y) = show pl ++ "(" ++ show x ++ ", " ++ show y ++ ")"

data MoveTree = Leaf | Fan [(Move, MoveTree)]

instance Show MoveTree where
    show Leaf = "."
    show (Fan ts) = show ts

singleT :: Move -> MoveTree
singleT mv = Fan $ [(mv, Leaf)]

headT :: MoveTree -> Maybe (Move)
headT (Fan [(mv, t)]) = Just mv
headT _ = Nothing

tailT :: MoveTree -> Maybe MoveTree
tailT (Fan [(_, Leaf)]) = Just Leaf
tailT (Fan [(_, t)]) = do
    mv <- getMove t
    tl <- tailT t
    return $ Fan $ [(mv, tl)]
tailT _ = Nothing

getMove :: MoveTree -> Maybe Move
getMove (Fan [(mv, _)]) = Just mv
getMove Leaf = Nothing

getT :: Int -> MoveTree -> Maybe MoveTree
getT 0 (Fan [(mv, _)]) = Just $ Fan [(mv, Leaf)]
getT n (Fan [(_, t)]) = do
    mv <- getMove t
    tl <- tailT t
    getT (n - 1) $ Fan [(mv, tl)]

lengthT :: MoveTree -> Int
lengthT (Fan [(mv, Leaf)]) = 1
lengthT (Fan [(mv, t)]) = 1 + lengthT t

mapT :: ((Move, MoveTree) -> (Move, MoveTree)) -> MoveTree -> MoveTree
mapT _ Leaf = Leaf
mapT f (Fan ts) = Fan (mapTs f ts)
mapTs :: ((Move, MoveTree) -> (Move, MoveTree)) -> [(Move, MoveTree)]-> [(Move, MoveTree)]
mapTs _ [] = []
mapTs f (branch : ts) = f branch : mapTs f ts

prependT :: Move -> MoveTree -> MoveTree
prependT mv Leaf = singleT mv
prependT mv ts@(Fan _) = Fan [(mv, ts)]

allMoves :: Player -> MoveTree
allMoves pl = Fan $ threeMoves 0 ++ threeMoves 1 ++ threeMoves 2
  where
      threeMoves :: Int -> [(Move, MoveTree)]
      threeMoves y = [(Move pl 0 y, Leaf), (Move pl 1 y, Leaf), (Move pl 2 y, Leaf)]

instance Operad MoveTree where
    ident = Leaf
    -- compose :: MoveTree -> Forest MoveTree -> MoveTree
    compose Leaf [t] = t
    -- | | | | | | j
    --    | | | |  k
    --     \/ \/   k
    compose (Fan ((mv, t) : ts)) frt =
        let (mts1, mts2) = splitForest (grade t) frt
            tree  = (compose t mts1)
            (Fan trees) = compose (Fan ts) mts2
        in Fan $ (mv, tree) : trees

    compose (Fan []) [] = Fan []
    compose _ _ = error "compose!"

instance Graded MoveTree where
    grade Leaf = 1
    grade (Fan lst) = getSum $ foldMap (\(_, t) -> Sum (grade t)) lst

data Score = Bad | Win | Lose | Good Int
  deriving (Show, Eq)

type Evaluation = (Score, MoveTree)

instance Show Evaluation where
    show (Bad, _) = "Bad\n"
    show (ev, mt) = show ev ++ ": " ++ show mt ++ "\n"

type TicTacToe = W MoveTree Evaluation

eval :: Board -> MoveTree -> [Evaluation]
eval board moves = case moves of
    Leaf -> [(Good 0, Leaf)]
    Fan ts -> evalTs (evalBranch board) ts



evalBranch :: Board -> (Move, MoveTree) -> [Evaluation]
evalBranch board (mv@(Move pl x y), t) =
    if isMarked x y board
    then replicate (grade t) (Bad, Leaf)
    else let  board' = set pl x y board
              sc = evalValidMove board' mv
         in case sc of
             Win  -> replicate (grade t) (Win, singleT mv)
             Lose -> replicate (grade t) (Lose, singleT mv)
             Good sval ->
                let evals = eval board' t
                    isLosing = any (\(s, _) -> s == Lose) evals
                    adj = if isLosing then -100 else sval
                in fmap (\(s, mvs) -> (adjustScore adj s, prependT mv mvs)) $ evals
  where
      adjustScore adj (Good sc) = Good (sc + adj)
      adjustScore _ sc = sc

evalValidMove :: Board -> Move -> Score
evalValidMove board (Move pl x y) = 
    if winRow || winCol || winDiag 
    then if pl == Circle then Win else Lose
    else let sc = getM x y scoreBoard
         in 
             if pl == Circle then Good sc else Good 0
  where
    winRow = all isMine $ getRow y board
    winCol = all isMine $ getCol x board
    winDiag = winDiagL || winDiagR
    winDiagL = x == y && (all isMine $ getDiagL board)
    winDiagR = isRDiag && (all isMine $ getDiagR board)
    isRDiag = x == 1 && y == 1 ||
              x == 2 && y == 0 ||
              y == 2 && x == 0
    isMine = maybe False (== pl)

evalTs :: ((Move, MoveTree) -> [Evaluation]) -> [(Move, MoveTree)] -> [Evaluation]
evalTs _ [] = []
evalTs f (br : ts) = f br ++ evalTs f ts

isMarked :: Int -> Int -> Board -> Bool
isMarked x y = isJust . get x y

tryMove :: TicTacToe -> MoveTree -> (Score, TicTacToe)
tryMove game move =
  let evs = runW game move
      (ev, _) = head evs
  in case ev of
      Good _ ->  let games = duplicate game
                 in (ev, head $ runW games move)
      _ -> (ev, game)


tryAll :: MoveTree -> Player -> MoveTree
tryAll mt pl = compose mt $ replicateF (grade mt) (allMoves pl)

makeMove :: TicTacToe -> (Score, TicTacToe, MoveTree)
makeMove game =
    let moves = tryAll (tryAll Leaf Circle) Cross
        evals = runW game moves
        (score, branch) = bestMove evals
        games = duplicate game
        (_, branch0) = extract game
        -- The new move is past the current branch
        Just mv = getT (lengthT branch0) branch -- cannot fail!
        game' = head $ runW games mv
    in (score, game', mv)

bestMove :: [Evaluation] -> (Score, MoveTree)
bestMove [] = error "No valid moves"
bestMove (ev : evals) = go ev evals
  where
    go :: Evaluation -> [Evaluation] -> (Score, MoveTree)
    go (sc, mmv) [] = (sc, mmv)
    go ev1@(sc1, _) (ev2@(sc, _) : evs) =
      if better sc sc1 
      then go ev2 evs
      else go ev1 evs
    better sc sc' = case sc of
        Win -> True
        (Good n) -> case sc' of
            (Good m) -> n > m
            Bad -> True
            _ -> False
        _ -> False

-- get a user move, validate it, make a move
play :: Board -> TicTacToe -> IO ()
play board game = do
    putStrLn $ show $ board
    ln <- getLine
    let coords :: [Int] = (fmap (\x -> x - 1) . fmap read . words) ln
        pos = do
                x <- safeHead coords >>= toFin3
                y <- safeTail coords >>= safeHead >>= toFin3
                return (x, y)
    case pos of
        Nothing -> do 
            putStrLn "Enter two numbers: x y coordinates 1..3 1..3"
            play board game
        Just (x, y) ->
            let userMove = singleT (Move Cross x y)
                board' = set Cross x y board
                (status, game') = tryMove game userMove
            in case status of
              Lose -> do
                  putStrLn "You win!"
                  putStrLn $ show $ board'
              Bad -> do
                  putStrLn "Invalid move! Try again."
                  play board game'
              Good _ -> do
                  putStrLn $ show $ board'
                  respond board' game'

toFin3 :: Int -> Maybe Int
toFin3 n = if n < 3 then Just n else Nothing

respond :: Board -> TicTacToe -> IO ()
respond board game = do
    let (status, game', mt) = makeMove game
        Just (Move pl x y) = getMove mt -- cannot fail!
        board' = set pl x y board
    case status of
      Good _ -> do
        play board' game'
      Win -> do
        putStrLn "You lose!"
        putStrLn $ show $ board'
      _ -> putStrLn "A tie!"


main :: IO ()
main = do
    putStrLn "Make your moves by entering x y coordinates 1..3 1..3, anything else to quit."
    let board = emptyBoard
        game = W $ eval board
    play board game

safeHead :: [a] -> Maybe a
safeHead (x:_) = Just x
safeHead _ = Nothing

safeTail :: [a] -> Maybe [a]
safeTail (_:xs) = Just xs
safeTail _ = Nothing

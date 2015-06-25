{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-} -- for show

import Numbers
import Vector
import Matrix
import Forest
import Operad

import Data.Maybe
import Control.Comonad
import Data.Constraint
import Data.Proxy
import Data.Foldable
import Prelude hiding (concat, sum, foldr)

-- Tic Tac Toe

data Player = Cross | Circle
  deriving Eq

instance Show Player where
    show Cross  = " X "
    show Circle = " O "

--------
-- Board
--------

type Board = Matrix Three Three (Maybe Player)

instance Show Board where
    show = concat . fmap (\v -> ln v ++ "\n") . rows
      where
          ln  :: Show a => Vec n (Maybe a) -> String
          ln v = (concat . toList . fmap (\x -> maybe " - " show x ++ " ")) v

get :: Fin Three -> Fin Three -> Board -> Maybe Player
get x y = getM x y

set :: Player -> Fin Three -> Fin Three -> Board -> Board
set pl x y = setM (Just pl) x y

three :: SNat Three
three = SS (SS (SS SZ))

emptyRow :: Vec Three (Maybe Player)
emptyRow = VCons Nothing (VCons Nothing (VCons Nothing VNil))

emptyBoard :: Board
emptyBoard = Matrix (VCons emptyRow (VCons emptyRow (VCons emptyRow VNil)))

scoreBoard :: Matrix Three Three Int
scoreBoard = Matrix $ VCons scoreRow1 $ VCons scoreRow2 $ VCons scoreRow1 VNil
  where
      scoreRow1 = VCons 1 $ VCons 0 $ VCons 1 VNil
      scoreRow2 = VCons 0 $ VCons 2 $ VCons 0 VNil

data Move = Move Player (Fin Three) (Fin Three)

instance Show Move where
    show (Move pl x y) = show pl ++ "(" ++ show x ++ ", " ++ show y ++ ")"

-----------
-- MoveTree
-- Leaf-counted edge-labelled rose tree of moves
-- Counted version of
-- data RoseTree = Leaf | [(Move, RoseTree)]
-----------
data MoveTree n where
    Leaf ::               MoveTree One
    Fan  :: Trees n    -> MoveTree n

data Trees n where
    NilT ::                                     Trees Z
    (:+) :: (Move, MoveTree k) -> Trees m    -> Trees (k + m)

infixr 5 :+

instance Show (MoveTree n) where
    show Leaf = "."
    show (Fan ts) = show ts

instance Show (Trees n) where
    show NilT = ";"
    show ((m, t) :+ ts) = show m ++ "->{" ++ show t ++ "} :- " ++ show ts

singleT :: Move -> MoveTree One
singleT mv = Fan $ (mv, Leaf) :+ NilT

tailT :: MoveTree n -> Maybe (MoveTree n)
tailT (Fan ((_, Leaf) :+ NilT)) = Just Leaf
tailT (Fan ((_, t) :+ NilT)) = do
    mv <- getMove t
    tl <- tailT t
    return $ Fan $ (mv, tl) :+ NilT
tailT _ = Nothing

getMove :: MoveTree n -> Maybe Move
getMove (Fan ((mv, _) :+ NilT)) = Just mv
getMove Leaf = Nothing

getT :: Int -> MoveTree One -> Maybe (MoveTree One)
getT 0 (Fan ((mv, _) :+ NilT)) = Just $ Fan ((mv, Leaf) :+ NilT)
getT n (Fan ((_, t) :+ NilT)) = do
    mv <- getMove t
    tl <- tailT t
    getT (n - 1) $ Fan ((mv, tl) :+ NilT)

mapT :: (forall k. (Move, MoveTree k) -> (Move, MoveTree k)) -> MoveTree n -> MoveTree n
mapT _ Leaf = Leaf
mapT f (Fan ts) = Fan (mapTs f ts)
mapTs :: (forall k. (Move, MoveTree k) -> (Move, MoveTree k)) -> Trees n -> Trees n
mapTs _ NilT = NilT
mapTs f (branch :+ ts) = f branch :+ mapTs f ts

prependT :: forall n. Move -> MoveTree n -> MoveTree n
prependT mv Leaf = singleT mv
prependT mv ts@(Fan _) = case plusZ :: Dict (n ~ (n + Z)) of Dict -> Fan $ (mv, ts) :+ NilT

concatT :: Trees n -> Trees m -> Trees (n + m)
concatT NilT ts = ts
-- (k + m) + n = k + (m + n)
concatT ((mv, a :: MoveTree k) :+ (as :: Trees m)) (ts :: Trees n) = 
  case plusAssoc (Proxy :: Proxy k) (Proxy :: Proxy m) (Proxy :: Proxy n) of Dict -> (mv, a) :+ (concatT as ts)

allMoves :: Player -> MoveTree Nine
allMoves pl = Fan $ threeMoves FinZ `concatT` threeMoves (FinS FinZ) `concatT` threeMoves (FinS (FinS FinZ))
  where
      threeMoves :: Fin Three -> Trees Three
      threeMoves y = (Move pl FinZ y, Leaf) :+
                     (Move pl (FinS FinZ) y, Leaf) :+
                     (Move pl (FinS (FinS FinZ)) y, Leaf) :+ NilT


instance Operad MoveTree where
    ident = Leaf
    -- compose :: MoveTree n -> Forest m n -> MoveTree m
    compose Leaf (Cons Leaf Nil) = Leaf
    compose Leaf (Cons (t :: MoveTree m) Nil) = 
        case plusZ :: Dict (m ~ (m + Z)) of Dict -> t
    -- | | | | | | j
    --    | | | |  k
    --     \/ \/   k
    compose (Fan ((mv, t) :+ ts)) frt = Fan $ splitForest (grade t) (grade ts) frt $
              \(mts1, mts2) ->                 -- (Forest MoveTree i1 m1, Forest MoveTree i2 m2)
                 let tree  = (compose t mts1)  -- MoveTree i1
                     (Fan trees) = (compose (Fan ts) mts2) -- Trees i2 <- (Trees m2 . Forest MoveTree i2 m2)
                 in (mv, tree) :+ trees
    compose (Fan NilT) Nil = Fan NilT
    compose _ _ = error "compose!"

instance Graded MoveTree where
    grade Leaf = SS SZ
    grade (Fan ts) = grade ts

instance Graded Trees where
    grade NilT = SZ
    grade ((_, t) :+ ts) = grade t `plus` grade ts


-- Win, Lose, or Good from the perspective of the computer
-- A move is Bad if the square is occupied
data Score = Bad | Win | Lose | Good Int
  deriving (Show, Eq)

type Evaluation = (Score, MoveTree One)

instance Show Evaluation where
    show (Bad, _) = "Bad\n"
    show (ev, mt) = show ev ++ ": " ++ show mt ++ "\n"

type TicTacToe = W MoveTree Evaluation

data Status = Valid | Winning | Losing | Invalid

----------
-- Comonad
----------
-- newtype W f a = W { runW :: forall n. f n -> Vec n a }
-- eval is the implementation of the comonad
-- First move is always the user's

eval :: Board -> MoveTree n -> Vec n Evaluation
eval board moves = case moves of
    Leaf -> singleV (Good 0, Leaf)
    Fan ts -> evalTs (evalBranch board) ts



evalBranch :: Board -> (Move, MoveTree n) -> Vec n Evaluation
evalBranch board (mv@(Move pl x y), t) =
    if isMarked x y board
    then replicateV (grade t) (Bad, Leaf)
    else let  board' = set pl x y board
              sc = evalValidMove board' mv
         in case sc of
             Win  -> replicateV (grade t) (Win, singleT mv)
             Lose -> replicateV (grade t) (Lose, singleT mv)
             Good sval ->
                let evals = eval board' t
                    isLosing = anyV (\(s, _) -> s == Lose) evals
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
    winRow = allV isMine $ getRow y board
    winCol = allV isMine $ getCol x board
    winDiag = winDiagL || winDiagR
    winDiagL = x == y && (allV isMine $ getDiagL board)
    winDiagR = isRDiag && (allV isMine $ getDiagR board)
    isRDiag = x == (FinS FinZ) && y == FinS FinZ ||
              x == (FinS (FinS FinZ)) && y == FinZ ||
              y == (FinS (FinS FinZ)) && x == FinZ
    isMine = maybe False (== pl)

evalTs :: (forall k. (Move, MoveTree k) -> Vec k Evaluation) -> Trees n -> Vec n Evaluation
evalTs _ NilT = VNil
evalTs f (br :+ ts) = concatV (f br) (evalTs f ts)

isMarked :: Fin Three -> Fin Three -> Board -> Bool
isMarked x y = isJust . get x y

tryMove :: TicTacToe -> MoveTree One -> (Score, TicTacToe)
tryMove game move =
  let evs = runW game move
      (ev, _) = headV evs
  in case ev of
      Good _ ->  let games = duplicate game
                 in (ev, headV $ runW games move)
      _ -> (ev, game)


tryAll :: MoveTree n -> Player -> MoveTree (n * Nine)
tryAll mt pl = compose mt $ replicateF (grade mt) (allMoves pl)

makeMove :: TicTacToe -> Int -> (Score, TicTacToe, MoveTree One)
makeMove game n = 
    let moves = tryAll (tryAll Leaf Circle) Cross
        evals = runW game moves
        (score, branch) = bestMove evals
        games = duplicate game
        Just mv = getT n branch -- cannot fail!
        game' = headV $ runW games mv
    in (score, game', mv)

bestMove :: Vec n Evaluation -> (Score, MoveTree One)
bestMove VNil = error "No valid moves"
bestMove (VCons ev evals) = go ev evals
  where
    go :: Evaluation -> Vec m Evaluation -> (Score, MoveTree One)
    go (sc, mmv) VNil = (sc, mmv)
    go ev1@(sc1, _) (VCons ev2@(sc, _) evs) = 
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
play :: Board -> TicTacToe -> Int -> IO ()
play board game n = do
    putStrLn $ show $ board
    ln <- getLine
    let (coords :: [Int]) = (fmap (\x -> x - 1) . fmap read . words) ln
        pos = do
                x <- safeHead coords >>= toFin3
                y <- safeTail coords >>= safeHead >>= toFin3
                return (x, y)
    case pos of
        Nothing -> do 
            putStrLn "Enter two numbers: x y coordinates 1..3 1..3"
            play board game n
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
                  play board game' n
              Good _ -> do
                  putStrLn $ show $ board'
                  if n < 8
                  then respond board' game' (n + 1)
                  else putStrLn "It's a tie!"

respond :: Board -> TicTacToe -> Int -> IO ()
respond board game n = do
    let (status, game', mt) = makeMove game n
        Just (Move pl x y) = getMove mt -- cannot fail!
        board' = set pl x y board
    case status of
      Good _ -> do
        putStrLn "My move:"
        putStrLn $ show $ board'
        play board' game' (n + 1)
      Win -> do
        putStrLn "You lose!"
        putStrLn $ show $ board'
      _ -> putStrLn "A tie!"


main :: IO ()
main = do
    putStrLn "Make your moves by entering x y coordinates 1..3 1..3, anything else to quit."
    let board = emptyBoard
        game = W $ eval board
    play board game 0

safeHead :: [a] -> Maybe a
safeHead (x:_) = Just x
safeHead _ = Nothing

safeTail :: [a] -> Maybe [a]
safeTail (_:xs) = Just xs
safeTail _ = Nothing

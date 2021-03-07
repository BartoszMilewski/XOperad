{-# LANGUAGE GADTs #-}
module Matrix where

import Numbers
import Vector

import Data.Foldable
import Data.Traversable
import Prelude hiding (concat, sum, foldr)
-----------------
-- Matrix
-- n rows, m cols
-----------------
newtype Matrix n m a = Matrix { unMatrix :: Vec n (Vec m a) }

getM :: Fin m -> Fin n -> Matrix n m a -> a
getM x y = ixV x . ixV y . unMatrix

setM :: a -> Fin m -> Fin n -> Matrix n m a -> Matrix n m a
setM a x y m = Matrix $ atV newCol y (unMatrix m)
  where newCol = atV a x (ixV y (unMatrix m))


instance Functor (Matrix m n) where
    fmap f = Matrix . fmap (fmap f) . unMatrix

instance Foldable (Matrix m n) where
    foldMap f = foldMap (foldMap f) . unMatrix

instance Traversable (Matrix m n) where
    traverse g = fmap Matrix . traverse (traverse g) . unMatrix

instance Show a => Show (Matrix m n a) where
    show = concat . fmap (\v -> ln v ++ "\n") . rows
      where
          ln  :: Show a => Vec n a -> String
          ln = concat . toList . fmap (\x -> show x ++ " ")

rows :: Matrix n m a -> [Vec m a]
rows = toList . unMatrix

cols :: KnownNat m => Matrix n m a -> [Vec n a]
cols = toList . transpose . unMatrix

getRow :: Fin n -> Matrix n m a -> Vec m a
getRow k (Matrix vv) = ixV k vv

getCol :: Fin m -> Matrix n m a -> Vec n a
getCol k (Matrix vv) = fmap (ixV k) vv

getDiagL :: Matrix n n a -> Vec n a
getDiagL (Matrix vv) = diag vv
  where
    diag :: Vec n (Vec n a) -> Vec n a
    diag (VCons (VCons a VNil) VNil) = singleV a
    diag (VCons (VCons a _) vs) = VCons a (diag $ fmap tailV vs)

getDiagR :: Matrix n n a -> Vec n a
getDiagR (Matrix vv) = antidiag vv
  where
    antidiag ::  Vec n (Vec n a) -> Vec n a
    antidiag (VCons (VCons a VNil) VNil) = singleV a
    antidiag (VCons v vs) = VCons (lastV v) (antidiag $ fmap initV vs)

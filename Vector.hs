{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Vector where

import Numbers
import Control.Applicative
import Data.Traversable
import Data.Foldable
import Data.Monoid
import Prelude hiding (concat, sum)

data Vec n a where
    VCons :: a -> Vec n a -> Vec (S n) a
    VNil :: Vec Z a

instance (Show a) => Show (Vec n a) where
    show VNil = "VNil"
    show (VCons a as) = show a ++ " : " ++ show as

infixr 5 `VCons`

singleV :: a -> Vec One a
singleV a = VCons a VNil

replicateV :: SNat n -> a -> Vec n a
replicateV SZ _ = VNil
replicateV (SS n) x = VCons x (replicateV n x)

allV :: (a -> Bool) -> Vec n a -> Bool
allV f = getAll . foldMap (All . f)

anyV :: (a -> Bool) -> Vec n a -> Bool
anyV f = getAny . foldMap (Any . f)

zipWithV :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithV f (VCons a as) (VCons b bs) = VCons (f a b) (zipWithV f as bs)
zipWithV _ VNil VNil = VNil
zipWithV _ _ _ = undefined -- can't happen

headV :: Vec (S n) a -> a
headV (VCons a _) = a

lastV :: Vec (S n) a -> a
lastV (VCons a VNil) = a
lastV (VCons _ as@(VCons _ _)) = lastV as

tailV :: Vec (S n) a -> Vec n a
tailV (VCons _ as) = as

initV :: Vec (S n) a -> Vec n a
initV (VCons a (VCons _ VNil)) = VCons a VNil
initV (VCons a as@(VCons _ _)) = VCons a (initV as)
initV (VCons _ VNil) = undefined -- must not happen!

concatV :: Vec n a -> Vec m a -> Vec (n + m) a
concatV VNil v = v
concatV (VCons a as) v = VCons a (concatV as v)

splitV :: SNat n -> SNat m -> Vec (n + m) a -> (Vec n a, Vec m a)
splitV SZ _ v = (VNil, v)
splitV (SS n) m (h `VCons` t) = (h `VCons` t1, t2)
  where
      (t1, t2) = splitV n m t

split3V :: SNat n -> SNat m -> SNat k -> Vec (n + (m + k)) a -> (Vec n a, Vec m a, Vec k a)
split3V n m k v = (vn, vm, vk)
   where (vn, t) = splitV n (m `plus` k) v
         (vm, vk) = splitV m k t

middleV :: SNat n -> SNat m -> SNat k -> Vec (n + (m + k)) a -> Vec m a
middleV n m k v = mid
  where (_, mid, _) = split3V n m k v

nthV :: SNat n -> SNat (S m) -> Vec (n + S m) a -> a
nthV n m v = headV v2
  where
      (_, v2) = splitV n m v

ixV :: Fin n -> Vec n a -> a
ixV FinZ (x `VCons` _) = x
ixV (FinS fin_n) (_ `VCons` xs) = ixV fin_n xs

atV :: a -> Fin n -> Vec n a -> Vec n a
atV a FinZ (_ `VCons` as) = a `VCons` as
atV b (FinS n) (a `VCons` as) = a `VCons` atV b n as
atV _ FinZ _ = undefined

instance Functor (Vec n) where
    fmap f (VCons a as) = VCons (f a) (fmap f as)
    fmap _ VNil = VNil

instance KnownNat n => Applicative (Vec n) where
    pure = replicateV natSing
    fs <*> xs = zipWithV ($) fs xs

instance Foldable (Vec n) where
    foldMap _ VNil = mempty
    foldMap f (VCons a as) = f a <> foldMap f as

instance Traversable (Vec n) where
    traverse _ VNil = pure VNil
    traverse f (VCons a as) = VCons <$> f a <*> traverse f as

transpose :: KnownNat m => Vec n (Vec m a) -> Vec m (Vec n a)
transpose = sequenceA


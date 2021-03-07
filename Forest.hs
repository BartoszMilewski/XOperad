{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
module Forest where

import Numbers
import Data.Proxy
import Data.Constraint
import Data.Kind

-- f n : a tree with n branches (inputs)
-- Forest f i o : a forest of o trees with total i branches
-- Cons 
--   i1    i2        (i1 + i2)
--  \ /  | | | |    | | | | | |
--   |     | |         | | |
--          n          1 + n
data Forest f n m where
  Nil  :: Forest f Z Z 
  Cons :: f i1 -> Forest f i2 n -> Forest f (i1 + i2) (S n)

instance Show (Forest f n m) where
    show Nil = "."
    show (Cons _ fs) = "V" ++ ", " ++ show fs

class Graded (f :: Nat -> Type) where
  grade :: f n -> SNat n

inputs :: forall f n m. (forall k. f k -> SNat k) -> Forest f n m -> SNat n
inputs _ Nil = SZ
inputs g (Cons a as) = g a `plus` inputs g as

replicateF :: SNat n -> f i -> Forest f (n * i) n
replicateF SZ _ = Nil
replicateF (SS n) f = Cons f (replicateF n f)

splitForest :: forall m n i f r. SNat m -> SNat n -> Forest f i (m + n) ->
               -- to simulate exists i1 i2, we need to CPS this function
               (forall i1 i2. (i ~ (i1 + i2)) => (Forest f i1 m, Forest f i2 n) -> r) -> r
splitForest SZ _ fs k = k (Nil, fs)
splitForest (SS (sm :: SNat m_1)) sn (Cons (t :: f i1) (ts :: Forest f i2 (m_1 + n))) k =
    splitForest sm sn ts (\((m_frag :: Forest f i3 m_1), (n_frag :: Forest f i4 n)) ->
        case plusAssoc (Proxy :: Proxy i1) (Proxy :: Proxy i3) (Proxy :: Proxy i4) of Dict -> k (Cons t m_frag, n_frag))

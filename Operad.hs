{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Operad where

import Numbers
import Vector
import Forest

import Control.Comonad
import Data.Constraint

---------
-- Operad
---------
-- Composition:
-- \ / \|/
--  |   |  Forest m n
--   \ /
--    |    f n

class (Graded f) => Operad (f :: Nat -> *) where
  ident :: f (S Z)
  compose :: f n -> Forest f m n -> f m

-- Free Operad

data Free (f :: Nat -> *) n where
    Ident :: Free f (S Z)
    Apply :: f n -> Forest (Free f) i n -> Free f i

instance (Graded f) => Graded (Free f) where
    grade Ident = SS SZ
    grade (Apply _ as) = inputs grade as

instance (Graded f) => Operad (Free f) where
    ident = Ident
    -- compose :: Free f n -> Forest (Free f) m n -> Free f m
    compose Ident (Cons (x :: Free f n) Nil) = case plusZ :: Dict (n ~ (n + Z)) of Dict -> x
    -- | | | | n
    --   | | k          xs
    --   \ / k
    --    |             f
    -- Apply f xs :: Free f n, where f :: f k, xs :: Forest (Free f) n k
    -- | | | | | | m
    --   | | | | n     ys
    -- ys :: Forest (Free f) m n
    -- result :: Free f m = Apply f (combine zs), where f :: f k, zs :: Forest (Free f) m k
    compose (Apply f xs) ys = Apply f (combine xs ys)
      where
          -- Forests form a category
          combine :: Forest (Free f) n k -> Forest (Free f) m n -> Forest (Free f) m k
          combine Nil Nil = Nil
          --combine (Cons t ts) us

          -- t :: Free f i
          -- ts :: Forest (Free f) n k 
          -- us :: Forest (Free f) m (i + n)
          -- result :: Forest (Free f) m (k + 1)
          --                        (i + n) (k + 1)                                    m (i + n)         m (k + 1)
          combine (Cons (t :: Free f i) (ts :: Forest (Free f) n k)) (us :: Forest (Free f) m (i + n)) =
              splitForest (grade t) (inputs grade ts) us (\(f1, f2) -> Cons (compose t f1) (combine ts f2))
    
idents :: Operad f => SNat n -> Forest f n n
idents SZ = Nil
idents (SS n) = ident `Cons` idents n

-- Create a forest: idents k ++ f n ++ idents m
plantTreeAt :: Operad f => SNat k -> SNat m -> f n -> Forest f (k + (n + m)) (k + S m)
-- f `Cons` idents m :: Forest (n + m) (S m)
plantTreeAt k m f = prependIdents k (f `Cons` idents m)
  where
      prependIdents :: Operad f => SNat k -> Forest f m n -> Forest f (k + m) (k + n)
      prependIdents SZ forest = forest
      prependIdents (SS n) forest = ident `Cons` prependIdents n forest

-- Monad
data M f a where
   M :: f n -> Vec n a -> M f a

type OperadAlgebra f a = M f a -> a
type OperadCoalgebra f a = a -> M f a

-- Comonad
newtype W f a = W { runW :: forall n. f n -> Vec n a }

instance Functor (W f) where
    fmap g (W k) = W $ \f -> fmap g (k f)

instance Operad f => Comonad (W f) where
  extract (W k) = case k ident of
    -- ident produces a singleton vector
    VCons a VNil -> a
  -- duplicate :: W f -> W (W f)
  -- k :: forall n. f n -> Vec n a
  -- result :: forall m. f m -> Vec m (W f)
  duplicate (W act :: W f a) = W $ \f -> go f SZ (grade f)
    where
      -- n increases, m decreases, n starts as zero, m starts as (grade f)
      go :: f (n + m) -> SNat n -> SNat m -> Vec m (W f a)
      go _ _ SZ = VNil
      --axiom: n + S m ~ S (n + m)
      go f n (SS m) =  case succAssoc n m of 
          Dict -> W act' `VCons` go f (SS n) m
        where
          act' :: f k -> Vec k a
          act' fk = middleV n (grade fk) m (act (f `compose` plantTreeAt n m fk))

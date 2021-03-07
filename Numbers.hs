{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-} -- for multiplication

module Numbers where
    
import Data.Proxy
import Data.Constraint
import Unsafe.Coerce

-- Peano numbers
data Nat = Z | S Nat
  deriving Show

-- Addition of Nats lifted to types (Here, Nat is a kind)
type family (+) (a :: Nat) (b :: Nat) :: Nat
type instance Z   + m = m
type instance S n + m = S (n + m)

type family (*) (a :: Nat) (b :: Nat) :: Nat
type instance Z * m = Z
type instance (S n) * m = m + (n * m)


-- Singleton type parameterized by Nat. Useful for recursion
data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- Arithmetic on singletons
plus :: SNat n -> SNat m -> SNat (n + m)
plus SZ n = n
plus (SS n) m = SS (n `plus` m)
-- (1 + n) + m  = 1 + (n + m)

-- Things that can be converted to Singleton nats
class KnownNat (n :: Nat) where
  natSing :: SNat n

-- Converting lifted Nats to Singetons
instance KnownNat Z where
  natSing = SZ

instance KnownNat n => KnownNat (S n) where
  natSing = SS natSing

type One   = S Z
type Two   = S (S Z)
type Three = S (S (S Z))
type Four  = S (S (S (S Z)))
type Five  = S (S (S (S (S Z))))
type Six   = S (S (S (S (S (S Z)))))
type Seven = S (S (S (S (S (S (S Z))))))
type Eight = S (S (S (S (S (S (S (S Z)))))))
type Nine  = S (S (S (S (S (S (S (S (S Z))))))))

-- Numbers smaller than n
data Fin n where
    FinZ :: Fin (S n) -- zero is less than any successor
    FinS :: Fin n -> Fin (S n) -- n is less than (n+1)

instance Eq (Fin n) where
    FinZ == FinZ = True
    FinS n == FinS m = n == m
    _ == _ = False

instance Show (Fin n) where
    show FinZ = "0"
    show (FinS FinZ) = "1"
    show (FinS (FinS FinZ)) = "2"
    show (FinS (FinS (FinS FinZ))) = "3"
    show (FinS n) = "S " ++ show n

toFin3 :: Int -> Maybe (Fin Three)
toFin3 0 = Just FinZ
toFin3 1 = Just (FinS FinZ)
toFin3 2 = Just (FinS (FinS FinZ))
toFin3 _ = Nothing

-- Axioms

plusZ :: forall n. Dict (n ~ (n + Z))
plusZ = unsafeCoerce (Dict :: Dict (n ~ n))

plusAssoc :: p a -> q b -> r c -> Dict (((a + b) + c) ~ (a + (b + c)))
plusAssoc _ _ _ = unsafeCoerce (Dict :: Dict (a ~ a))

succAssoc :: p a -> q b -> Dict ((a + S b) ~ S (a + b))
succAssoc _ _ = unsafeCoerce (Dict :: Dict (a ~ a))

multDistrib :: p a -> q b -> Dict (S (a * b) ~ (b + (a * b)))
multDistrib _ _ = unsafeCoerce (Dict :: Dict (a ~ a))

-- Convert regular Int to type
-- Can't simply do: exists n. Int -> Proxy n 
-- Existential trick: Use CPS
reifyNat :: Int -> (forall n. KnownNat n => Proxy n -> r) -> r
reifyNat 0 k = k (Proxy :: Proxy Z)
reifyNat n k = reifyNat (n - 1) $ \(Proxy :: Proxy n_1) -> k (Proxy :: Proxy (S n_1))

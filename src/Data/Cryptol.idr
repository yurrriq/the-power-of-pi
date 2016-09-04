module Data.Cryptol

import Data.Vect

%access public export

split : (n : Nat) -> (m : Nat) -> Vect (m * n) a -> Vect m (Vect n a)
split n  Z    [] = []
split n (S k) xs = take n xs :: split n k (drop n xs)

data TakeView : (a : Type) -> (m, n : Nat) -> Vect (m + n) a -> Type where
  Take : (xs : Vect m a) -> (ys : Vect n a) -> TakeView a m n (xs ++ ys)

takeView : (m : Nat) -> (ys : Vect (m + n) a) -> TakeView a m n ys
takeView  Z          ys                           = Take []  ys
takeView (S k) (y :: ys') with (takeView k ys')
  takeView (S k) (y :: (ys ++ zs)) | (Take ys zs) = Take (y :: ys) zs

-- data SplitView : (m : Nat) -> Vect (m * n) a -> Type where
--   Split : (xss : Vect m (Vect n a)) -> SplitView m (concat xss)

data Bit : Type where
  O : Bit
  I : Bit

||| A binary word is a vector of bits.
Word : (n : Nat) -> Type
Word n = Vect n Bit

module Data.Cryptol

%access public export

data Vec : (a : Type) -> Nat -> Type where
  Nil  : Vec a Z
  (::) : a -> Vec a n -> Vec a (S n)

%name Vec xs,ys,zs,ws

(++) : Vec a m -> Vec a n -> Vec a (m + n)
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys

take : (n : Nat) -> Vec a (n + m) -> Vec a n
take  Z     _        = []
take (S k) (x :: xs) = x :: take k xs

drop : (n : Nat) -> Vec a (n + m) -> Vec a m
drop  Z          xs  = xs
drop (S k) (x :: xs) = drop k xs

split : (n : Nat) -> (m : Nat) -> Vec a (m * n) -> Vec (Vec a n) m
split n  Z    [] = []
split n (S k) xs = take n xs :: split n k (drop n xs)

concat : Vec (Vec a n) m -> Vec a (m * n)
concat []          = []
concat (xs :: xxs) = xs ++ concat xxs

data TakeView : (a : Type) -> (m, n : Nat) -> Vec a (m + n) -> Type where
  Take : (xs : Vec a m) -> (ys : Vec a n) -> TakeView a m n (xs ++ ys)

takeView : (m : Nat) -> (ys : Vec a (m + n)) -> TakeView a m n ys
takeView  Z          ys                           = Take []  ys
takeView (S k) (y :: ys') with (takeView k ys')
  takeView (S k) (y :: (ys ++ zs)) | (Take ys zs) = Take (y :: ys) zs

-- data SplitView : (m : Nat) -> Vec a (m * n) -> Type where
--   Split : (xss : Vec (Vec a n) m) -> SplitView m (concat xss)

data Bit : Type where
  O : Bit
  I : Bit

||| A binary word is a vector of bits.
Word : (n : Nat) -> Type
Word n = Vec Bit n

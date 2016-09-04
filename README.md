# The Power of Pi

Data.Cryptol
------------

[*Source*](src/Data/Cryptol.lidr)

Here we're modeling [*Cryptol*](https://github.com/GaloisInc/cryptol), a domain-specific language for cryptographic protocols developed by [Galois, Inc](https://galois.com).

```idris
module Data.Cryptol
```

Since we'll need to operate on vectors, we import the [`Vect` data type](https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr).

```idris
import Data.Vect
```

`Data.Vect` provides [`splitAt`](https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr#L446-L452):

``` idris
splitAt : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect m a)
```

... and [`partition`](https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr#L454-L461):

``` idris
partition : (a -> Bool) -> Vect n a -> ((p ** Vect p a), (q ** Vect q a))
```

... but, not `split`, so we define it here.

```idris
export
split : (n : Nat) -> (m : Nat) -> Vect (m * n) a -> Vect m (Vect n a)
split n  Z    [] = []
split n (S k) xs = take n xs :: split n k (drop n xs)
```

The `TakeView` provides a way to pattern match on taking `m` elements from a vector with `m + n` elements, leaving a vector with `n` elements remaining.

It's entirely similar to [`splitAt`](https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr#L446-L452) and could probably be deprecated in favor of it.

```idris
public export
data TakeView : (a : Type) -> (m, n : Nat) -> Vect (m + n) a -> Type where
  Take : (xs : Vect m a) -> (ys : Vect n a) -> TakeView a m n (xs ++ ys)
```

The covering function `takeView` takes an `m` and a vector with `m + n` elements and returns the appropriate `TakeView`, which can then be used for pattern matching.

N.B. As of now, this definition is *not* recursive and thus not the most efficient.

```idris
export
takeView : (m : Nat) -> (ys : Vect (m + n) a) -> TakeView a m n ys
takeView  Z          ys                           = Take []  ys
takeView (S k) (y :: ys') with (takeView k ys')
  takeView (S k) (y :: (ys ++ zs)) | (Take ys zs) = Take (y :: ys) zs
```

Currently, my version of Idris is [having trouble](https://gist.github.com/yurrriq/a3a4ab7b5e409239fc494920133987ca) with the following, so we'll exclude it for now.

``` idris
public export
data SplitView : (m : Nat) -> Vect (m * n) a -> Type where
  Split : (xss : Vect m (Vect n a)) -> SplitView m (concat xss)
```

**TODO**: Describe `Bit`s and `Word`s.

```idris
public export
data Bit : Type where
  O : Bit
  I : Bit
```

```idris
||| A binary word is a vector of bits.
public export
Word : (n : Nat) -> Type
Word n = Vect n Bit
```

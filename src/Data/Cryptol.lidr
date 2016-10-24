== Data.Cryptol

[*Source*](src/Data/Cryptol.lidr)

Here we're modeling [*Cryptol*][Cryptol], a domain-specific language for
cryptographic protocols developed by [Galois, Inc][Galois].

[Cryptol]: https://github.com/GaloisInc/cryptol
[Galois]: https://galois.com

> module Data.Cryptol

Since we'll need to operate on vectors, we import [`Data.Vect`], which provides
the `Vect` data type.

> import Data.Vect

[`Data.Vect`]: https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr

**TODO**: Describe `Bit`s and `Word`s.

> public export
> data Bit : Type where
>   O : Bit
>   I : Bit

> ||| A binary word is a vector of bits.
> public export
> Word : Nat -> Type
> Word n = Vect n Bit

`Data.Vect` provides [`splitAt`][splitAt]:

```idris
splitAt : (n : Nat) -> (xs : Vect (n + m) a) -> (Vect n a, Vect m a)
```

... and [`partition`][partition]:

```idris
partition : (a -> Bool) -> Vect n a -> ((p ** Vect p a), (q ** Vect q a))
```

... but, not `split`, so we define it here.

> export
> split : (n : Nat) -> (m : Nat) -> Vect (m * n) a -> Vect m (Vect n a)
> split n  Z    [] = []
> split n (S k) xs = take n xs :: split n k (drop n xs)

[splitAt]: https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr#L446-L452
[partition]: https://github.com/idris-lang/Idris-dev/blob/v0.12.2/libs/base/Data/Vect.idr#L454-L461

The `TakeView` provides a way to pattern match on taking `m` elements from a
vector with `m + n` elements, leaving a vector with `n` elements remaining.

It's entirely similar to [`splitAt`][splitAt] and could probably be deprecated
in favor of it.

> public export
> data TakeView : (a : Type) -> (m, n : Nat) -> Vect (m + n) a -> Type where
>   Take : (xs : Vect m a) -> (ys : Vect n a) -> TakeView a m n (xs ++ ys)

The covering function `takeView` takes an `m` and a vector with `m + n` elements
and returns the appropriate `TakeView`, which can then be used for pattern
matching.

N.B. As of now, this definition is *not* recursive and thus not the most
efficient.

> export
> takeView : (m : Nat) -> (ys : Vect (m + n) a) -> TakeView a m n ys
> takeView  Z          ys                           = Take []  ys
> takeView (S k) (y :: ys') with (takeView k ys')
>   takeView (S k) (y :: (ys ++ zs)) | (Take ys zs) = Take (y :: ys) zs

> public export
> data SplitView : {n : Nat} -> (m : Nat) -> Vect (m * n) a -> Type where
>   Split : (xss : Vect m (Vect n a)) -> SplitView m (concat xss)

> takeLemma : (ys : Vect n a) -> (zs : Vect m a) -> take n (ys ++ zs) = ys
> takeLemma []        zs = Refl
> takeLemma (y :: ys) zs = cong (takeLemma ys zs)

> dropLemma : (ys : Vect n a) -> (zs : Vect m a) -> drop n (ys ++ zs) = zs
> dropLemma []        zs = Refl
> dropLemma (y :: ys) zs = dropLemma ys zs

> splitConcatLemma : (xs : Vect (m * n) a) -> concat (split n m xs) = xs
> splitConcatLemma {m = Z} [] = Refl
> splitConcatLemma {m = S k} {n} xs with (takeView n xs)
>   splitConcatLemma {m = S k} {n} (ys ++ zs) | (Take ys zs) =
>     let inductiveHypothesis = splitConcatLemma zs {m=k} {n=n} in
>       rewrite takeLemma ys zs in
>       rewrite dropLemma ys zs in
>       rewrite inductiveHypothesis in
>               Refl

> export
> splitView : (n, m : Nat) -> (xs : Vect (m * n) a) -> SplitView m xs
> splitView n m xs =
>   let prf  = sym (splitConcatLemma xs {m = m} {n = n})
>       view = Split (split n m xs) {n = n} in
>   rewrite prf in view

> export
> swab : Word 32 -> Word 32
> swab xs with (splitView 8 4 xs)
>   swab _ | Split [a, b, c, d] = concat [b, a, c, d]

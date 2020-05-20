> {-# LANGUAGE Safe #-}
> {-|
> Module    : Data.ContinuedFraction
> Copyright : (c) 2020 Dakotah Lambert
> License   : MIT
> 
> Algorithms for constructing and doing arithmetic
> with continued fraction representations of numbers
> both rational and irrational.
> One caveat is that most operations
> that would turn an irrational into a rational
> will never halt.
> -}
> module Data.ContinuedFraction
>     ( -- *Constructions and parameterized rationalization
>       CF(..)
>     , SCF
>     , convergent
>     , converge
>       -- *Generic arithmetic
>       -- |While the @Num@ instance is sufficient
>       -- to perform calculations,
>       -- these functions are more efficient for
>       -- complicated linear fractional transformations.
>       -- Using a bit of algebra,
>       -- it is sometimes possible to combine many operations into one.
>     , gosper4
>     , gosper8
>       -- *Square roots
>     , sqrti
>     , sqrtq
>     ) where

> import Data.Ratio

The empty continued fraction is infinity;
even though it is not generally representable in other formats,
we define here an integral and fractional infinity:

> infinityF :: Fractional a => a
> infinityF = 1 / 0
> infinityI :: Integral a => a
> infinityI = div 1 0

Also, a few other functions for convenience:

> frac :: (Real a, Fractional b) => a -> a -> b
> frac a b = fromRational (toRational a / toRational b)

> characteristic :: Num a => Bool -> a
> characteristic b = if b then 1 else 0

> square :: Num a => a -> a
> square a = a ^ (2 :: Int)


\section{Introduction}

A regular continued fraction is a number represented in the form
\[a_0 + \frac{1}{a_1 + \frac{1}{a_2 + \cdots}}\]
where \(\langle a_0, a_1, a_2, \ldots\rangle\) is a sequence of
integers, all but the first of which are necessarily positive.
The sequence is finite iff the represented number is rational.

For an initial prototype,
we can represent continued fractions with a simple Haskell list.
A better implementation might use
a structure with detectable cycles
in order to more easily work with irrationals
such as the principal square root of 2: \(\langle 1, (2)\rangle\)
(where parentheses indicate a cycle).

> -- |Continued Fraction: a sequence of coefficients.
> newtype CF a = CF [a] deriving (Eq, Read, Show)
> -- |A reasonable specific kind of CF, having integer coefficients.
> type SCF = CF Integer
> -- |Unwrap a continued fraction.
> cfContents :: CF a -> [a]
> cfContents (CF x) = x

> wrap :: ([a] -> [b]) -> CF a -> CF b
> wrap f = CF . f . cfContents

Truncating the sequence after \(n\) elements yields
what is known as the \(n\)th convergent of the representation.
If the denominator of this convergent is \(d\),
this convergent is the nearest rational approximation
to the intended number
with denominator \(d\) or less.

> -- |The element in a converging sequence of rationals
> -- given by taking the first \(n\) coefficients of a representation.
> convergent :: Int -> CF a -> CF a
> convergent n = wrap (take n)

The Haskell @Real@ typeclass provides a single function: @toRational@.
We can turn a continued fraction representation of a number
into a rational by carrying out the computation it implies.
Of course, it would be unwise to call @toRational@ on
an argument whose representation is infinite.
Necessary superclasses of this will be instantiated in a later section.

> instance Real a => Real (CF a) where
>     toRational x = evaluate (cfContents x)
>         where evaluate []      =  infinityF
>               evaluate (a:[])  =  realToFrac a
>               evaluate (a:as)  =  realToFrac a + recip (evaluate as)

The inverse translation is also often possible.
Given any representation of a number,
a continued fraction can be formed.
The result is only as precise as the input representation allows;
so don't expect a perfect \(\langle 1,(2)\rangle\) sequence
if you ask for @cfracOf (sqrt 2)@.
With @Float@ precision,
the eleventh convergent will already be incorrect.
With @Double@, the twenty-second.

> -- |Construct a continued fraction
> -- as accurately as possible from a given number.
> -- @Rational@ numbers will be converted exactly.

> cfracOf :: (RealFrac a, Num b) => a -> CF b
> cfracOf x = CF $ fromIntegral fl :
>             if fromIntegral fl == x
>             then []
>             else cfContents . cfracOf . recip $ x - fromIntegral fl
>     where fl = floor x :: Integer


\section{Operations}

Due to the possibility of infinite representations,
continued fractions are more expressive than rationals.
They also have the nice property that representations
are in one-to-one correspondence with represented objects,
which is not the case with decimals (\(0.9999... = 1\)) or
general rationals (where \(\frac{2}{3} = \frac{6}{9}\), for example).
Some operations are quite complicated, while others are trivial.


\subsection{Comparisons}

Comparing two continued fractions
does not require knowing their final values.
At the beginning of the sequence
a coefficient represents a numerator,
so larger coefficents imply larger values.
If two representations have equal first coefficients,
the second coefficients are checked;
these represent denominators,
so larger coefficients imply smaller values.
Until unequal coefficients are found, this cycle repeats.

> instance Ord a => Ord (CF a) where
>     compare (CF xs) (CF ys) = compare' compare xs ys
>         where compare' _ [] [] = EQ
>               compare' f [] _  = f GT LT
>               compare' f _ []  = f LT GT
>               compare' f (a:as) (b:bs)
>                   = let g = f (compare a b) EQ
>                     in case g of
>                          EQ -> compare' (flip f) as bs
>                          _  -> g

All comparisons involving at least one finite representation terminate.
All comparisons involving inequal numbers terminate.
Comparing two equal infinite representations takes infinite time.


\subsection{Linear fractional transformations}

Bill Gosper presented algorithms for continued fraction arithmetic
(\url{https://perl.plover.com/classes/cftalk/INFO/gosper.ps}).
The simplest is applying a transformation of the form
\(\frac{ax+b}{cx+d}\), a linear fractional transformation,
with \(a, b, c, d\) all integers.

> -- |@gosper4 a b c d x@ is the linear fractional transformation
> -- \(\frac{ax + b}{cx + d}\).  The function is named for Bill Gosper,
> -- who first dealt with continued fraction arithmetic.
> gosper4 :: Real a => a -> a -> a -> a -> CF a -> CF a
> gosper4 a b c d = wrap (gosper4' a b c d)

> gosper4' :: Real a => a -> a -> a -> a -> [a] -> [a]
> gosper4' a _ c _ []
>     | c == 0     =  []
>     | otherwise  =  cfContents (frac a c)
> gosper4' 0 b 0 d _ = gosper4' b 0 d 0 []
> gosper4' a 0 c 0 (_:_:_) = gosper4' a 0 c 0 [] -- for any nonzero x
> gosper4' a b c d (x:xs)
>     | a == 0 || b == 0 || c == 0 || d == 0 || m /= n
>         = gosper4' (x * a + b) a (x * c + d) c xs
>     | otherwise = m : gosper4' c d (a - m * c) (b - m * d) (x:xs)
>     where (q1, b1) = ratio a c
>           (q2, b2) = ratio b d
>           (m, n) = case compare q1 q2 of
>                      LT  ->  (q1, q2 - characteristic b2)
>                      GT  ->  (q2, q1 - characteristic b1)
>                      _   ->  (q1, q2)

> -- |Returns the largest integer not greater than the input,
> -- as well as whether the input was already an integer.
> ratio :: Real a => a -> a -> (a, Bool)
> ratio p q = let x = floor (frac p q) :: Integer
>             in (fromIntegral x, p == q * fromIntegral x)

An enhanced version of this algorithm computes a two-argument variant,
\(\frac{axy+bx+cy+d}{exy+fx+gx+h}\).

> -- |@gosper8 a b c d e f g h x y@ is the transformation
> -- \(\frac{axy + bx + cy + d}{exy + fx + gy + h}\).
> -- Like @gosper4@, this function is named for Bill Gosper.
> gosper8 :: Real a
>         => a -> a -> a -> a -> a -> a -> a -> a -> CF a -> CF a -> CF a
> gosper8 a b c d e f g h (CF x) (CF y)
>     = CF (gosper8' a b c d e f g h x y)

> gosper8' :: Real a
>          => a -> a -> a -> a -> a -> a -> a -> a -> [a] -> [a] -> [a]
> gosper8' a _ _ _ e _ _ _ [] []
>     | e == 0     =  []
>     | otherwise  =  cfContents (frac a e)
> gosper8' a b _ _ e f _ _ [] ys = gosper4' a b e f ys
> gosper8' a _ c _ e _ g _ xs [] = gosper4' a c e g xs
> gosper8' a b c d e f g h (x:xs) (y:ys)
>     | e == 0 && f == 0 && g == 0 && h == 0 = []
>     | e == 0 && f == 0 = goX
>     | e == 0 && g == 0 = goY
>     | f == 0 = goY
>     | g == 0 || h == 0 || e == 0 = goX
>     | vb == vx && vx == vy && vy == vn
>         = n : gosper8' e f g h (m a e) (m b f) (m c g) (m d h)
>               (x:xs) (y:ys)
>     | vb == vy = goY
>     | otherwise = goX
>     where (qb, rb) = ratio a e
>           (qx, rx) = ratio b f
>           (qy, ry) = ratio c g
>           (qn, rn) = ratio d h
>           n = minimum [qb, qx, qy, qn]
>           m s t = s - n * t
>           v q r = q - characteristic (q > n && r)
>           vb = v qb rb
>           vx = v qx rx
>           vy = v qy ry
>           vn = v qn rn
>           goX = gosper8' (a * x + c) (b * x + d) a b
>                          (e * x + g) (f * x + h) e f
>                          xs (y:ys)
>           goY = gosper8' (a * y + b) a (c * y + d) c
>                          (e * y + f) e (g * y + h) g
>                          (x:xs) ys

A lot of the code in this function is simply deciding
which way to progress when ratios would have zero denominators.
But with it all in place,
we can perform many of our favourite operations
on continued fraction representations!
Depending on the initial matrix given to @gosper8@,
we have addition, subtraction, multiplication, and division
all from the same algorithm (as well as some other transformations).


\section{Numeric typeclass and instances thereof}

We have already implemented the @Real@ instance in the introduction.
This section covers the other reasonable numeric typeclasses.
Using the transformation functions from the previous section,
we can implement every function required of a @Num@ instance.

> instance Real a => Num (CF a) where
>     (+) = gosper8 0 1   1  0 0 0 0 1
>     (-) = gosper8 0 1 (-1) 0 0 0 0 1
>     (*) = gosper8 1 0   0  0 0 0 0 1
>     negate = gosper4 (-1) 0 0 1
>     signum x = case x of
>                  CF (a : _)  ->  CF [signum a]
>                  _           ->  x
>     abs x
>         | cfContents (signum x) == [-1] = negate x
>         | otherwise = x
>     fromInteger x = CF [fromIntegral x]

It wouldn't make sense to have continued fractions
that aren't @Fractional@.
Thankfully the functions there are also trivial to implement.

> instance Real a => Fractional (CF a) where
>     (/) = gosper8 0 1 0 0 0 0 1 0
>     recip x
>         | x < 0 = gosper4 0 1 1 0 x
>         | otherwise = case x of
>                         CF (0:xs)  ->  CF xs
>                         CF xs      ->  CF (0 : xs)
>     fromRational = cfracOf

Two alternative implementations of @recip@ are possible:
\begin{itemize}
\item An unconditional call to @gosper4 0 1 1 0@
\item Or calling (negate . recip . negate) for negative numbers.
\end{itemize}
Both of these result in more calls to @gosper4@ than necessary.

The @RealFrac@ instance is hampered by the requirement that
@properFraction@ must output a pair where each value has the
same sign as the input, but implementation is still rather easy.

> instance Real a => RealFrac (CF a) where
>     floor (CF xs) = case xs of
>                       (x:_)  ->  floor (toRational x)
>                       _      ->  infinityI
>     ceiling x = case x of
>                   CF (_:_:_)  ->  floor x + 1
>                   _           ->  floor x
>     truncate x = if x < 0 then ceiling x else floor x
>     properFraction x = let t = truncate x
>                        in (t, x - fromIntegral t)


\section{Miscellaneous neat things}

Beyond this point lie some other computations
that may or may not be useful.


\subsection{Square roots of integers and rationals}

Finding the square root of an integer need not be constrained
by the precision of one's floating point hardware.
One can verify that
\[
    \frac{m\sqrt{x}+r}{d}
    =
    f + \frac{1}{\frac{dm\sqrt{x}-dr+d^2f}{m^2x-(r-df)^2}}\mbox{.}
\]
This looks ugly, but it means that given \(m, r, d, x\),
a mechanism can choose an appropriate \(f\) to output
and then produce a new collection of coefficients
with which to repeat the process.

> -- |A more accurate method for finding square roots
> -- than @(realToFrac . sqrt)@, operating semi-symbolically.
> sqrti :: Integral a => a -> CF a
> sqrti = CF . sqrti' 1 0 1

> -- |Produce a continued fraction for \(\frac{m\sqrt{x}+r}{d}\).
> sqrti' :: Integral a => a -> a -> a -> a -> [a]
> sqrti' m r d x
>     | square (d*f - r) == square m * x = [f]
>     | otherwise  =  f : sqrti' (div m' g) (div r' g) (div d' g) x
>     where f = ipartOfSqrt m r d x `asTypeOf` x
>           m' = d * m
>           r' = -d * r + square d * f
>           d' = square m * x - square (r - d * f)
>           g  = gcd d' $ gcd m' r'

> -- |Binary search for floor of \(\frac{m\sqrt{x}+r}{d}\).
> -- This avoids floating point math and associated precision loss.
> ipartOfSqrt :: (Real a, Integral b) => a -> a -> a -> a -> b
> ipartOfSqrt m r d x = fromIntegral $ ipart' 0 (y + 1) (avg 0 y)
>     where y = floor (toRational x) :: Integer
>           avg a b = floor (frac (a + b) 2)
>           ipart' a b g
>               | abs (a - b) <= 1 = g
>               | otherwise = case compare
>                                  (square (d * fromIntegral g - r))
>                                  (square m * x) of
>                               EQ -> g
>                               LT -> ipart' g b (avg g b)
>                               GT -> ipart' a g (avg a g)

We can then define the square root of any (nonnegative) rational.

> -- |The square root of a rational number,
> -- operating semi-symbolically.
> -- Provides accurate results, unlike @(realToFrac . sqrt)@.
> sqrtq :: Integral a => Ratio a -> CF a
> sqrtq x = sqrti (numerator x) / sqrti (denominator x)


\subsection{Good approximations without hard-coding}

A modification of @gosper4@ can produce
a sequence of convergents without recalculation.
With this we can output a good approximation
without having to hard-code which numbered convergent
we think should suffice.

> convergents :: Real a => a -> a -> a -> a -> CF a -> [Rational]
> convergents a _ c _ (CF [])
>     | c == 0     =  []
>     | otherwise  =  [frac a c]
> convergents a b c d (CF (x:xs))
>     = (if c /= 0 then (:) (frac a c) else id)
>       $ convergents (x * a + b) a (x * c + d) c (CF xs)

> findEq :: [Rational] -> Rational
> findEq [] = infinityF
> findEq (x:[]) = x
> findEq (x:y:xs)
>     | realToFrac x == (realToFrac y :: Double) = x
>     | otherwise = findEq (y : xs)

> -- |The first convergent of a number
> -- that provides as much precision as a @Double@ would.
> converge :: Real a => CF a -> CF a
> converge = fromRational . findEq . convergents 1 0 0 1

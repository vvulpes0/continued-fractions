# continued-fractions
![Current Version](https://img.shields.io/badge/version-0.1-informational.svg)
![License](https://img.shields.io/github/license/vvulpes0/continued-fractions)
![Issues](https://img.shields.io/github/issues/vvulpes0/continued-fractions)


## Table of contents
* [Introduction](#introduction)
* [Installation](#installation)
* [Examples](#examples)

## Introduction
As Bill Gosper once said:

> Contrary to everybody … continued fractions
> are not only perfectly amenable to arithmetic,
> they are amenable to perfect arithmetic.

There are plenty of Haskell libraries
that construct continued fraction representations,
but to my knowledge there are no libraries
that implement arithmetic on such representations.
This library fills that gap.

With this library, one can construct continued fractions
for any rational number or the square root thereof exactly.
Then arithmetic with no loss of precision is possible.

When using these representations,
one must consider that most operations
that would turn an irrational into a rational
will never halt, and may produce no output at all.

## Installation
The Glasgow Haskell Compiler (GHC)
is the only officially supported compiler,
and cabal-install is required for installation.
The easiest way to obtain these is to install the
[Haskell Platform](https://www.haskell.org/platform).
Only GHC 8.10.1 has been officially tested,
but older versions may work just as well.
For relatively new versions of cabal-install,
installation is simply:

    cabal v2-install --lib ContinuedFraction

The library should then be available for use.

## Examples
```haskell
> import Data.ContinuedFraction
> sqrti 4
CF [2]
> convergent 10 (sqrti 2)
CF [1,2,2,2,2,2,2,2,2,2]
> convergent 10 (sqrti 2 + sqrtq (3/4))
CF [2,3,1,1,3,6,2,2,2,5]
> converge ((sqrti (5) + 1)/2) -- the golden ratio
CF [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2]
> 3/4 + 22/7 :: SCF
CF [3, 1, 8, 3]
> realToFrac (3/4 + 22/7 :: SCF)
3.892857142857143
> realToFrac . converge . recip $ sqrti 2
0.7071067811865476
```

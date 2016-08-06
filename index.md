---
title: Home
date: 2016/08/06 20:51:38 JST
author: Hiromi ISHII
---

Overview
========
The `computational-algebra` is the computational algebra system, implemented as a Embedded Domain Specific Language (*EDSL*) in [Haskell](https://www.haskell.org).
This library provides many functionality for computational algebra, especially ideal computation such as Groebner basis calculation.

Thanks to Haskell's powerful language features, this library achieves the following goals:

Type-Safety
:   Haskell's static type system enforces **static correctness** and prevents you from violating invariants. 

Flexibility
:   With the powerful type-system of Haskell,
    we can write **highly abstract program** resulted in **easy-to-extend** system.

Efficiency
:   Haskell comes with many **aggressive optimization mechanism** and **parallel computation features**,
    which enables us to write efficient program.

This package currently provides the following functionalities:

* Groebner basis calculation w.r.t. arbitrary monomial ordering
    * Currently using Buchberger's algorithm with some optimization
    * Faugere's F_4 algorithms is experimentally implemented,
	  but currently not as fast as Buchberger's algorithm 
* Computation in the (multivariate) polynomial ring over arbitarary field and its quotient ring
    * Ideal membership problem
    * Ideal operations such as intersection, saturation and so on.
    * Zero-dimensional ideal operation and conversion via FGLM algorithm
    * Variable elimination
* Find numeric solutions for polynomial system with real coefficient

Requirements and Installation
=============================
Old version of this package is [uploaded on Hackage](hackage:computational-algebra), but it's rather outdated.
Most recent version of `computational-algebra` is developed on [GitHub](github:konn/computational-algebra).

It uses the most agressive language features recently implemented in [Glasgow Haskell Compiler](https://www.haskell.org/ghc/), so it requires at least GHC 8.0.1 and
also it depends on many packages currently not available on Hackage, but you can install it fairly easily with help of [The Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/).

```zsh
$ curl -sSL https://get.haskellstack.org/ | sh
  # if you haven't install Stack yet
$ git clone https://github.com/konn/computational-algebra
$ cd computational-algebra
$ stack build
```

In addition, you may need to install GSL and LAPACK (for matrix computation) beforehand.
You can install them via Homebrew (OS X), `apt-get`, or other major package management systems.

Example
=======

```haskell
{-# LANGUAGE ConstraintKinds, DataKinds, GADTs, KindSignatures     #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude              #-}
{-# LANGUAGE NoMonomorphismRestriction, QuasiQuotes, TypeOperators #-}
module Main where
import Algebra.Algorithms.Groebner
import Algebra.Field.Finite
import Algebra.Prelude
import Data.Type.Ordinal.Builtin

-- | 0-th variable of polynomial ring with at least one variable.
-- Variables are 0-origin.
x :: (KnownNat n, CoeffRing r, IsMonomialOrder n order, (0 :< n) ~ 'True)
  => OrderedPolynomial r order n
x = var [od|0|]

-- | 1-st variable of polynomial ring with at least two variable.
y :: (KnownNat n, CoeffRing r, IsMonomialOrder n order, (1 :< n) ~ 'True)
  => OrderedPolynomial r order n
y = var [od|1|]

-- | The last variable of
z :: Polynomial Rational 3
z = var [od|2|]

-- | f in QQ[x,y,z]
f :: OrderedPolynomial Rational Grevlex 3
f = 1%2*x*y^2 + y^2

-- | map f to the F_5[x,y,z], where F_5 = ZZ/5ZZ
f' :: Polynomial (F 5) 3
f' = mapCoeff (\r -> fromInteger (numerator r) / fromInteger (denominator r) ) f

-- | ideal of QQ[x,y,a,b,c,s]
heron :: Ideal (OrderedPolynomial Rational Lex 6)
heron = toIdeal [ 2 * s - a * y
                , b^2 - (x^2 + y^2)
                , c^2 - ((a - x)^2 + y^2)
                ]
  where
    -- | Get the last four variables of QQ[x,y,a,b,c,s]
    [_, _, a, b, c, s] = vars

main :: IO ()
main = do
  print f
  print f'
  print $ x * f'^2
  print $ calcGroebnerBasis heron
  -- print $ f' * 5 + f -- ^ Type error!
```

Type Interface
==============
`computational-algebra` provides well-typed interface. In this section, we will see how this package represents mathematical objects by type.

## Type-level natural numbers and singletons
As we will see below, we use type-level natural number to indicate the number of variables. So, let's see how we express natural numbers as type.

The [`type-natural` package](hackage:type-natural) provides the functionality to treat type-level natural numbers seamlesly.
That library also provides Peano numerals, but it is enough to use `*.Builtin` module for our purposes.
<!-- It provides quasiquote `snat`{.haskell} to express the natural numbers. For example, we can write `[nat| 40 |]`{.haskell}, `[nat|100|]`{.haskell} and so on. -->

Sometimes we have to specify the type-level natural as function argument explicitly. We use so-called **singleton**s for the type natural in such case.
To generate singletons for type-level naturals, we can use `snat`{.haskell} quasiquoter from `Data.Type.Natural.Builtin`{.haskell} in `type-natural` package.
Furthermore, the [`singletons` package](hackage:singletons) provides unified way to do with singletons.
For more detail, please read the [original paper of singletons](http://www.cis.upenn.edu/~eir/papers/2012/singletons/paper.pdf).

## Algebraic structures and operations
To express algebraic structures, we use the type classes from [`algebra`](http://hackage.haskell.org/package/algebra ) package.
For example, if we say "k is a *field*", it means that `k`{.haskell} is an instance of `Field`{.haskell} class from `algebra` package.
As mentioned above, we can compute the Groebner basis for ideals in polynomial rings over arbitary field. This means we can compute bases for those with coefficient field an instance of `Field`. In addition, `computational-algebra` provides `NoetherianRing`{.haskell} class for completion.

The ring and field operations for objects implemented in this package is provided as the instance function of `Ring`{.haskell} and `Field`{.haskell} classes.
Of course, this package also provides instances for the standard type classes such as `Num`{.haskell} and `Fractional`{.haskell}, but we recommend to use the operation from `algebra` with `NoImplicitPrlude`{.haskell} option. We provide the convenient module `Algebra.Ring.Prelude`{.haskell} to use with `NoImplicitPrlude`{.haskell} option.
Also we will plan to provide drop-in replacement for `Prelude`{.haskell} module.

## Polynomial ##
The type for the polynomials and operations are defined in `Algebra.Ring.Polynomial`{.haskell} module.

`OrderedPolynomial r ord n`{.haskell} represents

* the `n`{.haskell}-variate polynomial ring, 
* over the coefficient ring `r`{.haskell},
* with terms sorted w.r.t. [*the monomial ordering*](http://en.wikipedia.org/wiki/Monomial_order) `ord`{.haskell}.

In the above, `n`{.haskell} should have kind `Nat`{.haskell} and `r`{.haskell} should be at least an instance of `NoetherianRing`{.haskell}, but usually the `Field`{.haskell} for practical usage. The monomial ordering `ord`{.haskell} should be the instance of `IsMonomialOrder`{.haskell}.
More precisely, `ord`{.haskell} must have instance for `IsMonomial Order n ord`{.haskell} if and only if `ord`{.haskell} stands for some monomial ordering on n-ary polynomial.

Let's see example. $\mathbb{Q}[x,y,z]$ (the trivariate polynomial ring over the rational number) with Lex ordering is represented by the type `OrderedPolynomial Rational Lex 3`{.haskell}. `Polynomial Rational 3`{.haskell} is short for `OrderedPolynomial Rational Grevlex 3`{.haskell}.

## Monomial Orderings ##
By default, `computational-algebra` provides the following monomial orderings:

* `Lex`{.haskell}, the lexicographical order, 
* `Grlex`{.haskell}, the graded lex order, and
* `Grevlex`{.haskell}, the graded reversed lex order.

In addition to the basic monomial orders listed above, we can construct new monomial orderings from existing ones with following: 

* `Graded ord`{.haskell}, the graded order which first compares the grade (i.e. total degree)
  and break the tie with `ord`{.haskell},
* `ProductOrder n ord ord'`{.haskell}, the product order which compares
  first n variables with `ord`{.haskell}, then compare the rest with `ord'`{.haskell}, and
* `WeightOrder ws ord`{.haskell}, weighted order which compares the dot-product
  with ws first and then break the tie with `ord`{.haskell}.

We provide the `Revlex`{.haskell}, the reversed lex order. `Revlex`{.haskell} is **not** the monomial order, but we can construct monomial orderings from it with above constructors. For example, `Graded Revlex`{.haskell} is equivalent to `Grevlex`{.haskell}.

### How to write `IsMonomialOrder`{.haskell} instances?

If you should use the monomial ordering which cannot constructed from the above, and you have proven that ordering is really a monomial ordering, you can just implement an instance for the `IsMonomialOrder`{.haskell}.

In `computational-algebra`{.haskell}, monomials are essentially  represented as `Sized n Int`{.haskell}, the `Int`{.haskell} vector with size `n`{.haskell}.

(stub)

## Quotient ring ##
The type `Quotient k ord n ideal`{.haskell} stands for the quotient ring of n-variate polynomial ring over the field `k`{.haskell}.
In order to distinguish the quotient ring over different ideals, we parametrize ideals in type. But, wait, how to parametrize the ideal information in the type-level?

To solve this problem, we use the Edward Kmett's [reflection](http://hackage.haskell.org/package/reflection ) package.

(stub)

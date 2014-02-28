Computational Algebra Library
==============================
[![Build Status](https://travis-ci.org/konn/computational-algebra.png?branch=master)](https://travis-ci.org/konn/computational-algebra)

Abstract
--------
A statically typed computational algebra library. This package currently focuses on computations in (multivariate) polynomial ring over arbitrary field and its quotient ring. As an application, this library also provides the functionality to solve the polynomial equation system.

This library utilizes GHC's advanced type system to statically guarantee safety, so please use with GHC >= 7.6.*.

Installation
-------------
```sh
$ cabal update
$ cabal install computational-algebra
```

Overview
--------
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

Example
-------

```haskell
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds, NoImplicitPrelude, NoMonomorphismRestriction, QuasiQuotes #-}
module Main where
import Algebra.Prelude
import Algebra.Field.Finite
import Algebra.Ring.Noetherian
import Algebra.Algorithms.Groebner
import Data.Type.Natural
import Data.Type.Ordinal

-- | 0-th variable of polynomial ring with at least one variable.
-- Variables are 0-origin.
x :: (IsPolynomial r n, IsOrder order) => OrderedPolynomial r order (S n)
x = var [od|0|]

-- | 1-st variable of polynomial ring with at least two variable.
y :: (IsPolynomial r n, IsOrder order) => OrderedPolynomial r order (S (S n))
y = var [od|1|]

-- | The last variable of 
z :: Polynomial Rational Three
z = var [od|2|]

-- | f in QQ[x,y,z] 
f :: OrderedPolynomial Rational Grevlex Three
f = 1%2*x*y^2 + y^2

-- | map f to the F_5[x,y,z], where F_5 = ZZ/5ZZ
f' :: Polynomial (F Five) Three
f' = mapCoeff fromRational f

-- | ideal of QQ[x,y,a,b,c,s]
heron :: Ideal (OrderedPolynomial Rational Lex Six)
heron = toIdeal [ 2 * s - a * y
                , b^2 - (x^2 + y^2)
                , c^2 - ((a-x)^2 + y^2)
                ]
  where
    -- | Get the last four variables of QQ[x,y,a,b,c,s]
    [_, _, a, b, c, s] = genVars sSix

main :: IO ()
main = do
  print f
  print f'
  print $ x * f'^2
  print $ calcGroebnerBasis heron
  -- print $ f' * 5 + f -- ^ Type error!
```

Type Interface
--------------
`computational-algebra` provides well-typed interface. In this section, we will see how this package represents mathematical objects by type.

### Type-level natural numbers and singletons ### {#type-nats}
As we will see below, we use type-level natural number to indicate the number of variables. So, let's see how we express natural numbers as type.

We use `Nat`{.haskell} from [`type-natural`](http://hackage.haskell.org/package/type-natural ) package. This package adopt [peano numerals](http://www.haskell.org/haskellwiki/Peano_numbers) to express the number at type-level, that is:

```haskell
data Nat = Z | S Z
```

`Z` stands for 0 and `S n` for n+1. For example, `S Z` stands for 1, `S (S (S Z))` for 3, and so on. With `DataKinds` language extension, we can use `Nat` as kind and `Z` and `S` as type constructors. For more detail, please read my introduction article for the dependently typed programming with Haskell (coming soon).

For the numbers upto 20, `type-natural` provides the type synonym to express these numbers such as:

* `Zero`{.haskell}, `One`{.haskell}, `Two`{.haskell}, `Three`{.haskell}, ..., `Twenty`{.haskell}
* `N0`{.haskell}, `N1`{.haskell}, ..., `N20`{.haskell}.

In addition, the package provides quasiquote `nat` to express the natural numbers. For example, we can write `[nat| 40 |]`{.haskell}, `[nat|100|]`{.haskell} and so on.
Peano numerals consume the same space as itself, sometimes we have to specify `-fcontext-stack=` option to compile the code which includes large type-level natural.

Sometimes we have to specify the type-level natural as function argument explicitly. We use singletons for the type natural in such case. A singleton for a type `t` has exactly one inhabitant and the same structure as `t`. For example, singleton type for `Three = S (S (S Z))`{.haskell} is the type `SNat Three`{.haskell} and its only inhabitant is `SS (SS (SS SZ))`{.haskell}. Also, `type-natural` provides synonyms for singleton natural numbers upto 20, such as `sOne`{.haskell}, `sTwo`{.haskell}, .... and `sN0`, `sN1`, .... and so on. In addition, you should use smart constructors such as `sS` and `sZ` to construct the singleton natural numbers, instead of data constructor `SS` and `SZ`. This sometimes make it easy for the compiler to find some instances.
For more detail, please read the [original paper of singletons](http://www.cis.upenn.edu/~eir/papers/2012/singletons/paper.pdf).

### Algebraic structures and operations ###
To express algebraic structures, we use the type classes from Edward Kmett's [`algebra`](http://hackage.haskell.org/package/algebra ) package.
For example, if we say "k is a *field*", it means that `k` is an instance of `Field`{.haskell} class from `algebra` package.
As mentioned above, we can compute the Groebner basis for ideals in polynomial rings over arbitary field. This means we can compute bases for those with coefficient field an instance of `Field`. In addition, `computational-algebra` provides `NoetherianRing` class for completion.

The ring and field operations for objects implemented in this package is provided as the instance function of `Ring` and `Field` classes. Of course, this package also provides instances for the standard type classes such as `Num` and `Fractional`, but we recommend to use the operation from `algebra` with `NoImplicitPrlude` option. We provide the convenient module `Algebra.Ring.Prelude` to use with `NoImplicitPrlude` option.

### Polynomial ###
The type for the polynomials and operations are defined in `Algebra.Ring.Polynomial`{.haskell} module.

`OrderedPolynomial r ord n`{.haskell} represents

* the `n`{.haskell}-variate polynomial ring, 
* over the coefficient ring `r`{.haskell},
* with terms sorted w.r.t. [*the monomial ordering*](http://en.wikipedia.org/wiki/Monomial_order) `ord`{.haskell}.

In the above, `n` should have kind `Nat`{.haskell} described [above](#type-nats) and `r` should be at least an instance of `NoetherianRing`, but usually the `Field` for practical usage. The monomial ordering `ord` should be the instance of `IsMonomialOrder`.

Let's see example. QQ[x,y,z] (the trivariate polynomial ring over the rational number) with Lex ordering is represented by the type `OrderedPolynomial Rational Lex Three`{.haskell}. `Polynomial Rational Three`{.haskell} is short for `OrderedPolynomial Rational Grevlex Three`{.haskell}.

### Monomial Orderings ###
By default, `computational-algebra` provides the following monomial orderings:

* `Lex`{.haskell}, the lexicographical order, 
* `Grlex`{.haskell}, the graded lex order, and
* `Grevlex`{.haskell}, the graded reversed lex order.

In addition to the basic monomial orders listed above, we can construct new monomial orderings from existing ones with following: 

* `Graded ord`{.haskell}, the graded order which first compares the grade (i.e. total degree)
  and break the tie with `ord`,
* `ProductOrder n ord ord'`{.haskell}, the product order which compares
  first n variables with `ord`, then compare the rest with `ord'`, and
* `WeightOrder ws ord`, weighted order which compares the dot-product
  with ws first and then break the tie with `ord`.

We provide the `Revlex`{.haskell}, the reversed lex order. `Revlex`{.haskell} is **not** the monomial order, but we can construct monomial orderings from it with above constructors. For example, `Graded Revlex`{.haskell} is equivalent to `Grevlex`{.haskell}.

### How to write `IsMonomialOrder` instances? ###

If you should use the monomial ordering which cannot constructed from the above, and you have proven that ordering is really a monomial ordering, you can just implement an instance for the `IsMonomialOrder`.

In `computational-algebra`, monomials are essentially  represented as `Vector Int n`, the `Int`{.haskell} vector with size `n`. 

(stub)

### Quotient ring ###
The type `Quotient k ord n ideal`{.haskell} stands for the quotient ring of n-variate polynomial ring over the field `k`.
In order to distinguish the quotient ring over different ideals, we parametrize ideals in type. But, wait, how to parametrize the ideal information in the type-level?

To solve this problem, we use the Edward Kmett's [reflection](http://hackage.haskell.org/package/reflection ) package.


(stub)

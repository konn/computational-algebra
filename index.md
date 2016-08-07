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
    * Faugere's $F_4$ algorithms is experimentally implemented,
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

Sometimes we have to specify the type-level natural as function argument explicitly. We use so-called **singleton**s for the type natural in such case.
To generate singletons for type-level naturals, we can use `snat`{.haskell} quasiquoter from `Data.Type.Natural.Builtin`{.haskell} in `type-natural` package.
Furthermore, the [`singletons` package](hackage:singletons) provides unified way to do with singletons.
For more detail, please read the [original paper of singletons](http://www.cis.upenn.edu/~eir/papers/2012/singletons/paper.pdf).

For technical reason, the compiler must know the information of specific type-level natural number.
This constraint is expressed as the type-class `KnownNat n`{.haskell} from `GHC.TypeLits`{.haskell} module, where $n$ is type-level natural.
It seems rather noisy to have these constraints all around, but if we have singleton value `sn :: SNat n`{.haskell} for some `n`{.haskell}, then we can give such information to the compiler by `withKnownNat`{.haskell} from `Data.Singletons.Prelude`{.haskell} of `singletons` package:

```haskell
import Data.Singletons.Prelude

func :: KnownNat n => a -> b -> ...

caller :: SNat n -> ...
caller sn = withKnownNat n $ func ...
```

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

* the $n$-variate polynomial ring, 
* over the coefficient ring `r`{.haskell},
* with terms sorted w.r.t. [*the monomial ordering*](http://en.wikipedia.org/wiki/Monomial_order) `ord`{.haskell}.

In the above, `n`{.haskell} should have kind `Nat`{.haskell} and `r`{.haskell} should be at least an instance of `NoetherianRing`{.haskell}, but usually the `Field`{.haskell} for practical usage. The monomial ordering `ord`{.haskell} should be the instance of `IsMonomialOrder`{.haskell}.
More precisely, `ord`{.haskell} must have instance for `IsMonomial Order n ord`{.haskell} if and only if `ord`{.haskell} stands for some monomial ordering on n-ary polynomial.

Let's see example. $\mathbb{Q}[x,y,z]$ (the trivariate polynomial ring over the rational number) with Lex ordering is represented by the type `OrderedPolynomial Rational Lex 3`{.haskell}. `Polynomial Rational 3`{.haskell} is short for `OrderedPolynomial Rational Grevlex 3`{.haskell}.

### Abstract type-classes for Polynomials
Sometimes, one might want to use different implementation for polynomials optimized to specific task.
For such a purpose, we provide two abstract type-classes `IsPolynomial`{.haskell} and `IsOrderedPolynomial`{.haskell}, defined in `Algebra.Ring.Polynomial.Class`{.haskell} module.
Indeed, many algebraic operations for `OrderedPolynomial`{.haskell} are provided via these classes.

The first `IsPolynomial`{.haskell} class abstracts polynomial rings by the universality offree commutative algebra over commutative ring.
The instance `IsPolynomial poly`{.haskell} means "`poly`{.haskell} is a polynomial ring".
The class comes with two associated types: `Arity`{.haskell} and `Coefficient`{.haskell}.
For example, we have the following instance for `OrderedPolynomial`{.haskell}:
```haskell
instance (CoeffRing r, IsMonomialOrder n ord)
      => IsPolynomial (OrderedPolynomial r ord n) where
  type Arity (OrderedPolynomial r ord n) = n
  type Coefficient (OrderedPolynomial r ord n) = r
  ...
```
As their name indicates, `Arity poly`{.haskell} stands for the *arity* of `poly`{.haskell}, that is, the number of variables of `poly`{.haskell} and `Coefficient poly`{.haskell} stands for the coefficient ring of `poly`{.haskell}.
The essential class functions of it is `var`{.haskell} and `liftMap`{.haskell}:

```haskell
class IsPolynomial poly where
  var     :: Ordinal (Arity poly) -> poly
  liftMap :: (Module (Scalar (Coefficient poly)) alg,
              Ring alg, Commutative alg)
          => (Ordinal (Arity poly) -> alg) -> poly -> alg
```

`var n`{.haskell} stands for the $n$-th variable of poly.
The type `Ordinal n`{.haskell} is provided in `Data.Type.Ordinals.Builtin`{.haskell} of `type-natural` package, and it stands for the natural numbers less than n.
So, in the context of polynomial, you can think `Ordinal n`{.haskell} as "variable of $n$-variate polynomial".
One can construct ordinals safely by the quasiquoter `od`{.haskell} provided in `Data.Type.Ordinal.Builtin`{.haskell}, when we use `QuasiQutoes`{.haskell} language extension.
For example, `[od|3|]`{.haskell} stands for the third ordinal.
`[od|3|] :: Ordinal 4`{.haskell} typechecks, but `[od|3|] :: Ordinal 2`{.haskell} is rejected in compile-time[^1].


The latter function `liftMap`{.haskell} seems to have odd type, but it is just an *algebraic substitution mapping*.
First, `f :: Ordinal n -> A`{.haskell} can be seen as "$A$-valued assignment for each variable".
Then `liftMap f p`{.haskell} extends f onto entire polynomial ring $R[X_1,\ldots,X_n]$, just substituting each variables in `p`{.haskell} using `f`{.haskell} and taking products in $A$.
These are what we have calld "the universality of free algebra over commutative rings", as pictured the following diagram:

![Universality of free algebra](images/free-alg-univ.svg ) 

Although, we can derive other algebraic operations from these two functions in theory, but for the practical purpose, `IsPolynomial`{.haskell} class have other algebraic operations as its member functions, which can be overridden by instance-specific optimized implementation.

### Polynomials and Monomial Orderings

`IsPolynomial`{.haskell} class doesn't incorporate any information on monomial orderings.
Polynomial rings with operations related monomial orderings is abstracted in `IsOrderedPolynomial`{.haskell}.
This class comes with associated type `MOrder`{.haskell}, which stands for the monomial ordering of given polynomial type:

```haskell
instance (...) => IsOrderedPolynomial (OrderedPolynomial r ord n) where
  type MOrder (OrderedPolynomial r ord n) = ord
  ...
```

This class provide the interfaces to retrieve information related to monomial orderings, such as `leadingTerm`{.haskell}, `leadingMonomial`{.haskell} and `leadingCoefficient`{.haskell}.

By default, `computational-algebra` provides the following monomial orderings:

* `Lex`{.haskell}, the lexicographical order, 
* `Grlex`{.haskell}, the graded lex order, and
* `Grevlex`{.haskell}, the graded reversed lex order.

In addition to the basic monomial orders listed above, we can construct new monomial orderings from existing ones with following: 

* `Graded ord`{.haskell}, the graded order which first compares the grade (i.e. total degree)
  and break the tie with `ord`{.haskell},
* `ProductOrder n m ord ord'`{.haskell}, the product order which compares
  first n variables with `ord`{.haskell}, then the rest $m$ variables with `ord'`{.haskell}, and
* `WeightOrder ws ord`{.haskell}, weighted order which compares the dot-product
  with ws first and then break the tie with `ord`{.haskell}.

We provide the `Revlex`{.haskell}, the reversed lex order. `Revlex`{.haskell} is **not** the monomial order, but we can construct monomial orderings from it with above constructors. For example, `Graded Revlex`{.haskell} is equivalent to `Grevlex`{.haskell}.

Other utility functions and related type-classes are defined in the module `Algebra.Ring.Polynomial.Monomial`{.haskell}.

### How to write `IsMonomialOrder`{.haskell} instances?

If you should use the monomial ordering which cannot constructed from the above, and you have proven that ordering is really a monomial ordering, you can just implement an instance for the `IsMonomialOrder`{.haskell}.

In `computational-algebra`{.haskell}, monomials are essentially  represented as `Sized n Int`{.haskell}, the `Int`{.haskell} vector of size $n$ and each $k$-th element stands for the power of $k$-th variable.

More precisely, there are two types representing monomials: `Monomial`{.haskell} and `OrderedMonomial`{.haskell}.
The type `Monomial n`{.haskell} is just a synonym of `Sized n Int`{.haskell}, which is mathematically equal to $\mathbb{N}^n$.
You can manipulate the value of `Monomial n`{.haskell} with functions provided by `Data.Sized.Builtin`{.haskell} from [`sized` package](hackage:sized).

`OrderedMonomial`{.haskell} is just a newtype wrapping `Monomial`{.haskell} tagged with additional monomial ordering information:
```haskell
newtype OrderedMonomial ord n =
        OrderedMonomial { getMonomial :: Monomial n }
```
Note that type parameter `ord`{.haskell} doesn't appear in the right hand side of its definition.
Such type-parameters are called *phantom type*s.
The type `OrderedMonomial`{.haskell} itself doesn't incorporate any implementation of monomial ordering, but its phantom type paramter `ord`{.haskell} carries such information.

We use `IsOrder`{.haskell} classs to retrieve ordering infromation from such pahntom types:
```haskell
class IsOrder n ord where
  cmpMonomial :: Proxy ord -> Monomial n -> Monomial n -> Ordering
```
That is, `IsOrder n ord`{.haskell} stands for the "`ord`{.haskell} is ordering on $\mathbb{N}^n$" and `cmpMonomial`{.haskell} is the function to compare two monomials.
The first argument `Proxy ord`{.haskell} is just to indicate "which order to use", otherwise `cmpMonomial` can be ambiguous.
For example, we have following instance for `Lex`{.haskell} [^2]:

```haskell
instance KnownNat n => IsOrder n Lex where
  cmpMonomial _ NilL      NilL      = EQ
  cmpMonomial _ (n :< ns) (m :< ms)
    | n < m     = LT
    | n > m     = GT
    | otherwise = cmpMonomial ns ms
```

The type `Ordering`{.haskell} is one of the Haskell's standard data-type which stands for the "comparison result" of two values; that is, `compare n m`{.haskell} returns `LT`{.haskell} if $n < m$, `GT`{.haskell} if $n > m$ and `EQ`{.haskell} if they are equal.
Haskell's `Monoid`{.haskell} type-class and `Data.Ord`{.haskell} module provides more convenient way to write such a comparison function.
For example, we can rewrite above definition as follows:
```haskell
cmpMonomial _ ns ms = mconcat (zipWithSame compare ns ms)
```
where `zipWithSame`{.haskell} is imported from `Data.Sized.Builtin`{.haskell} from `sized` package.
Monoid opertions for `Ordering`{.haskell} can be considered as left-biased "breaking tie" operator.

The `Ord`{.haskell} instance for `Monomial ord n`{.haskell} is defined if `IsOrder n ord`{.haskell} is defined.
But the above definition only requires `ord` to be "total order"; it should be monomial ordering to treat with polynomials.
So, if one have proven that some `ord` is actually a monomial order, one should declare the instance for `IsMonomialOrder`{.haskell} as below:

```haskell
instance IsMonomialOrder n Lex
```

`IsMonomialOrder`{.haskell} doesn't provide any additional member function, but it is defined to distinguish mere ordering with monomial ordering.
It is instance-implementor's responsibility to assure that it is really a monomial ordering[^3].

So in this way, we can define the custom monomial ordering.

There is yet another type-class for monomial orderings: **`IsStrongMonomialOrder`{.haskell}**.
`IsOrder`{.haskell} and `IsMonomialOrder`{.haskell} takes fixed arity as its parameter,
but sometimes we require orderings to work with arbitarary many variables.
If some specific oreder `ord` has `IsMonomialOrder n ord` for each $n$, then GHC automatically generates the instance `IsStrongMonomialOrder ord`{.haskell}.
One can use `cmpAnyMonomial` function to compare monomials with different arity for such an ordering.

## Variants of polynomial types
There are several polynomial types shipped with this library other than `OrderedPolynomial`{.haskell}:

* `Unipol r`{.haskell} defined in `Algebra.Ring.Polynomial.Univariate`{.haskell}, which stands for univariate polynomial $R[x]$ over some commutative ring $R$.
  It comes with operations optimized to univariate polynomials, such as efficient substitution using [Horner's rule](https://en.wikipedia.org/wiki/Horner%27s_method)
  and fast multplication using [Karatsuba algorithm](https://en.wikipedia.org/wiki/Karatsuba_algorithm).
* `LabPolynomial poly vars` defined in `Algebra.Ring.Polynomial.Labeled`{.haskell}.
  It wraps existing polynomial type `poly`{.haskell} and have the same operation with it, but it *labels* each variables in `poly`{.haskell} by `vars`{.haskell}.
  Parameter `vars`{.haskell} is the type-level list of unique symbols which have the length equal to the arity of `poly`{.haskell} and.
  For example:
    ```haskell
    LabPolynomial (OrderedPolynomial Rational Grevlex 3) '["x", "y", "z"]
    ```
  is essentially the same as `OrderedPolynomial Rational Grevlex 3`{.haskell} ,
  but each variable is "labeled" with names $x$, $y$ and $z$ when we prrety-print values.
  It also provides strongly-typed inclusion mapping. For exmap,e. compiler can statically
  generate inclusion mapping from `LabPolynomial poly '["x", "y", "z"]`{.haskell} to
  `LabPolynomial poly '["z", "a", "x", "b", "c"]`{.haskell} .

Of course, users can define their custom polynomial types and made them instance of `IsOrdredPolynomial`{.haskell}.
The module `Algebra.Ring.Polynomial.Class`{.haskell} provides the function `injectVars`{.haskell}, which converts between different polynomial type with the same coefficient, just mapping each variable to corresponding one with the same index in the target.
Sometimes (e.g. variable elimination) one might want to permute variables.
In such a case, you can just use `liftMap`{.haskell}, `subst`{.haskell} or their variants.
    
## Quotient ring ##
The type `Quotient k ord n ideal`{.haskell} stands for the quotient ring of n-variate polynomial ring over the field `k`{.haskell}.
In order to distinguish the quotient ring over different ideals, we parametrize ideals in type. But, wait, how to parametrize the ideal information in the type-level?

To solve this problem, we use the Edward Kmett's [reflection](http://hackage.haskell.org/package/reflection ) package.

(stub)

[^1]: One can also construct ordinals using integer literals of Haskell, like `3 :: Ordinal 4`{.haskell}, but it is unsafe and so highly unrecommended.
For example, although `[od|3|] :: Ordinal 2`{.haskell} is rejected by compiler as expected, but `3 :: Ordinal 2`{.haskell} passes the compile-time typecheck and throws run-time error.
This is due to the mechanism of Haskell's literal desugaring.

[^2]: Indeed, actual implementation is more optimized.

[^3]: Actually, recent GHC's type-level functionality is strong enough to
require instances to include static proof of correctness;
but it is too expensive for library writers compared to the result we gain,
hence we haven't include such "proof requirement" to class.
Another reason is that, it makes difficult to treat *dynamically generated orderings*,
which occurs in some applications such as integer programming.

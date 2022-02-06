---
title: Home
date: 2018/01/05 14:00:00 JST
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

Type Interface for Polynomials and Algebraic Structures
=======================================================
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
This constraint is expressed as the type-class[`KnownNat n`{.haskell}](hackage:base/docs/GHC-TypeLits.html#t:KnownNat) from `GHC.TypeLits`{.haskell} module, where $n$ is type-level natural.
It seems rather noisy to have these constraints all around, but if we have singleton value `sn :: SNat n`{.haskell} for some `n`{.haskell}, then we can give such information to the compiler by [`withKnownNat`{.haskell}](hackage:singletons/docs/Data-Singletons-TypeLits.html#v:withKnownNat) from [`Data.Singletons.TypeLits`{.haskell}](hackage:singletons/docs/Data-Singletons-TypeLits.html) of `singletons` package:

```haskell
import Data.Singletons.TypeLits

func :: KnownNat n => a -> b -> ...

caller :: SNat n -> ...
caller sn = withKnownNat n $ func ...
```

## Algebraic structures and operations
To express algebraic structures, we use the type classes from [`algebra`](http://hackage.haskell.org/package/algebra ) package.
For example, if we say "k is a *field*", it means that `k`{.haskell} is an instance of `Field`{.haskell} class from `algebra` package.
As mentioned above, we can compute the Groebner basis for ideals in polynomial rings over arbitary field. This means we can compute bases for those with coefficient field an instance of `Field`.

The ring and field operations for objects implemented in this package is provided as the instance function of `Ring`{.haskell} and `Field`{.haskell} classes.
Of course, this package also provides instances for the standard type classes such as `Num`{.haskell} and `Fractional`{.haskell}, but we recommend to use the operation from `algebra` with `NoImplicitPrlude`{.haskell} option. We provide the convenient module [`Algebra.Prelude`{.haskell}](doc:Algebra-Prelude.html) to use with `NoImplicitPrlude`{.haskell} option.

## Polynomial ##

The type for the polynomials and operations are defined in [`Algebra.Ring.Polynomial`{.haskell}](doc:Algebra-Ring-Polynomial.html) module.

[`OrderedPolynomial r ord n`{.haskell}](doc:Algebra-Ring-Polynomial.html#t:OrderedPolynomial) represents

* the $n$-variate polynomial ring,
* over the coefficient ring `r`{.haskell},
* with terms sorted w.r.t. [*the monomial ordering*](http://en.wikipedia.org/wiki/Monomial_order) `ord`{.haskell}.

In the above, `n`{.haskell} should have kind `Nat`{.haskell} and `r`{.haskell} should be at least an instance of [`CoeffRing`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:CoeffRing), which is essentially equivalent to "Commutative Ring with decidable equality", but usually the [`Field`{.haskell}](docs/algebra-4.3/Numeric-Field-Class.html#t:Field) for practical usage. The monomial ordering `ord`{.haskell} should be the instance of [`IsMonomialOrder`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:IsMonomialOrder).
More precisely, `ord`{.haskell} must have instance for `IsMonomial Order n ord`{.haskell} if and only if `ord`{.haskell} stands for some monomial ordering on n-ary polynomial.

Let's see example. $\mathbb{Q}[x,y,z]$ (the trivariate polynomial ring over the rational number) with Lex ordering is represented by the type `OrderedPolynomial Rational Lex 3`{.haskell}. `Polynomial Rational 3`{.haskell} is short for `OrderedPolynomial Rational Grevlex 3`{.haskell}.

### Abstract type-classes for Polynomials
Sometimes, one might want to use different implementation for polynomials optimized to specific task.
For such a purpose, we provide two abstract type-classes [`IsPolynomial`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:IsPolynomial) and [`IsOrderedPolynomial`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:IsOrderedPolynomial), defined in [`Algebra.Ring.Polynomial.Class`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html) module.
Indeed, many algebraic operations for `OrderedPolynomial`{.haskell} are provided via these classes.

The first `IsPolynomial`{.haskell} class abstracts polynomial rings by the universality offree commutative algebra over commutative ring.
The instance `IsPolynomial poly`{.haskell} means "`poly`{.haskell} is a polynomial ring".
The class comes with two associated types: [`Arity`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:Arity) and [`Coefficient`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:Coefficient).
For example, we have the following instance for `OrderedPolynomial`{.haskell}:
```haskell
instance (CoeffRing r, IsMonomialOrder n ord)
      => IsPolynomial (OrderedPolynomial r ord n) where
  type Arity (OrderedPolynomial r ord n) = n
  type Coefficient (OrderedPolynomial r ord n) = r
  ...
```
As their name indicates, `Arity poly`{.haskell} stands for the *arity* of `poly`{.haskell}, that is, the number of variables of `poly`{.haskell} and `Coefficient poly`{.haskell} stands for the coefficient ring of `poly`{.haskell}.
The essential class functions of it is [`var`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:var) and [`liftMap`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:liftMap):

```haskell
class IsPolynomial poly where
  var     :: Ordinal (Arity poly) -> poly
  liftMap :: (Module (Scalar (Coefficient poly)) alg,
              Ring alg, Commutative alg)
          => (Ordinal (Arity poly) -> alg) -> poly -> alg
```

`var n`{.haskell} stands for the $n$-th variable of poly.
The type `Ordinal n`{.haskell} is provided in [`Data.Type.Ordinal.Builtin`{.haskell}](hackage:type-natural/docs/Data-Type-Ordinal-Builtin.html) of `type-natural` package, and it stands for the natural numbers less than n.
So, in the context of polynomial, you can think `Ordinal n`{.haskell} as "variable of $n$-variate polynomial".
One can construct ordinals safely by the quasiquoter [`od`](hackage:type-natural/docs/Data-Type-Ordinal-Builtin.html#v:od) provided in `Data.Type.Ordinal.Builtin`{.haskell}, when we use `QuasiQutoes`{.haskell} language extension.
For example, `[od|3|]`{.haskell} stands for the third ordinal.
`[od|3|] :: Ordinal 4`{.haskell} typechecks, but `[od|3|] :: Ordinal 2`{.haskell} is rejected in compile-time[^1].


The latter function `liftMap`{.haskell} seems to have odd type, but it is just an *algebraic substitution mapping*.
First, `f :: Ordinal n -> A`{.haskell} can be seen as "$A$-valued assignment for each variable".
Then `liftMap f p`{.haskell} extends f onto entire polynomial ring $R[X_1,\ldots,X_n]$, just substituting each variables in `p`{.haskell} using `f`{.haskell} and taking products in $A$.
These are what we have calld "the universality of free algebra over commutative rings", as pictured the following diagram:

<!-- ![Universality of free algebra](images/free-alg-univ.svg )  -->

$$\begin{xy}
\xymatrix @C=10ex @R=15ex {
R[X_1, \ldots, X_n] \ar @{.>}[r]^-{\mathop{\mathtt{liftMap}} f} & A\\
\{X_1, \ldots, X_n\} \ar[u]^{\mathtt{var}} \ar[ur]_{f}
}
\end{xy}$$

Although, we can derive other algebraic operations from these two functions in theory, but for the practical purpose, `IsPolynomial`{.haskell} class have other algebraic operations as its member functions, which can be overridden by instance-specific optimized implementation.

### Polynomials and Monomial Orderings

`IsPolynomial`{.haskell} class doesn't incorporate any information on monomial orderings.
Polynomial rings with operations related monomial orderings is abstracted in [`IsOrderedPolynomial`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:IsOrderedPolynomial).
This class comes with associated type [`MOrder`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#t:MOrder), which stands for the monomial ordering of given polynomial type:

```haskell
instance (...) => IsOrderedPolynomial (OrderedPolynomial r ord n) where
  type MOrder (OrderedPolynomial r ord n) = ord
  ...
```

This class provide the interfaces to retrieve information related to monomial orderings, such as [`leadingTerm`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:leadingTerm), [`leadingMonomial`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:leadingMonomial) and [`leadingCoeff`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:leadingCoeff).

By default, `computational-algebra` provides the following monomial orderings:

* [`Lex`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:Lex), the lexicographical order,
* [`Grlex`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:Grlex), the graded lex order, and
* [`Grevlex`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:Grevlex), the graded reversed lex order.

In addition to the basic monomial orders listed above, we can construct new monomial orderings from existing ones with following:

* [`Graded ord`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:Graded), the graded order which first compares the grade (i.e. total degree)
  and break the tie with `ord`{.haskell},
* [`ProductOrder n m ord ord'`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:ProductOrder), the product order which compares
  first n variables with `ord`{.haskell}, then the rest $m$ variables with `ord'`{.haskell}, and
* [`WeightOrder ws ord`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:WeightOrder), weighted order which compares the dot-product
  with ws first and then break the tie with `ord`{.haskell}.

We provide the `Revlex`{.haskell}, the reversed lex order. `Revlex`{.haskell} is **not** the monomial order, but we can construct monomial orderings from it with above constructors. For example, `Graded Revlex`{.haskell} is equivalent to `Grevlex`{.haskell}.

Other utility functions and related type-classes are defined in the module [`Algebra.Ring.Polynomial.Monomial`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html).

### How to write `IsMonomialOrder`{.haskell} instances?

If you should use the monomial ordering which cannot constructed from the above, and you have proven that ordering is really a monomial ordering, you can just implement an instance for the `IsMonomialOrder`{.haskell}.

In `computational-algebra`{.haskell}, monomials are essentially  represented as [`Sized n Int`{.haskell}](doc:Algebra-Internal.html#t:Sized), the `Int`{.haskell} vector of size $n$ and each $k$-th element stands for the power of $k$-th variable.

More precisely, there are two types representing monomials: `Monomial`{.haskell} and `OrderedMonomial`{.haskell}.
The type `Monomial n`{.haskell} is just a synonym of `Sized n Int`{.haskell}, which is mathematically equal to $\mathbb{N}^n$.
You can manipulate the value of `Monomial n`{.haskell} with functions provided by [`Data.Sized.Builtin`{.haskell}](docs/sized-0.2.0.1/Data-Sized-Builtin.html) from [`sized` package](hackage:sized).

[`OrderedMonomial`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:OrderedMonomial) is just a newtype wrapping [`Monomial`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:Monomial) tagged with additional monomial ordering information:
```haskell
newtype OrderedMonomial ord n =
        OrderedMonomial { getMonomial :: Monomial n }
```
Note that type parameter `ord`{.haskell} doesn't appear in the right hand side of its definition.
Such type-parameters are called *phantom type*s.
The type `OrderedMonomial`{.haskell} itself doesn't incorporate any implementation of monomial ordering, but its phantom type paramter `ord`{.haskell} carries such information.

We use [`IsOrder`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:IsOrder) classs to retrieve ordering infromation from such pahntom types:
```haskell
class IsOrder n ord where
  cmpMonomial :: Proxy ord -> Monomial n -> Monomial n -> Ordering
```
That is, `IsOrder n ord`{.haskell} stands for the "`ord`{.haskell} is ordering on $\mathbb{N}^n$" and [`cmpMonomial`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#v:cmpMonomial) is the function to compare two monomials.
The first argument [`Proxy ord`{.haskell}](hackage:base/docs/Data-Proxy.html#t:Proxy) is just to indicate "which order to use", otherwise `cmpMonomial` can be ambiguous.
For example, we have following instance for `Lex`{.haskell} [^2]:

```haskell
instance KnownNat n => IsOrder n Lex where
  cmpMonomial _ NilL      NilL      = EQ
  cmpMonomial _ (n :< ns) (m :< ms)
    | n < m     = LT
    | n > m     = GT
    | otherwise = cmpMonomial ns ms
```

The type [`Ordering`{.haskell}](hackage:base/docs/Prelude.html#t:Ordering) is one of the Haskell's standard data-type which stands for the "comparison result" of two values; that is, `compare n m`{.haskell} returns `LT`{.haskell} if $n < m$, `GT`{.haskell} if $n > m$ and `EQ`{.haskell} if they are equal.
Haskell's [`Monoid`{.haskell}](hackage:base/docs/Data-Monoid.html#t:Monoid) type-class and [`Data.Ord`{.haskell}](hackage:base/docs/Data-Ord.html) module provides more convenient way to write such a comparison function.
For example, we can rewrite above definition as follows:
```haskell
cmpMonomial _ ns ms = mconcat (zipWithSame compare ns ms)
```
where [`zipWithSame`{.haskell}](docs/sized-0.2.0.1/Data-Sized.html#v:zipWithSame) is imported from `Data.Sized.Builtin`{.haskell} from `sized` package.
Monoid opertions for `Ordering`{.haskell} can be considered as left-biased "breaking tie" operator.

The `Ord`{.haskell} instance for `Monomial ord n`{.haskell} is defined if `IsOrder n ord`{.haskell} is defined.
But the above definition only requires `ord` to be "total order"; it should be monomial ordering to treat do polynomials.
So, if one have proven that some `ord` is actually a monomial order, one should declare the instance for [`IsMonomialOrder`{.haskell}](doc:Algebra-Ring-Polynomial-Monomial.html#t:IsMonomialOrder) as below:

```haskell
instance IsMonomialOrder n Lex
```

`IsMonomialOrder`{.haskell} doesn't provide any additional member function, but it is defined to distinguish mere ordering with monomial ordering.
It is instance-implementor's responsibility to assure that it is really a monomial ordering[^3].

So in this way, we can define the custom monomial ordering.

There is yet another type-class for monomial orderings: [**`IsStrongMonomialOrder`{.haskell}**](doc:Algebra-Ring-Polynomial-Monomial.html#t:IsStrongMonomialOrder).
`IsOrder`{.haskell} and `IsMonomialOrder`{.haskell} takes fixed arity as its parameter,
but sometimes we require orderings to work with arbitarary many variables.
If some specific oreder `ord` has `IsMonomialOrder n ord` for each $n$, then GHC automatically generates the instance `IsStrongMonomialOrder ord`{.haskell}.
One can use [`cmpAnyMonomial`](doc:Algebra-Ring-Polynomial-Monomial.html#v:cmpAnyMonomial) function to compare monomials with different arity for such an ordering.

## Variants of polynomial types
There are several polynomial types shipped with this library other than `OrderedPolynomial`{.haskell}:

* [`Unipol r`{.haskell}](doc:Algebra-Ring-Polynomial-Univariate.html#t:Unipol) defined in [`Algebra.Ring.Polynomial.Univariate`{.haskell}](doc:Algebra-Ring-Polynomial-Univariate.html), which stands for univariate polynomial $R[x]$ over some commutative ring $R$.
  It comes with operations optimized to univariate polynomials, such as efficient substitution using [Horner's rule](https://en.wikipedia.org/wiki/Horner%27s_method)
  and fast multplication using [Karatsuba algorithm](https://en.wikipedia.org/wiki/Karatsuba_algorithm).
* [`LabPolynomial poly vars`{.haskell}](doc:Algebra-Ring-Polynomial-Labeled.html#t:LabPolynomial) defined in [`Algebra.Ring.Polynomial.Labeled`{.haskell}](doc:Algebra-Ring-Polynomial-Labeled.html).
  It wraps existing polynomial type `poly`{.haskell} and have the same operation with it, but it *labels* each variables in `poly`{.haskell} by `vars`{.haskell}.
    Parameter `vars`{.haskell} is the type-level list of unique symbols which have the length equal to the arity of `poly`{.haskell} and.
    For example:
    ```haskell
    LabPolynomial (OrderedPolynomial Rational Grevlex 3) '["x", "y", "z"]
    ```
  is essentially the same as `OrderedPolynomial Rational Grevlex 3`{.haskell} ,
  but each variable is "labeled" with names $x$, $y$ and $z$ when we prrety-print values.
  By default, the following type-synonym is provided for convenience:

    ```haskell
    type LabPolynomial' r ord '[x] = LabPolynomial (Unipol r) '[x]
    type LabPolynomial' r ord vs   = LabPolynomial (OrderedPolynomial r ord (Length vs)) vs
    type LabUnipol r x             = LabPolynomial (Unipol r) '[x]
    ```

    It also provides strongly-typed inclusion mapping. For exmaple, compiler can statically
  generate inclusion mapping from `LabPolynomial poly '["x", "y", "z"]`{.haskell} to
  `LabPolynomial poly '["z", "a", "x", "b", "c"]`{.haskell}.
  Furthermore, with GHC's `OverloadedLabels`{.haskell} extension,
  one can use `#<var>`{.haskell} syntax to represent variables safely.
  For example the following type-checks and we can get what we wanted:

    <pre class="sourceCode haskell"><code class="sourceCode haskell">#x <span class="fu">*</span> #y <span class="fu">-</span> <span class="dv">5</span> <span class="fu">*</span> #a<span class="fu">^</span><span class="dv">2</span><span class="ot"> ::</span> <span class="dt">LabPolynomial'</span> <span class="dt">Rational</span> <span class="dt">Grevlex</span> <span class="ch">'[&quot;a&quot;, &quot;x&quot;, &quot;y&quot;]</span></code></pre>

    And <code class="sourceCode haskell"><span class="ot">#z ::</span> <span class="dt">LabUnipol</span>  <span class="dt">Rational</span> <span class="ch">&quot;x&quot;</span></code>
  is statically rejected by compiler at compile-time.
  One limitation is that we can only use `#<var>` syntax only for variables starting with small alphabet and whithout any white-spaces.

Of course, users can define their custom polynomial types and made them instance of `IsOrdredPolynomial`{.haskell}.
The module `Algebra.Ring.Polynomial.Class`{.haskell} provides the function [`injectVars`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:injectVars), which converts between different polynomial type with the same coefficient, just mapping each variable to corresponding one with the same index in the target.
Sometimes (e.g. variable elimination) one might want to permute variables.
In such a case, you can just use [`liftMap`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:liftMap), [`subst`{.haskell}](doc:Algebra-Ring-Polynomial-Class.html#v:subst) or their variants.

## Other polynomial operations
* The module [`Algebra.Ring.Polynomial.Factorise`](doc:Algebra-Ring-Polynomial-Factorise.html) implements the factorisation algorithm for *integer-coefficient univariate* polynomials.
* The module [`Algebra.Algorithms.ZeroDim`](doc:Algebra-Algorithms-ZeroDim.html) provides various algorithms to work with zero-dimensional ideals.

# Provided Algebraic Structures
This package comes with the following types for algebraic structures:

* `Integer`{.haskell} for the ring of integers,
* `Rational`{.haskell} for the rational field,
    * **N.B.** `computational-algebra`'s `Rational`{.haskell} is *different* from the default
      `Rational`{.haskell} type of Haskell.
      This is so because Haskell's `Ratio a`{.haskell} type requires superfluous constraints
      for some algebraic instances.
* Indeed, `Rational` is a type synonym for `Fraction Integer`{.haskell},
  where `Fraction r`{.haskell} stands for the field of fractions of an integral domain `r`.

Aside from the basic structurs above, we have the following structures: *finite fields*, *quotient rings* of polynomial rings, and the field of *algebraic reals*, which we will describe below.

## Finite Fields
[`Algebra.Field.Finite`{.haskell}](doc:Algebra-Field-Finite.html) provides the type-class for finite fields [`FiniteField`{.haskell} ](doc:Algebra-Field-Finite.html#t:FiniteField) and concrete types for prime field [`F p`{.haskell}](doc:Algebra-Field-Finite.html#t:F) which corresponds to $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$.
Note that, this type *doesn't check primarity* of type parameter $p$ (too expensive!).

For other general finite fields other than prime fields (Galois Field), you can use [`Algebra.Field.Galois`{.haskell}](doc:Algebra-Field-Galois.html) module provides types [`GF p n`{.haskell}](doc:Algebra-Field-Galois.html#t:GF), which corresponds to $\mathbb{F}_{p^n}$.
We use [Conway polynomial](https://en.wikipedia.org/wiki/Conway_polynomial_(finite_fields)) for internal representation of Galois Fields.
As a default, `computational-algebra` comes with the information of Conway polynomials for 10th power of 2,3,5,7,11.
Users can easily add the information by just defining [`ConwayPolynomial p n`{.haskell}](doc:Algebra-Field-Galois.html#t:ConwayPolynomial) instace for specific $p$ an $n$ as follows:

```haskell
instance ConwayPolynomial 19 1 where
  conwayPolynomial _ _ = x ^2 + 18 * x + 2
    where x = var 0 :: Unipol (F 19)
```

Although we are planning to implement the functionality to automatically calculate Conway Polynomial,
it is recomended to provide concrete value for each specific $p$ and $n$ to gain the efficiency.
The [`primitive`{.haskell}](doc:Algebra-Field-Galois.html#v:primitive) constant(s) stands for a primitive element of $\mathbb{F}_{p^n}$, i.e. a generator of the multiplicative group $\mathbb{F}_{p^n}^\times$ of units.

### Galois Field computation with arbitrary irreducible polynomials
Although Conway polynomials provides systematic way to treat field extensions,
it takes some computational overhead to compute Conway polynomial.
So if one doesn't need to treat field extension, it is enough to chose arbitrary
irreducible polynomial of degree $n$ with coeffcients in $\mathbb{F}_p$ to do computation.

Internally, the type `GF p n`{.haskell} is synonym for [`GF' p n (Conway p n)`{.haskell}](doc:Algebra-Field-Galois.html#t:GF');
here, [`Conway p n`{.haskell}](doc:Algebra-Field-Galois.html#t:Conway) is a placeholder to retrieve the information of conway polynomial for $\mathbb{F}_{p^n}$.
Actual computation algorithm for Galios fields is defined for `GF' p n f`{.haskell} for `f`{.haskell} carrying information of such an irreducible polynomial.
So if we have some irreducible $p \in \mathbb{F}_p[x]$ with $\deg(p) = n$, one can compute in $\mathbb{F}_{p^n}$ by *reflecting* the information of $p$ to parameter `f`{.haskell}.
The [`reflection` package](hackage:reflection) provides general way to do such a type-level reflection.
Based on that, `Algebra.Field.Galois`{.haskell} provides utility function to reflect given irreducible polynomial to type-level: [`withIrreducible`{.haskell}](doc:Algebra-Field-Galois.html#v:withIrreducible).
Suppose $p \in \mathbb{F}_5$ is irreducible and $\deg(p) = 7$.
Then we can do computation in $\mathbb{F}_{5^7}$ as follows:

```haskell
withIrreducible p $ \pxy ->
  show (sqrt (3 `asProxyTypeOf` pxy))
```

In above, `pxy`{.haskell} is Proxy type to carry the information of *reflected* field and [`asProxyTypeOf`{.haskell}](hackage:base/docs/Data-Proxy.html#v:asProxyTypeOf) forces literals to be interpreted as an element of the reflected field.
One thing to note is that the type variable `f`{.haskell} *dynamically* reflecting polynomial cannot *leak* outside of given functions.
For example, the value `GF' p n f`{.haskell} itself cannot be taken out from `withIrreducible`{.haskell} :

```haskell
withIrreducible p $ \pxy ->
  primitive * (2 * primivite - 1) `asProxyTypeOf` pxy -- type error!
```

In such a situation, one cannot "take out" the reulst directly, but one can still extract the *linear representation* of it:

```haskell
withIrreducible p $ \pxy ->
  linearRepGF (primitive * (2 * primivite - 1) `asProxyTypeOf` pxy) -- OK!
```

On the other hand, if we adopt Conway polynomials as a representation, one can do any computation without any scope restriction as this.
This is because `Conway p n`{.haskell} carries information of an irreducible polynomial *statically*.
So you can define [`Reifies`{.haskell}](hackage:reflection/docs/Data-Reflection.html#t:Reifies) instance for your custom placeholder type and store the information of some specific irreducible polynomial, then you can do such a calculation without any scoping problem:

```haskell
data MyPoly = MyPoly -- ^ Just for placeholder

instance Reifies MyPoly (Unipol (F 5)) where
  reflect _ = x^2 + 2 x + 4

type MyGF5'2 = GF' 5 2 MyPoly
...
```

Also, `Algebra.Field.Galois`{.haskell} comes with monadic function [`generateIrreducible`{.haskell}](doc:Algebra-Field-Galois.html#v:generateIrreducible) to find irreducible polynomials and [`reifyGF'`{.haskell}](doc:Algebra-Field-Galois.html#v:reifyGF') combining these two functions.
There is another function [`withGF'`{.haskell}](doc:Algebra-Field-Galois.html#v:withGF') to retrieve linear representation of elements of Galois Field.
See [documents](doc:Algebra-Field-Galois.html) for more information.

## Quotient rings ##
The type `Quotient k ord n ideal`{.haskell} stands for the quotient ring of n-variate polynomial ring over the field `k`{.haskell}.
In order to distinguish the quotient ring over different ideals, we parametrize ideals in type.
We use the functionalities provided by `reflection`{.haskell} package here, again.

## Algebraic Reals ##
[`Algebra.Field.AlgebraicReal`{.haskell}](doc:Algebra-Field-AlgebraicReal) module provides the type [`Algebraic`{.haskell}](doc:Algebra-Field-AlgebraicReal#t:Algebraic) for the field of *algebraic reals*, i.e. real roots of real coefficient polynomials.

Internally, every algebraic real is represented by the real-coefficient polynomial $f \in \mathbb{R}[X]$ and the interval $I \subseteq \mathbb{R}$ which contains exactly one real root of $f$.

Aside the basic field operations, we currently provide the following operations on algebraic reals:

* [`nthRoot`{.haskell}](doc:Algebra-Field-AlgebraicReal.html#v:nthRoot), where `nthRoot n r`{.haskell} calculates an $n$<sup>th</sup> real root of the given algebraic real `r`.
  If there is no real root, it returns `Nothing`{.haskell}.
* [`approximate`{.haskell}](doc:Algebra-Field-AlgebraicReal.html#v:approximate): `approximate e r`{.haskell} returns an approximating rational number $q$ with $\lvert q - r \rvert < e$.
  There is also a type-generic variant [`approxFractional`{.haskell}](doc:Algebra-Field-AlgebraicReal.html#v:approxFractional), which returns any `Fractional`{.haskell} number (such as `Double`{.haskell} or `Float`{.haskell} ) instead of `Rational`.
* [`realRoots`{.haskell}](doc:Algebra-Field-AlgebraicReal.html#v:realRoots): for the univariate polynomial $f$, `realRoots f`{.haskell} computes all the *real* roots of $f$.
    * There is also [`complexRoots`{.haskell}](doc:Algebra-Field-AlgebraicReal.html#v:complexRoots) which computes all the *complex* roots of $f$, but it comes with really naive implementation and *not ready for the practical usage*.

Links
=====
* [API Documents][apis]

Publication
-----------
* Hiromi ISHII, "[A Purely Functional Computer Algebra System Embedded in Haskell][paper]", preprint (to appear in the Proceedings of The 20th International Workshop on Computer Algebra in Scientific Computing (CASC 2018)).

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

[apis]: ./docs/index.html

[paper]: https://arxiv.org/abs/1807.01456

Computational Algebra Library
==============================
[![pipeline status](https://gitlab.com/konn/computational-algebra/badges/master/pipeline.svg)](https://gitlab.com/konn/computational-algebra/commits/master) 
[![coverage report](https://gitlab.com/konn/computational-algebra/badges/master/coverage.svg)](https://gitlab.com/konn/computational-algebra/commits/master)


**For more detail, please read [Official Project Site](http://konn.github.io/computational-algebra/)**.

Overview
--------
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
------------------------------
Old version of this package is uploaded on [Hackage](http://hackage.haskell.org/package/computational-algebra), but it's rather outdated.
Most recent version of `computational-algebra` is developed on GitHub.

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

Paper
-----
* Hiromi Ishii, _A Purely Functional Computer Algebra System Embedded in Haskell_.
  Computer Algebra in Scientific Computing, pp. 288-303. 20th International Workshop, CASC 2018, Lille, France, September 17-21, 2018, Proceedings ([arXiv][arXiv]).

### [Read More in Official Project Site](http://konn.github.io/computational-algebra/)

[arXiv]: https://arxiv.org/abs/1807.01456
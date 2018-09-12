{-# OPTIONS_GHC -Wno-orphans #-}
{-|
This module provides a series of rewriting rules, replacing invocations on
@'Algebra.Algorithms.Groebner.calcGroebnerBasis'@ and
@'Algebra.Algorithms.Groebner.calcGroebnerBasisWith'@ with @'f5'@ followed by minimisation and reduction of basis.
Since @'f5'@ is the fastest implementation for general Gröbner basis computation in this package,
it is expected that doing this improves the performance.

You can import this module to gain a speed-up also in other functions using @'Algebra.Algorithms.Groebner.calcGroebnerBasis'@ such as
@'Algebra.Algorithms.Groebner.intersection'@ and so on.

Rules replaces __all__ the occurences of @'Algebra.Algorithms.Groebner.calcGroebnerBasis'@ and @'Algebra.Algorithms.Groebner.calcGroebnerBasisWith'@ with @'f5'@.
This effect is pervasive once this module is imported; in general, importing this module in
/library-site/ is __NOT__ good idea.

In addition, we __DO NOT__ rewrite other Buchberger-specific functions such as
@'Algebra.Algorithms.Groebner.calcGroebnerBasisWithStrategy'@ or @'Algebra.Algorithms.Groebner.syzygyBuchberger'@.
-}
module Algebra.Algorithms.Groebner.Signature.Rules () where
import qualified Algebra.Algorithms.Groebner           as GB
import           Algebra.Algorithms.Groebner.Signature (f5)
import           Algebra.Prelude.Core                  (const)
import           Algebra.Prelude.Core                  (convertPolynomial')
import           Algebra.Prelude.Core                  (mapIdeal, (.))

{-# RULES
"calcGroebnerBasis/f5"
  GB.calcGroebnerBasis = GB.reduceMinimalGroebnerBasis . GB.minimizeGroebnerBasis . f5

"calcGroebnerBasisWith/f5"
  GB.calcGroebnerBasisWith = const (GB.reduceMinimalGroebnerBasis . GB.minimizeGroebnerBasis . f5)

"calcGroebnerBasisWith/f5 . convertPolynomial"
  GB.calcGroebnerBasisWith = const (GB.reduceMinimalGroebnerBasis . GB.minimizeGroebnerBasis . f5 . mapIdeal convertPolynomial')
 #-}

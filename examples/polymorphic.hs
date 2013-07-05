{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE ConstraintKinds, NoImplicitPrelude, TypeOperators #-}
module Example where
import Algebra.Algorithms.Groebner
import Algebra.Internal
import Algebra.Ring.Noetherian
import Algebra.Ring.Polynomial
import Data.Ratio
import Data.Type.Natural           hiding (one, zero)
import Numeric.Algebra
import Prelude                     hiding (Fractional (..), Integral (..),
                                    Num (..), (^), (^^))

default (Int)

(^^) :: Unital r => r -> Natural -> r
(^^) = pow

x, y, f, f1, f2 :: Polynomial (Ratio Integer) Two
x = var sOne
y = var sTwo
f = x^^2 * y + x * y^^2 + y^^2
f1 = x * y - 1
f2 = y^^2 - 1

type LexPolynomial r n = OrderedPolynomial r Lex n

heronIdeal :: Ideal (Polynomial (Ratio Integer) (Three :+: Three))
heronIdeal = toIdeal [ 2 * s - a * y
                     , b^^2 - (x^^2 + y^^2)
                     , c^^2 - ( (a-x) ^^ 2 + y^^2)
                     ]
  where
    [x, y, a, b, c, s] = genVars (sThree %+ sThree)


main :: IO ()
main = do
  putStrLn $ unwords ["(" ++ show (x + 1) ++ ")^2", "="
                     , show $ (x + 1) ^^2 ]
  putStrLn $ unwords ["(" ++ show (x + 1) ++ ")(" ++ show (x - 1) ++ ")", "="
                     , show $ (x + 1) * (x - 1) ]
  putStrLn $ unwords ["(" ++ show (x - 1) ++ ")(" ++ show (y^^2 + y - 1) ++ ")", "="
                     , show $ (x - 1) * (y^^2 + y- 1) ]
  putStrLn ""
  putStrLn "*** deriving Heron's formula ***"
  putStrLn "Area of triangles can be determined from following equations:"
  putStrLn "\t2S = ay, b^2 = x^2 + y^2, c^2 = (a-x)^2 + y^2"
  putStrLn ", where a, b, c and S stands for three lengths of the traiangle and its area, "
  putStrLn "and (x, y) stands for the coordinate of one of its vertices"
  putStrLn "(other two vertices are assumed to be on the origin and x-axis)."
  putStrLn "Erasing x and y from the equations above, we can get Heron's formula."
  putStrLn "Using elimination ideal, this can be automatically solved."
  putStrLn "We calculate this with theory of Groebner basis with respect to 'lex'."
  putStrLn "This might take a while. please wait..."
  print $ sTwo `thEliminationIdeal` heronIdeal
  putStrLn "In equation above, X_1, X_2, X_3 and X_4 stands for a, b, c and S, respectively."
  putStrLn "The ideal has just one polynomial `f' as its only generator."
  putStrLn "Solving the equation `f = 0' assuming S > 0, we can get Heron's formula."
  putStrLn ""
  putStrLn "Let's use nother elimination type. We choose Grevlex × Grevlex: "
  print $ thEliminationIdealWith (eliminationOrder sTwo) sTwo heronIdeal
  putStrLn "And weighted order:"
  print $ thEliminationIdealWith (weightedEliminationOrder sTwo) sTwo heronIdeal




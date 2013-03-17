{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE ConstraintKinds, NoImplicitPrelude, TypeOperators #-}
module Example where
import Algebra.Algorithms.Groebner.Monomorphic
import Algebra.Ring.Polynomial.Monomorphic
import Data.Ratio
import Numeric.Algebra
import Prelude                                 hiding (Fractional (..),
                                                Integral (..), (*), (+), (-),
                                                (^), (^^))

default (Int)

(^^) :: Unital r => r -> Natural -> r
(^^) = pow

x, y, f, f1, f2 :: Polynomial (Ratio Integer)
x = injectVar $ Variable 'x' Nothing
y = injectVar $ Variable 'y' Nothing
f = x^^2 * y + x * y^^2 + y^^2
f1 = x * y - one
f2 = y^^2 - one

heron :: [Polynomial (Ratio Integer)]
heron = eliminate [Variable 'x' Nothing, Variable 'y' Nothing] ideal
  where
    [a, b, c, s] = map (injectVar . flip Variable Nothing) "abcS"
    ideal =  [ 2 * s - a * y
             , b^^2 - (x^^2 + y^^2)
             , c^^2 - ( (a-x) ^^ 2 + y^^2)
             ]

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
  print heron
  putStrLn "In equation above, X_1, X_2, X_3 and X_4 stands for a, b, c and S, respectively."
  putStrLn "The ideal has just one polynomial `f' as its only generator."
  putStrLn "Solving the equation `f = 0' assuming S > 0, we can get Heron's formula."


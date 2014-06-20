{-# OPTIONS_GHC -fno-warn-type-defaults #-}
{-# LANGUAGE ConstraintKinds, NoImplicitPrelude, OverloadedStrings #-}
{-# LANGUAGE TypeOperators                                         #-}
module Example where
import           Algebra.Algorithms.Groebner.Monomorphic
import           Algebra.Ring.Polynomial.Monomorphic
import           Algebra.Ring.Polynomial.Parser
import           Data.Either
import           Data.List                               (intercalate)
import qualified Data.Text                               as T
import           Numeric.Algebra
import           Numeric.Field.Fraction
import           Prelude                                 hiding
                                                          (Fractional (..),
                                                          Integral (..), (*),
                                                          (+), (-), (^), (^^))
import           System.IO

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
                     , show $ show $ (x + 1) ^^2 ]
  putStrLn $ unwords ["(" ++ show (x + 1) ++ ")(" ++ show (x - 1) ++ ")", "="
                     , show $ (x + 1) * (x - 1) ]
  putStrLn $ unwords ["(" ++ show (x - 1) ++ ")(" ++ show (y^^2 + y - 1) ++ ")", "="
                     , show $ (x - 1) * (y^^2 + y- 1) ]
  putStrLn "\n==================================================\n"
  idealMembershipDemo
  putStrLn "\n==================================================\n"
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
  putStrLn $ show heron
  putStrLn "In equation above, X_1, X_2, X_3 and X_4 stands for a, b, c and S, respectively."
  putStrLn "The ideal has just one polynomial `f' as its only generator."
  putStrLn "Solving the equation `f = 0' assuming S > 0, we can get Heron's formula."

idealMembershipDemo :: IO ()
idealMembershipDemo = do
  putStrLn "======= Ideal Membership Problem ========"
  putStrLn "Enter ideal generators, separetated by comma."
  putStr "enter: "
  hFlush stdout
  src <- getLine
  let (ls, rs) = partitionEithers $ map (parsePolyn . T.unpack) $ T.splitOn "," $ T.pack src
  putStrLn "Enter the polynomial which you want to know whether it's a member of ideal above or not."
  putStr "enter: "
  hFlush stdout
  src <- getLine
  let ex = parsePolyn src
  case (ls, ex) of
    ([], Right f)
        | f `isIdealMember` rs -> putStrLn $ concat ["[YES!] ", show f, " ∈ 〈", intercalate ", " $ map show rs, "〉"]
        | otherwise            ->
            putStrLn $ concat ["[NO!] ", showRatPolynomial f, " ∉ 〈", intercalate ", " $ map show rs, "〉"]
    _ -> putStrLn "Parse error! try again." >> idealMembershipDemo

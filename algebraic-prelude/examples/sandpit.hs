{-# LANGUAGE OverloadedStrings #-}
module Main where
import AlgebraicPrelude

default (Fraction Integer)

arg, main :: IO ()
arg = do
  putStrLn "Good morning everybody!"
  if True
  then print (5.2 :: Rational)
  else print $ take 5 [1 :: Double,2,345]
main = arg

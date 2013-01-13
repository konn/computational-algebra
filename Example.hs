{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module Example where
import Polynomial

default (Int)

x, y, z :: Polynomial Int Three
x = var sOne
y = var sTwo
z = var sThree

main :: IO ()
main = do
  putStrLn $ unwords ["(" ++ show (x + 1) ++ ")^2", "="
                     , show $ (x + 1) ^2 ]
  putStrLn $ unwords ["(" ++ show (x + 1) ++ ")(" ++ show (x - 1) ++ ")", "="
                     , show $ (x + 1) * (x - 1) ]
  putStrLn $ unwords ["(" ++ show (x - 1) ++ ")(" ++ show (y^2 + y - 1) ++ ")", "="
                     , show $ (x - 1) * (y^2 + y- 1) ]


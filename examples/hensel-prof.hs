{-# LANGUAGE DataKinds #-}
module Main where
import Algebra.Algorithms.Faugere4
import Algebra.LinkedMatrix
import Algebra.Prelude
import Control.Exception           (evaluate)

main :: IO ()
main = do
  _ <- evaluate $ faugere4Modular optimalStrategy (cyclic (sing :: SNat 4))
  return ()

testCase :: Matrix (Fraction Integer)
testCase = fromLists [[0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,1,0,0]
                    ,[0,0,0,0,0,0,1,1,1,0,0,1,0,0,0,1,0,0,0]
                    ,[0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,0]
                    ,[0,0,0,0,0,1,0,0,0,0,1,-1,0,-1,1,0,-1,0,0]
                    ,[0,0,0,0,1,1,0,1,0,0,1,0,0,0,1,0,0,0,0]
                    ,[1,1,0,1,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0]
                    ,[1,0,1,0,1,0,0,0,0,1,0,1,0,0,0,0,0,0,0]
                    ]

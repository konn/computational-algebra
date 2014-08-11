module Main where
import Algebra.Algorithms.Faugere4
import Algebra.LinkedMatrix
import Algebra.Prelude
import Control.Exception           (evaluate)
import Control.Monad               (void)
import Data.Type.Natural           (sFour)
import Data.Type.Natural           (sFive)

main :: IO ()
main = do
  _ <- evaluate $ faugere4Modular optimalStrategy (cyclic sFive)
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

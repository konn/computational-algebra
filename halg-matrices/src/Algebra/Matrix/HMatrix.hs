{-# OPTIONS_GHC -Wno-orphans -funbox-strict-fields #-}
-- | Provides @'Matrix'@ and @'MMatrix'@ instances for
--  @'LA.Matrix'@ type of @hmatrix@ package.
module Algebra.Matrix.HMatrix (STMatrix) where
import           Algebra.Matrix.Generic
import           Algebra.Matrix.Generic.Mutable (MMatrix (..))
import           Algebra.Prelude.Core
import           Control.Monad                  (forM_)
import           Control.Monad.Primitive
import qualified Data.Vector.Storable           as SV
import qualified Numeric.LinearAlgebra          as LA
import qualified Numeric.LinearAlgebra.Devel    as LA

type instance Mutable LA.Matrix = STMatrix
type instance Row LA.Matrix = LA.Vector
type instance Column LA.Matrix = LA.Vector
type instance Row STMatrix = LA.Vector
type instance Column STMatrix = LA.Vector

-- | Wrapper type for @hmatrix@'s @'LA.STMatrix'@.
data STMatrix s a = STMat { stmRows :: !Int
                          , stmCols :: !Int
                          , unwrapSTM :: LA.STMatrix s a
                          }

instance (Num a, LA.Container LA.Matrix a) => Matrix LA.Matrix a where
  basicRowCount = LA.rows
  basicColumnCount = LA.cols
  unsafeFromRows = LA.fromRows
  unsafeFromColumns = LA.fromColumns
  basicUnsafeIndexM m i j = return $ m `LA.atIndex` (i, j)
  unsafeFreeze = stToPrim . LA.unsafeFreezeMatrix . unwrapSTM
  unsafeThaw m = stToPrim $ STMat (LA.rows m) (LA.cols m) <$> LA.unsafeThawMatrix m
  basicUnsafeGetRowM m i = return $ getRowLA  i m
  basicUnsafeGetColumnM m i = return $ head $ LA.toColumns $ m LA.¿ [i]
  unsafeGenerate w h f =
    LA.fromRows [ SV.generate w $ \j -> f i j
                | i <- [0..h - 1]
                ]

getRowLA :: LA.Element t => Int -> LA.Matrix t -> LA.Vector t
getRowLA i m = head $ LA.toRows $ m LA.? [i]
getColLA :: LA.Element t => Int -> LA.Matrix t -> LA.Vector t
getColLA i m = head $ LA.toColumns $ m LA.¿ [i]

instance (Num a, LA.Container LA.Matrix a) => MMatrix STMatrix a where
  basicUnsafeNew n m = stToPrim $ STMat n m <$> LA.newMatrix 0 n m
  basicInitialise _ = return ()
  basicRowCount = stmRows
  basicColumnCount = stmCols
  unsafeGetRow i m = stToPrim $ getRowLA i <$> LA.unsafeFreezeMatrix (unwrapSTM m)
  unsafeGetColumn i m = stToPrim $ getColLA i <$> LA.unsafeFreezeMatrix (unwrapSTM m)
  unsafeFill n m a = stToPrim $ STMat n m <$> LA.newMatrix a n m
  unsafeFromRow r = stToPrim $ STMat 1 (SV.length r) <$> LA.unsafeThawMatrix (LA.asRow r)
  unsafeFromRows rs = stToPrim $ do
    let m = LA.fromRows rs
    STMat (LA.rows m) (LA.cols m) <$> LA.unsafeThawMatrix m
  unsafeFromColumn c = stToPrim $ STMat (SV.length c) 1 <$> LA.unsafeThawMatrix (LA.asColumn c)
  unsafeFromColumns rs = stToPrim $ do
    let m = LA.fromColumns rs
    STMat (LA.rows m) (LA.cols m) <$> LA.unsafeThawMatrix m
  unsafeCopy (STMat r c m)  (STMat _ _ m') = stToPrim $
    LA.setMatrix m r c =<< LA.unsafeFreezeMatrix m'
  unsafeRead (STMat _ _ m) i j = stToPrim $ LA.readMatrix m i j
  unsafeWrite (STMat _ _ m) i j x = stToPrim $ LA.writeMatrix m i j x
  basicSet (STMat r c m) x = stToPrim $ LA.modifyMatrix m r c $ const x
  basicUnsafeSwapRows (STMat _ _ m) i j = stToPrim $ LA.rowOper (LA.SWAP i j LA.AllCols) m
  unsafeScaleRow (STMat _ _ m) i c = stToPrim $ LA.rowOper (LA.SCAL c (LA.Row i) LA.AllCols) m
  basicUnsafeIMapRowM (STMat _ c m) i f = forM_ [0..c-1] $ \j ->
    stToPrim . LA.writeMatrix m i j =<< f j =<< stToPrim (LA.readMatrix m i j)
  toRows (STMat _ _ m) = stToPrim $ LA.toRows <$> LA.unsafeFreezeMatrix m
  toColumns (STMat _ _ m) = stToPrim $ LA.toColumns <$> LA.unsafeFreezeMatrix m

{-# LANGUAGE PartialTypeSignatures, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans -funbox-strict-fields #-}
-- | Provides @'Matrix'@ and @'MMatrix'@ instances for
--  @'LA.Matrix'@ type of @hmatrix@ package.
module Algebra.Matrix.HMatrix (STMatrix) where
import           Algebra.Matrix.Generic
import           Algebra.Matrix.Generic.Mutable (MMatrix (..))
import           Algebra.Prelude.Core
import           Control.Monad                  (forM_)
import           Control.Monad.Primitive
import qualified Data.Coerce                    as DC
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

instance (Num a, LA.Container LA.Matrix a) => Matrix LA.Matrix (WrapNum a) where
  basicRowCount = LA.rows
  basicColumnCount = LA.cols
  unsafeFromRows rs = DC.coerce $ LA.fromRows (DC.coerce rs :: [LA.Vector a])
  unsafeFromColumns cs = DC.coerce $ LA.fromColumns (DC.coerce cs :: [LA.Vector a])
  basicUnsafeIndexM m i j =
    return $ WrapNum $ (DC.coerce m :: LA.Matrix a) `LA.atIndex` (i, j)
  unsafeFreeze = stToPrim . LA.unsafeFreezeMatrix . unwrapSTM
  unsafeThaw m = stToPrim $ STMat (LA.rows m) (LA.cols m) <$> LA.unsafeThawMatrix m
  basicUnsafeGetRowM m i = return $ DC.coerce $ getRowLA  i (DC.coerce m :: LA.Matrix a)
  basicUnsafeGetColumnM m i =
    return $ DC.coerce $ head $ LA.toColumns (DC.coerce m LA.¿ [i] :: LA.Matrix a)
  unsafeGenerate w h f =
    DC.coerce $
    LA.fromRows [ SV.generate w $ \j -> unwrapNum $ f i j
                | i <- [0..h - 1]
                ]

instance (Integral a, LA.Container LA.Matrix a) => Matrix LA.Matrix (WrapIntegral a) where
  basicRowCount = LA.rows
  basicColumnCount = LA.cols
  unsafeFromRows rs = DC.coerce $ LA.fromRows (DC.coerce rs :: [LA.Vector a])
  unsafeFromColumns cs = DC.coerce $ LA.fromColumns (DC.coerce cs :: [LA.Vector a])
  basicUnsafeIndexM m i j =
    return $ WrapIntegral $ (DC.coerce m :: LA.Matrix a) `LA.atIndex` (i, j)
  unsafeFreeze = stToPrim . LA.unsafeFreezeMatrix . unwrapSTM
  unsafeThaw m = stToPrim $ STMat (LA.rows m) (LA.cols m) <$> LA.unsafeThawMatrix m
  basicUnsafeGetRowM m i = return $ DC.coerce $ getRowLA  i (DC.coerce m :: LA.Matrix a)
  basicUnsafeGetColumnM m i =
    return $ DC.coerce $ head $ LA.toColumns (DC.coerce m LA.¿ [i] :: LA.Matrix a)
  unsafeGenerate w h f =
    DC.coerce $
    LA.fromRows [ SV.generate w $ \j -> unwrapIntegral $ f i j
                | i <- [0..h - 1]
                ]

instance (Fractional a, LA.Container LA.Matrix a) => Matrix LA.Matrix (WrapFractional a) where
  basicRowCount = LA.rows
  basicColumnCount = LA.cols
  unsafeFromRows rs = DC.coerce $ LA.fromRows (DC.coerce rs :: [LA.Vector a])
  unsafeFromColumns cs = DC.coerce $ LA.fromColumns (DC.coerce cs :: [LA.Vector a])
  basicUnsafeIndexM m i j =
    return $ WrapFractional $ (DC.coerce m :: LA.Matrix a) `LA.atIndex` (i, j)
  unsafeFreeze = stToPrim . LA.unsafeFreezeMatrix . unwrapSTM
  unsafeThaw m = stToPrim $ STMat (LA.rows m) (LA.cols m) <$> LA.unsafeThawMatrix m
  basicUnsafeGetRowM m i = return $ DC.coerce $ getRowLA  i (DC.coerce m :: LA.Matrix a)
  basicUnsafeGetColumnM m i =
    return $ DC.coerce $ head $ LA.toColumns (DC.coerce m LA.¿ [i] :: LA.Matrix a)
  unsafeGenerate w h f =
    DC.coerce $
    LA.fromRows [ SV.generate w $ \j -> unwrapFractional $ f i j
                | i <- [0..h - 1]
                ]

getRowLA :: LA.Element t => Int -> LA.Matrix t -> LA.Vector t
getRowLA i m = head $ LA.toRows $ m LA.? [i]
getColLA :: LA.Element t => Int -> LA.Matrix t -> LA.Vector t
getColLA i m = head $ LA.toColumns $ m LA.¿ [i]

unwrapSTMNum :: STMatrix s (WrapNum a) -> LA.STMatrix s a
unwrapSTMNum = DC.coerce . unwrapSTM
{-# INLINE unwrapSTMNum #-}

castSTMatrixNum :: LA.STMatrix s (WrapNum a) -> LA.STMatrix s a
castSTMatrixNum = DC.coerce
{-# INLINE castSTMatrixNum #-}

instance (Num a, LA.Container LA.Matrix a) => MMatrix STMatrix (WrapNum a) where
  basicUnsafeNew n m = stToPrim $ STMat n m <$> LA.newMatrix 0 n m
  basicInitialise _ = return ()
  basicRowCount = stmRows
  basicColumnCount = stmCols
  unsafeGetRow i m =
    stToPrim $ DC.coerce . getRowLA i <$> LA.unsafeFreezeMatrix (unwrapSTMNum m)
  unsafeGetColumn i m = stToPrim $ DC.coerce . getColLA i <$> LA.unsafeFreezeMatrix (unwrapSTMNum m)
  unsafeFill n m a = stToPrim $ STMat n m <$> LA.newMatrix a n m
  unsafeFromRow r = stToPrim $ STMat 1 (SV.length r) <$> LA.unsafeThawMatrix (LA.asRow r)
  unsafeFromRows rs = stToPrim $ do
    let m = LA.fromRows (DC.coerce rs :: [LA.Vector a])
    STMat (LA.rows m) (LA.cols m) . DC.coerce <$> LA.unsafeThawMatrix m
  unsafeFromColumn c = stToPrim $ STMat (SV.length c) 1 <$> LA.unsafeThawMatrix (LA.asColumn c)
  unsafeFromColumns rs = stToPrim $ do
    let m = LA.fromColumns (DC.coerce rs :: [LA.Vector a])
    STMat (LA.rows m) (LA.cols m) . DC.coerce <$> LA.unsafeThawMatrix m
  unsafeCopy (STMat r c m)  (STMat _ _ m') = stToPrim $ do
    m0 <- LA.unsafeFreezeMatrix m'
    LA.setMatrix (DC.coerce m :: LA.STMatrix w a) r c (DC.coerce m0 :: LA.Matrix a)
  unsafeRead (STMat _ _ m) i j = stToPrim $ LA.readMatrix m i j
  unsafeWrite (STMat _ _ m) i j x = stToPrim $ LA.writeMatrix m i j x
  basicSet (STMat r c m) x = stToPrim $ LA.modifyMatrix m r c $ const x
  basicUnsafeSwapRows (STMat _ _ m) i j =
    stToPrim $ LA.rowOper (LA.SWAP i j LA.AllCols) $ castSTMatrixNum m
  unsafeScaleRow (STMat _ _ m) i c =
    stToPrim $ LA.rowOper (LA.SCAL (unwrapNum c) (LA.Row i) LA.AllCols) $ castSTMatrixNum m
  basicUnsafeIMapRowM (STMat _ c m) i f = forM_ [0..c-1] $ \j ->
    stToPrim . LA.writeMatrix m i j =<< f j =<< stToPrim (LA.readMatrix m i j)
  toRows (STMat _ _ m) =
    stToPrim $ DC.coerce . LA.toRows <$> LA.unsafeFreezeMatrix (castSTMatrixNum m)
  toColumns (STMat _ _ m) =
    stToPrim $ DC.coerce . LA.toColumns <$> LA.unsafeFreezeMatrix (castSTMatrixNum m)

unwrapSTMFractional :: STMatrix s (WrapFractional a) -> LA.STMatrix s a
unwrapSTMFractional = DC.coerce . unwrapSTM
{-# INLINE unwrapSTMFractional #-}

castSTMatrixFractional :: LA.STMatrix s (WrapFractional a) -> LA.STMatrix s a
castSTMatrixFractional = DC.coerce
{-# INLINE castSTMatrixFractional #-}

instance (Fractional a, LA.Container LA.Matrix a) => MMatrix STMatrix (WrapFractional a) where
  basicUnsafeNew n m = stToPrim $ STMat n m <$> LA.newMatrix 0 n m
  basicInitialise _ = return ()
  basicRowCount = stmRows
  basicColumnCount = stmCols
  unsafeGetRow i m =
    stToPrim $ DC.coerce . getRowLA i <$> LA.unsafeFreezeMatrix (unwrapSTMFractional m)
  unsafeGetColumn i m = stToPrim $ DC.coerce . getColLA i <$> LA.unsafeFreezeMatrix (unwrapSTMFractional m)
  unsafeFill n m a = stToPrim $ STMat n m <$> LA.newMatrix a n m
  unsafeFromRow r = stToPrim $ STMat 1 (SV.length r) <$> LA.unsafeThawMatrix (LA.asRow r)
  unsafeFromRows rs = stToPrim $ do
    let m = LA.fromRows (DC.coerce rs :: [LA.Vector a])
    STMat (LA.rows m) (LA.cols m) . DC.coerce <$> LA.unsafeThawMatrix m
  unsafeFromColumn c = stToPrim $ STMat (SV.length c) 1 <$> LA.unsafeThawMatrix (LA.asColumn c)
  unsafeFromColumns rs = stToPrim $ do
    let m = LA.fromColumns (DC.coerce rs :: [LA.Vector a])
    STMat (LA.rows m) (LA.cols m) . DC.coerce <$> LA.unsafeThawMatrix m
  unsafeCopy (STMat r c m)  (STMat _ _ m') = stToPrim $ do
    m0 <- LA.unsafeFreezeMatrix m'
    LA.setMatrix (DC.coerce m :: LA.STMatrix w a) r c (DC.coerce m0 :: LA.Matrix a)
  unsafeRead (STMat _ _ m) i j = stToPrim $ LA.readMatrix m i j
  unsafeWrite (STMat _ _ m) i j x = stToPrim $ LA.writeMatrix m i j x
  basicSet (STMat r c m) x = stToPrim $ LA.modifyMatrix m r c $ const x
  basicUnsafeSwapRows (STMat _ _ m) i j =
    stToPrim $ LA.rowOper (LA.SWAP i j LA.AllCols) $ castSTMatrixFractional m
  unsafeScaleRow (STMat _ _ m) i c =
    stToPrim $ LA.rowOper (LA.SCAL (unwrapFractional c) (LA.Row i) LA.AllCols) $ castSTMatrixFractional m
  basicUnsafeIMapRowM (STMat _ c m) i f = forM_ [0..c-1] $ \j ->
    stToPrim . LA.writeMatrix m i j =<< f j =<< stToPrim (LA.readMatrix m i j)
  toRows (STMat _ _ m) =
    stToPrim $ DC.coerce . LA.toRows <$> LA.unsafeFreezeMatrix (castSTMatrixFractional m)
  toColumns (STMat _ _ m) =
    stToPrim $ DC.coerce . LA.toColumns <$> LA.unsafeFreezeMatrix (castSTMatrixFractional m)

unwrapSTMIntegral :: STMatrix s (WrapIntegral a) -> LA.STMatrix s a
unwrapSTMIntegral = DC.coerce . unwrapSTM
{-# INLINE unwrapSTMIntegral #-}

castSTMatrixIntegral :: LA.STMatrix s (WrapIntegral a) -> LA.STMatrix s a
castSTMatrixIntegral = DC.coerce
{-# INLINE castSTMatrixIntegral #-}

instance (Integral a, LA.Container LA.Matrix a) => MMatrix STMatrix (WrapIntegral a) where
  basicUnsafeNew n m = stToPrim $ STMat n m <$> LA.newMatrix 0 n m
  basicInitialise _ = return ()
  basicRowCount = stmRows
  basicColumnCount = stmCols
  unsafeGetRow i m =
    stToPrim $ DC.coerce . getRowLA i <$> LA.unsafeFreezeMatrix (unwrapSTMIntegral m)
  unsafeGetColumn i m = stToPrim $ DC.coerce . getColLA i <$> LA.unsafeFreezeMatrix (unwrapSTMIntegral m)
  unsafeFill n m a = stToPrim $ STMat n m <$> LA.newMatrix a n m
  unsafeFromRow r = stToPrim $ STMat 1 (SV.length r) <$> LA.unsafeThawMatrix (LA.asRow r)
  unsafeFromRows rs = stToPrim $ do
    let m = LA.fromRows (DC.coerce rs :: [LA.Vector a])
    STMat (LA.rows m) (LA.cols m) . DC.coerce <$> LA.unsafeThawMatrix m
  unsafeFromColumn c = stToPrim $ STMat (SV.length c) 1 <$> LA.unsafeThawMatrix (LA.asColumn c)
  unsafeFromColumns rs = stToPrim $ do
    let m = LA.fromColumns (DC.coerce rs :: [LA.Vector a])
    STMat (LA.rows m) (LA.cols m) . DC.coerce <$> LA.unsafeThawMatrix m
  unsafeCopy (STMat r c m)  (STMat _ _ m') = stToPrim $ do
    m0 <- LA.unsafeFreezeMatrix m'
    LA.setMatrix (DC.coerce m :: LA.STMatrix w a) r c (DC.coerce m0 :: LA.Matrix a)
  unsafeRead (STMat _ _ m) i j = stToPrim $ LA.readMatrix m i j
  unsafeWrite (STMat _ _ m) i j x = stToPrim $ LA.writeMatrix m i j x
  basicSet (STMat r c m) x = stToPrim $ LA.modifyMatrix m r c $ const x
  basicUnsafeSwapRows (STMat _ _ m) i j =
    stToPrim $ LA.rowOper (LA.SWAP i j LA.AllCols) $ castSTMatrixIntegral m
  unsafeScaleRow (STMat _ _ m) i c =
    stToPrim $ LA.rowOper (LA.SCAL (unwrapIntegral c) (LA.Row i) LA.AllCols) $ castSTMatrixIntegral m
  basicUnsafeIMapRowM (STMat _ c m) i f = forM_ [0..c-1] $ \j ->
    stToPrim . LA.writeMatrix m i j =<< f j =<< stToPrim (LA.readMatrix m i j)
  toRows (STMat _ _ m) =
    stToPrim $ DC.coerce . LA.toRows <$> LA.unsafeFreezeMatrix (castSTMatrixIntegral m)
  toColumns (STMat _ _ m) =
    stToPrim $ DC.coerce . LA.toColumns <$> LA.unsafeFreezeMatrix (castSTMatrixIntegral m)

instance {-# OVERLAPPING #-} (LA.Container LA.Matrix a, Show a) => Show (LA.Matrix (WrapNum a)) where
  showsPrec d = showsPrec d . (DC.coerce :: LA.Matrix (WrapNum a) -> LA.Matrix a)

instance {-# OVERLAPPING #-} (LA.Container LA.Matrix a, Show a) => Show (LA.Matrix (WrapIntegral a)) where
  showsPrec d = showsPrec d . (DC.coerce :: LA.Matrix (WrapIntegral a) -> LA.Matrix a)

instance {-# OVERLAPPING #-} (LA.Container LA.Matrix a, Show a) => Show (LA.Matrix (WrapFractional a)) where
  showsPrec d = showsPrec d . (DC.coerce :: LA.Matrix (WrapFractional a) -> LA.Matrix a)

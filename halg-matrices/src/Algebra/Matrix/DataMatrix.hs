{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans -funbox-strict-fields #-}
-- | Provides @'Matrix'@ and @'MMatrix'@ instances for
--   @'DM.Matrix'@ type of @matrix@ package.
--
-- | __N.B.__ This module provides @0@-origin interface for @'DM.Matrix'@,
--            contrary to the @matrix@ package provides @1@-origin.
module Algebra.Matrix.DataMatrix (DMatrix) where
import           Algebra.Matrix.Generic
import           Algebra.Prelude.Core
import qualified Data.Coerce            as DC
import qualified Data.Matrix            as DM
import qualified Data.Vector            as V

type WIMatrix = WrapImmutable DM.Matrix
type DMatrix = DM.Matrix

type instance Mutable DM.Matrix = WIMatrix
type instance Row DM.Matrix = V.Vector
type instance Column DM.Matrix = V.Vector

instance (UnitNormalForm a, Ring a) => Matrix DM.Matrix a where
  basicRowCount = DM.nrows
  basicColumnCount = DM.ncols
  basicUnsafeIndexM m i j = return $ DM.unsafeGet (i+1) (j+1) m
  basicUnsafeGetRowM m i = return $ DM.getRow (i + 1) m
  basicUnsafeGetColumnM m i = return $ DM.getCol (i + 1) m
  unsafeGenerate w h f = DM.matrix w h $ \(i, j) -> f (i-1) (j-1)
  unsafeWrite mat i j x = DM.unsafeSet x (i+1, j+1) mat
  unsafeFromRows = foldr1 (DM.<->) . map DM.rowVector
  unsafeFromColumns = foldr1 (DM.<|>) . map DM.colVector

  toRows m = map (`DM.getRow` m) [1..DM.nrows m]
  toColumns m = map (`DM.getCol` m) [1..DM.ncols m]

  swapRows m i j = DM.switchRows (i+1) (j+1) m
  scaleRow m i c = DC.coerce $ DM.scaleRow (WrapAlgebra c) (i+1) (DC.coerce m :: DM.Matrix (WrapAlgebra a))
  unsafeIMapRow m i f = DM.mapRow (\k -> f (k - 1)) (i+1) m
  combineRows i c j = DC.coerce $ DM.combineRows (i+1) (WrapAlgebra c) (j+1)

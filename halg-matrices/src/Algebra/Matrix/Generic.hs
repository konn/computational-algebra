{-# LANGUAGE NoMonomorphismRestriction, RankNTypes, ScopedTypeVariables #-}
module Algebra.Matrix.Generic
  ( Matrix(..), Column, Row, Size, Index
  , rowCount, columnCount, generate, freeze, thaw
  , fromRows, fromColumns, gaussReduction, create
  ) where
import           Algebra.Matrix.Generic.Mutable (Index, MMatrix, Size)
import qualified Algebra.Matrix.Generic.Mutable as GM
import           Algebra.Prelude.Core           hiding (Vector, generate)
import           Control.Monad.Primitive        (PrimMonad, PrimState)
import           Control.Monad.ST
import           Data.Kind
import           Data.Vector.Generic            (Mutable, Vector)
import qualified Data.Vector.Generic            as GV

type family Column (mat :: Type -> Type) :: Type -> Type
type family Row    (mat :: Type -> Type) :: Type -> Type

-- | General Matrix type, with associated mutable matrix.
class ( Vector (Column mat) a, Vector (Row mat) a
      , MMatrix (Mutable mat) a
      , Mutable (Row mat)    ~ GM.MRow (Mutable mat)
      , Mutable (Column mat) ~ GM.MColumn (Mutable mat)
      )
   => Matrix mat a where
  basicRowCount         :: mat a -> Size
  basicColumnCount      :: mat a -> Size
  unsafeFreeze          :: PrimMonad m => Mutable mat (PrimState m) a -> m (mat a)
  unsafeThaw            :: PrimMonad m => mat a -> m (Mutable mat (PrimState m) a)
  basicUnsafeIndexM     :: Monad m => mat a -> Index -> Index -> m a
  basicUnsafeGetRowM    :: Monad m => mat a -> Index -> m (Row mat a)
  basicUnsafeGetColumnM :: Monad m => mat a -> Index -> m (Row mat a)

  basicUnsafeCopy      :: PrimMonad m => Mutable mat (PrimState m) a -> mat a -> m ()
  basicUnsafeCopy mmat = GM.unsafeCopy mmat <=< unsafeThaw

  unsafeGenerate :: Size -> Size -> (Index -> Index -> a) -> mat a
  unsafeGenerate w h f = runST $ unsafeFreeze =<< GM.unsafeGenerate w h f

  unsafeFromRows :: [Row mat a] -> mat a
  unsafeFromRows rs = runST $ unsafeFreeze =<< GM.unsafeFromRows =<< mapM GV.unsafeThaw rs

  unsafeFromColumns :: [Column mat a] -> mat a
  unsafeFromColumns rs = runST $ unsafeFreeze =<< GM.unsafeFromColumns =<< mapM GV.unsafeThaw rs

  toRows :: Matrix mat a => mat a -> [Row mat a]
  toRows mat = runST $ mapM GV.unsafeFreeze =<< GM.toRows =<< unsafeThaw mat

  toColumns :: Matrix mat a => mat a -> [Column mat a]
  toColumns mat = runST $ mapM GV.unsafeFreeze =<< GM.toColumns =<< unsafeThaw mat

rowCount :: Matrix mat a => mat a -> Size
rowCount = basicRowCount

columnCount :: Matrix mat a => mat a -> Size
columnCount = basicColumnCount

generate :: Matrix mat a => Size -> Size -> (Index -> Index -> a) -> mat a
generate w h f = runST $ unsafeFreeze =<< GM.generate w h f

freeze :: (Matrix mat a, PrimMonad m) => Mutable mat (PrimState m) a -> m (mat a)
freeze = unsafeFreeze <=< GM.clone

thaw :: (Matrix mat a, PrimMonad m) => mat a -> m (Mutable mat (PrimState m) a)
thaw   = GM.clone <=< unsafeThaw

fromRows :: Matrix mat a => [Row mat a] -> mat a
fromRows rs
  | let lens = map GV.length rs
  , and $ zipWith (==) lens (tail lens) = unsafeFromRows rs
  | otherwise = error "fromRows: rows should be of the same length"

fromColumns :: Matrix mat a => [Column mat a] -> mat a
fromColumns cs
  | let lens = map GV.length cs
  , and $ zipWith (==) lens (tail lens) = unsafeFromColumns cs
  | otherwise = error "fromColumns: columns should be of the same length"

gaussReduction :: (Eq a, Matrix mat a, Normed a, Field a) => mat a -> (mat a, mat a, a)
gaussReduction mat = runST $ do
  (m', p, d) <- GM.gaussReduction =<< unsafeThaw mat
  tmat <- unsafeFreeze m'
  piv <- unsafeFreeze p
  return (tmat, piv, d)

create :: Matrix mat a => (forall s. ST s (Mutable mat s a)) -> mat a
create act = runST $ unsafeFreeze =<< act

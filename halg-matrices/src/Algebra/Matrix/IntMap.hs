module Algebra.Matrix.IntMap (IMMatrix, MIMMatrix) where
import           Algebra.Matrix.Generic
import           Algebra.Matrix.Generic.Mutable (MMatrix)
import qualified Algebra.Matrix.Generic.Mutable as GM
import           Algebra.Prelude.Core
import           Control.DeepSeq
import           Data.IntMap                    (IntMap)
import qualified Data.IntMap                    as IM
import           Data.Vector                    (MVector, Vector)
import qualified Data.Vector                    as V
import           Data.Vector.Generic            (Mutable)
import qualified Data.Vector.Generic.Mutable    as MV (basicInitialize,
                                                       basicLength)
import qualified Data.Vector.Mutable            as MV

-- | Sparse matrix represented by a finite map from index to an element.
data IMMatrix a = IMM { imRows :: Vector (IntMap a)
                      , imColCount :: Int
                      }
                  deriving (Eq, Ord)

instance NFData a => NFData (IMMatrix a) where
  rnf (IMM vs i) = rnf vs `seq` rnf i `seq` ()

instance (DecidableZero a, Show a) => Show (IMMatrix a) where
  showsPrec d = showsPrec d . toRows

lookCoe :: Monoidal c => IM.Key -> IntMap c -> c
lookCoe a = fromMaybe zero . IM.lookup a

-- | Mutable version of @'IMMatrix'@, but the same.
data MIMMatrix s a = MIM { _mimRows :: MVector s (IntMap a)
                         , _mimColCount :: Int
                         }

guardZero :: DecidableZero a => a -> Maybe a
guardZero a | isZero a = Nothing
            | otherwise = Just a
{-# INLINE guardZero #-}

cmpMatrixSizeMsg :: IMMatrix a1 -> IMMatrix a2 -> String
cmpMatrixSizeMsg m m'
  = unwords [ show (V.length $ imRows m) ++ "x" ++ show (imColCount m)
            , "matrix with"
            , show (V.length $ imRows m') ++ "x" ++ show (imColCount m')
            ]

instance DecidableZero a => Additive (IMMatrix a) where
  m@(IMM rs cs) + m'@(IMM rs' cs')
    | cs == cs' && V.length rs == V.length rs'
    = IMM (V.zipWith (IM.unionWith (+)) rs rs') cs
    | otherwise =
      error $
      unwords ["(Additive.+):"
              , "adding"
              , cmpMatrixSizeMsg m m'
              ]

dot :: (DecidableZero a, Ring a) => IntMap a -> Vector a -> a
dot row col = sum $ IM.mapMaybeWithKey (\k a -> guardZero $ a * (col V.! k)) row

instance (Ring a, DecidableZero a) => Multiplicative (IMMatrix a) where
  m * m'
    | columnCount m /= rowCount m' =
      error $ unwords [ "(Multiplicative.*)", "multipling", cmpMatrixSizeMsg m m']
    | otherwise =
      let loop row =
            IM.fromList [ (j, dot row $ V.map (lookCoe j) $ imRows m')
                        | j <- [0.. imColCount m' - 1]
                        ]
          rs = V.map loop (imRows m)
      in IMM rs (imColCount m')

type instance Mutable IMMatrix = MIMMatrix
type instance Row IMMatrix = Vector
type instance Column IMMatrix = Vector

instance DecidableZero a => Matrix IMMatrix a where
  basicRowCount (IMM v _) = V.length v
  basicColumnCount (IMM _ c) = c
  unsafeFreeze (MIM v c) = flip IMM c <$> V.unsafeFreeze v
  unsafeThaw   (IMM v c) = flip MIM c <$> V.unsafeThaw v
  basicUnsafeIndexM (IMM v _) i j = return $ fromMaybe zero $ IM.lookup j $ V.unsafeIndex v i
  basicUnsafeGetRowM (IMM v c) i = return $ V.generate c $ \j ->
    fromMaybe zero $ IM.lookup j $ v V.! i
  basicUnsafeGetColumnM (IMM v _) j = return $ V.map (fromMaybe zero . IM.lookup j) v

mfromIM :: Monoidal a => Size -> IntMap a -> Vector a
mfromIM n dic = V.generate n $ \k -> fromMaybe zero $ IM.lookup k dic

mrowToIM :: (DecidableZero a) => Vector a -> IntMap a
mrowToIM mv =
  IM.fromList $ V.toList $
  V.imapMaybe (\i k -> if isZero k then Nothing else Just (i, k)) mv

type instance Row    MIMMatrix = Vector
type instance Column MIMMatrix = Vector
instance DecidableZero a => MMatrix MIMMatrix a where
  basicUnsafeNew n m = flip MIM m <$> MV.unsafeNew n
  basicInitialise (MIM v _) = MV.basicInitialize v >> MV.set v IM.empty
  basicRowCount (MIM v _) = MV.basicLength v
  basicColumnCount (MIM _ w) = w
  unsafeGetRow i (MIM v c) = mfromIM c <$> MV.read v i
  unsafeGetColumn i (MIM v _) =
    V.map (fromMaybe zero . IM.lookup i) <$> V.unsafeFreeze v
  unsafeFromRows rs =
    flip MIM (V.length $ head rs) <$> V.unsafeThaw (V.fromList $ map mrowToIM rs)
  unsafeCopy (MIM v _) (MIM u _) = MV.unsafeCopy v u
  unsafeRead (MIM v _) r c =
    fromMaybe zero . IM.lookup c <$> MV.unsafeRead v r
  unsafeWrite (MIM v _) r c x
    | isZero x  = return ()
    | otherwise = MV.write v r . IM.insert c x =<< MV.read v r
  basicUnsafeSwapRows (MIM v _) = MV.swap v
  basicSet (MIM v c) a = MV.set v $ IM.fromList [(i, a) | i <- [0.. c - 1]]
  unsafeScaleRow (MIM v _) i c =
    MV.write v i . IM.mapMaybe (guardZero . (c *))
    =<< MV.read v i
  basicUnsafeIMapRowM (MIM v c) i f =
    forM_ [0..c - 1] $ \j -> do
    dic <- MV.read v i
    a <- f j $ fromMaybe zero $ IM.lookup j dic
    if isZero a
      then MV.write v i $ IM.delete j dic
      else MV.write v i $ IM.insert j a dic

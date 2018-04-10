module Control.Monad.ST.Combinators
       ( newArray
       , (.=), (.%=), (%!), arrayToList
       , module Control.Monad.ST.Strict
       , module Data.STRef.Strict
       ) where
import           Control.Monad           ((<=<))
import           Control.Monad.ST.Strict
import           Data.STRef.Strict
import qualified Data.Vector             as V
import qualified Data.Vector.Mutable     as MV
import           Prelude

type ArrayRef s a = STRef s (V.MVector s a)

newArray :: [a] -> ST s (ArrayRef s a)
newArray = newSTRef <=< V.unsafeThaw . V.fromList

arrayToList :: ArrayRef s a -> ST s [a]
arrayToList = fmap V.toList . V.unsafeFreeze <=< readSTRef

(.=) :: STRef s a -> a -> ST s ()
(.=) = writeSTRef

(.%=) :: STRef s a -> (a -> a) -> ST s ()
(.%=) = modifySTRef'

(%!) :: ArrayRef s a -> Int -> ST s a
v %! i = flip MV.read i =<< readSTRef v

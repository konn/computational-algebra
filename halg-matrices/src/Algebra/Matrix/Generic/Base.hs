module Algebra.Matrix.Generic.Base (Column, Row, Index, Size) where
import Data.Int  (Int)
import Data.Kind (Type)

type family Column (mat :: k) :: Type -> Type
type family Row    (mat :: k) :: Type -> Type

type Index = Int
type Size = Int

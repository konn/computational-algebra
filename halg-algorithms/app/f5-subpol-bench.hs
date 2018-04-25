{-# LANGUAGE LambdaCase, NoImplicitPrelude, ViewPatterns #-}
module Main where
import Algebra.Algorithms.Groebner.Signature
import Algebra.Prelude.Core
import Cases
import System.Environment

main :: IO ()
main = getArgs >>= \case
  (c:(readIntM -> Just n)) : _
    | c `elem` "cC" ->
      case toSing (fromIntegral n) of
        SomeSing sn -> withKnownNat sn $
          let (_, hist) = f5WithHistory (cyclic sn)
          in print hist
  "katsura8" : _ -> print $ snd $ f5WithHistory katsura8
  "katsura9" : _ -> print $ snd $ f5WithHistory katsura9
  "i3" : _ -> print $ snd $ f5WithHistory i3
  _ -> print $ snd $ f5WithHistory $ cyclic (sing :: Sing 5)

readIntM :: String -> Maybe Natural
readIntM str =
  case reads str of
    [(n, "")] -> Just n
    _ -> Nothing

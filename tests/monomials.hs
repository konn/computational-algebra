{-# LANGUAGE RankNTypes #-}
module Main where
import qualified Algebra.Ring.Polynomial as P
import qualified Data.Sequence           as S
import           Data.Type.Monomorphic
import qualified SequenceMonomial        as S
import           Test.Hspec
import qualified Test.Hspec.QuickCheck   as QC
import qualified Test.Hspec.SmallCheck   as SC
import qualified Test.QuickCheck         as QC
import qualified Test.SmallCheck         as SC
import qualified Test.SmallCheck.Series  as SC

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Monomial orderings" $ do
    QC.prop "coincides on lex (random)" $ compQC P.lex S.lex
    QC.prop "coincides on revlex (random)" $ compQC P.revlex S.revlex
    QC.prop "coincides on grlex (random)" $ compQC P.grlex S.grlex
    QC.prop "coincides on grevlex (random)" $ compQC P.grevlex S.grevlex
    it "coincides on lex (exhaustive)" $ SC.property $ compSC P.lex S.lex
    it "coincides on revlex (exhaustive)" $ SC.property $ compSC P.revlex S.revlex
    it "coincides on grlex (exhaustive)" $ SC.property $ compSC P.grlex S.grlex
    it "coincides on grevlex (exhaustive)" $ SC.property $ compSC P.grevlex S.grevlex

compQC :: P.MonomialOrder -> S.MonomialOrder -> QC.Property
compQC pol sq =
    QC.forAll (QC.listOf $ QC.resize 100 QC.arbitrarySizedBoundedIntegral) $ \m1 ->
           QC.forAll (QC.listOf $ QC.resize 100 QC.arbitrarySizedBoundedIntegral) $ \m2 ->
             let len = max (length m1) (length m2)
                 n1  = m1 ++ replicate (len - length m1) 0
                 n2  = m2 ++ replicate (len - length m2) 0
             in withPolymorhic len $ \sn ->
                 pol (P.fromList sn n1) (P.fromList sn n2) == sq (S.fromList n1) (S.fromList n2)

compSC :: Monad m => P.MonomialOrder -> S.MonomialOrder -> SC.Property m
compSC pol sq =
    SC.forAll $ \m1 m2 ->
        let len = max (length m1) (length m2)
            n1  = map SC.getNonNegative $ m1 ++ replicate (len - length m1) 0
            n2  = map SC.getNonNegative $ m2 ++ replicate (len - length m2) 0
        in withPolymorhic len $ \sn ->
            pol (P.fromList sn n1) (P.fromList sn n2) == sq (S.fromList n1) (S.fromList n2)


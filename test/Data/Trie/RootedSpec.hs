module Data.Trie.RootedSpec (main, spec) where

import Data.Trie.Rooted
import qualified Data.Trie.Rooted as R

import Prelude hiding (lookup)
import Data.List.NonEmpty
import qualified Data.List.NonEmpty as NE
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Instances

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "insertion" $ do
    prop "should exist after `Just` assignment" lookupJust

lookupJust :: [String] -> Int -> Rooted String Int -> Property
lookupJust ts x trie =
    (R.lookup ts $ R.assign ts (Just x) trie) === Just x

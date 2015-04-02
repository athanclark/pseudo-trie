module Data.Trie.PseudoSpec (main, spec) where

import Data.Trie.Pseudo
import qualified Data.Trie.Pseudo as P
import Data.Trie.Rooted
import qualified Data.Trie.Rooted as R

import Prelude hiding (lookup)
import Data.List.NonEmpty
import qualified Data.List.NonEmpty as NE
import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.Instances

main :: IO ()
main = hspec spec

-- TODO:
--   - Overwriting
--   - Forking two Rests at their divergent point
--   - fromAssocs . toAssocs == normalize
--   - making a new root node...?
--      - implicit optional root node :\ bad idea

spec :: Spec
spec = do
  describe "insertion" $ do
    it "should exist after `Just` assignment" $ do
      property lookupJust
  describe "reconstruction" $ do
    it "`fromAssocs . toAssocs` should ~ `prune`" $ do
      property fromToPrune

lookupJust :: [String] -> Int -> Rooted String Int -> Property
lookupJust ts x trie =
    (R.lookup ts $ set ts x trie) === Just x

fromToPrune :: PseudoTrie String Int -> Property
fromToPrune trie = (fromAssocs $ toAssocs trie) === prune trie

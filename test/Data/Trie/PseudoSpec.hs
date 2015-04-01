module Data.Trie.PseudoSpec (main, spec) where

import Data.Trie.Pseudo

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
  describe "reconstruction" $ do
    it "`fromAssocs . toAssocs` should ~ `prune`" $ do
      property fromToPrune

fromToPrune :: PseudoTrie String Int -> Property
fromToPrune x = (fromAssocs $ toAssocs x) === prune x

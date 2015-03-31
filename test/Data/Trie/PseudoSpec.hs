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
  describe "someFunction" $ do
    it "should work fine" $ do
      property someFunction

someFunction :: Bool -> Bool -> Property
someFunction x y = x === y

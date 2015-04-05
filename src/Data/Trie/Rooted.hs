{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Trie.Rooted where

import           Control.Applicative
import           Data.List.NonEmpty        hiding (head, tail)
import qualified Data.List.NonEmpty        as NE
import           Data.Monoid
import           Data.Trie.Pseudo          as P
import           Test.QuickCheck
import           Test.QuickCheck.Instances


data Rooted t a = Rooted { root :: (Maybe a)
                         , children :: [PseudoTrie t a] }
  deriving (Show, Eq, Functor)

instance (Arbitrary a) => Arbitrary (Rooted String a) where
  arbitrary = do
    (mx :: Maybe a) <- arbitrary
    (xs :: [PseudoTrie String a]) <- arbitrary
    return $ Rooted mx xs

-- | Intersection instance
instance (Eq t) => Applicative (Rooted t) where
  pure x = Rooted (Just x) []
  (<*>) (Rooted mf fs) (Rooted mx xs) =
    Rooted (mf <*> mx)
      [intersectionWith ($) f x | f <- fs, x <- xs]

-- | Union instance
instance (Eq t, Monoid a) => Monoid (Rooted t a) where
  mempty = Rooted Nothing []
  mappend = unionWith mappend

newtype MergeRooted t a = MergeRooted
  { unMergeRooted :: Rooted t a }
  deriving (Functor)

instance (Eq t) => Monoid (MergeRooted t a) where
  mempty = MergeRooted $ Rooted Nothing []
  (MergeRooted x) `mappend` (MergeRooted y) =
    MergeRooted $ x `Data.Trie.Rooted.merge` y

-- | Strictly constructive form of @Data.Trie.Pseudo.assign@
assign :: (Eq t) => [t] -> Maybe a -> Rooted t a -> Rooted t a
assign [] mx (Rooted _ ys) = Rooted mx ys
assign tss@(t:ts) mx (Rooted my ys)
  | any (`beginsWith` t) ys =
      Rooted my $ fmap (P.assign (NE.fromList tss) mx) ys
  | otherwise = case mx of
                  Nothing -> Rooted my ys -- nowhere to remove
                  Just x  -> Rooted my $ Rest (NE.fromList tss) x : ys
-- assign ts x = flip Data.Trie.Rooted.merge $
--                 Rooted Nothing [Rest (NE.fromList ts) x]

lookup :: (Eq t) => [t] -> Rooted t a -> Maybe a
lookup [] (Rooted mx _) = mx
lookup ts (Rooted _ xs) = foldr (go ts) Nothing xs
  where
    go ts x Nothing     = P.lookup (NE.fromList ts) x
    go ts x ma@(Just a) = ma

merge :: (Eq t) =>
         Rooted t a
      -> Rooted t a
      -> Rooted t a
merge (Rooted mx xs) (Rooted my ys) =
  Rooted (getLast $ Last mx <> Last my) $
    foldr go [] $ xs ++ ys
  where
    go q [] = [q]
    go q (z:zs) | areDisjoint q z = q : z : zs
                | otherwise = P.merge q z : zs

-- | Disjoint cases just pull children to common root
unionWith :: (Eq t) =>
             (a -> a -> a)
          -> Rooted t a
          -> Rooted t a
          -> Rooted t a
unionWith f (Rooted mx xs) (Rooted my ys) =
  Rooted (f <$> mx <*> my) $
    Prelude.concat [process f x y | x <- xs, y <- ys]
  where
    process f x y | areDisjoint x y = [unionWith' f x y]
                  | otherwise       = x : [y]
    -- partial function, neglecting disjoint cases
    unionWith' _ Nil Nil = Nil
    unionWith' _ Nil y = y
    unionWith' _ x Nil = x
    unionWith' f (Rest tss@(t:|ts) x) (Rest pss@(p:|ps) y)
      | tss == pss = Rest pss $ f x y
      | t == p = case (ts,ps) of
                   ([], p':ps') -> More (t, Just x) $ Rest (fromList ps) y :| []
                   (t':ts', []) -> More (p, Just y) $ Rest (fromList ts) x :| []
                   (_,_) -> More (t,Nothing) $ fromList
                              [unionWith' f (Rest (NE.fromList ts) x)
                                            (Rest (NE.fromList ps) y)]
    unionWith' f (More (t,mx) xs) (More (p,my) ys)
      | t == p = let zs = NE.toList xs ++ NE.toList ys in
                 More (p,f <$> mx <*> my) $ NE.fromList $
                   foldr (\q (z':zs') -> unionWith' f z' q : zs') [head zs] (tail zs)
    unionWith' f (More (t,mx) xs) (Rest pss@(p:|ps) y)
      | t == p = case ps of
                   [] -> More (p,f <$> mx <*> Just y) xs
                   _  -> More (t,mx) $ fmap (flip (unionWith' f) $ Rest (fromList ps) y) xs
    unionWith' f (Rest tss@(t:|ts) x) (More (p,my) ys)
      | t == p = case ts of
                   [] -> More (t,f <$> Just x <*> my) ys
                   _  -> More (p,my) $ fmap (unionWith' f $ Rest (fromList ts) x) ys

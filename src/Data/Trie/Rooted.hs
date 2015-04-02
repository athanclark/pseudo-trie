{-# LANGUAGE DeriveFunctor #-}

module Data.Trie.Rooted where

import Prelude
import Data.Trie.Pseudo
import Data.Monoid
import Control.Applicative
import Data.List.NonEmpty hiding (head, tail)
import qualified Data.List.NonEmpty as NE

data Rooted t a = Rooted (Maybe a) [PseudoTrie t a]
  deriving (Show, Eq, Functor)

instance (Eq t) => Applicative (Rooted t) where
  pure x = Rooted (Just x) []
  (<*>) (Rooted mf fs) (Rooted mx xs) =
    Rooted (mf <*> mx) $
      [intersectionWith ($) f x | f <- fs, x <- xs]

instance (Eq t, Monoid a) => Monoid (Rooted t a) where
  mempty = Rooted Nothing []
  mappend = unionWith mappend

set :: (Eq t) => [t] -> a -> Rooted t a -> Rooted t a
set [] x = unionWith const $ Rooted (Just x) []
set ts x = unionWith const $ Rooted Nothing [Rest (NE.fromList ts) x]

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
                   _  -> More (t,mx) $ fmap ((flip $ unionWith' f) $ Rest (fromList ps) y) xs
    unionWith' f (Rest tss@(t:|ts) x) (More (p,my) ys)
      | t == p = case ts of
                   [] -> More (t,f <$> Just x <*> my) ys
                   _  -> More (p,my) $ fmap (unionWith' f $ Rest (fromList ts) x) ys

{-# LANGUAGE DeriveFunctor #-}

module Data.Trie.Pseudo where

import Data.Trie.Pseudo.Internal

import Prelude hiding (lookup)
import Data.List.NonEmpty
import Data.Default
import Data.Monoid
import Data.Foldable (find)
import Data.Maybe (fromMaybe)

-- | Non-Empty Rose Tree with explicit emptyness
data PseudoTrie t a = More (t, Maybe a) (NonEmpty (PseudoTrie t a))
                    | Rest (NonEmpty t) a
                    | Nil
  deriving (Show, Eq, Functor)

lookup :: (Eq t, Monoid t) => NonEmpty t -> PseudoTrie t a -> Maybe a
lookup _ Nil = Nothing
lookup tss (Rest pss a) | tss == pss = Just a
                        | otherwise = Nothing
lookup tss@(t:|ts) (More (p,mx) xs) | t == p =
  case ts of
    [] -> mx
    (t':ts') -> find (hasNextTag t') xs >>= lookup (fromList ts)

  where
    hasNextTag :: Eq t => t -> PseudoTrie t a -> Bool
    hasNextTag t Nil = False
    hasNextTag t (More (p,_) _) = t == p
    hasNextTag t (Rest (p:|_) _) = t == p

-- instance (Eq t) => Applicative (PseudoTrie t) where
--   -- noop
--   Nil <*> xss@(More (p, mx) xs) = xss
--   Nil <*> xss@(Rest ps a) = xss
--   -- info loss
--   (More (t,mf) fs) <*> Nil = Nil
--   (Rest ts f) <*> Nil = Nil
--   -- computation
--   (More (t,mf) fs) <*> (More (p,mx) xs)
--     | t == p = More (p, mf <*> mx) $ fs <*> xs
--     | otherwise = More (p,mx) xs -- derailed
--   (Rest ts f) <*> (Rest ps x)
--     | ts == ps = Rest ps $ f x
--     | otherwise = Rest ps x
--   (More (t,mf) fs) <*> (Rest pss@(p:|ps) x)
--     | t == p = Rest pss $
--   (Rest ts f) <*> (More (p,mx) xs) =


-- instance Default t =>

{-# LANGUAGE DeriveFunctor #-}

module Data.Trie.Pseudo where

import Data.Trie.Pseudo.Internal

import Prelude hiding (lookup, map)
import Control.Applicative
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

-- instance Default t =>

{-# LANGUAGE DeriveFunctor #-}

module Data.Trie.Pseudo where

import Data.Trie.Pseudo.Internal

import Data.List.NonEmpty
import Data.Default

-- | Non-Empty Rose Tree with explicit emptyness
data PseudoTrie t a = More (t, Maybe a) (NonEmpty (PseudoTrie t a))
                    | Rest (NonEmpty t) a
                    | Nil
  deriving (Show, Eq, Functor)

instance Applicative (PseudoTrie t) where
  -- noop
  Nil <*> xss@(More (t, mx) xs) = xss
  Nil <*> xss@(Rest ts a) = xss
  -- info loss
  (More (t,mf) fs) <*> Nil = Nil
  (Rest ts f) <*> Nil = Nil
  -- computation
  (More (t,mf) fs) <*> (More (t,mx) xs) =
  (Rest ts f) <*> (Rest ps x) =
  (More (t,mf) fs) <*> (Rest ps x) =
  (Rest ts f) <*> (More (t,mx) xs) =


instance Default t =>

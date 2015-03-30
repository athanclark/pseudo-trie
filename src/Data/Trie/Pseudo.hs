{-# LANGUAGE DeriveFunctor #-}

module Data.Trie.Pseudo where

import Data.Trie.Pseudo.Internal

import Prelude hiding (lookup, map)
import Control.Applicative
import Data.List.NonEmpty hiding (head, tail)
import Data.Default
import Data.Monoid
import Data.Foldable (find)
import Data.Maybe (fromMaybe)

-- | Non-Empty Rose Tree with explicit emptyness
data PseudoTrie t a = More (t, Maybe a) (NonEmpty (PseudoTrie t a))
                    | Rest (NonEmpty t) a
                    | Nil
  deriving (Show, Eq, Functor)

lookup :: (Eq t) => NonEmpty t -> PseudoTrie t a -> Maybe a
lookup _ Nil = Nothing
lookup tss (Rest pss a) | tss == pss = Just a
                        | otherwise = Nothing
lookup tss@(t:|ts) (More (p,mx) xs) | t == p =
  case ts of
    [] -> mx
    (t':ts') -> find (hasNextTag t') xs >>= lookup (fromList ts)

  where
    hasNextTag :: (Eq t) => t -> PseudoTrie t a -> Bool
    hasNextTag t Nil = False
    hasNextTag t (More (p,_) _) = t == p
    hasNextTag t (Rest (p:|_) _) = t == p

-- | Rightward bias
union :: (Eq t, Default t) => PseudoTrie t a -> PseudoTrie t a -> PseudoTrie t a
union Nil Nil = Nil
union x Nil = x
union Nil y = y
union (Rest tss@(t:|ts) x) (Rest pss@(p:|ps) y)
  | tss == pss = Rest pss y
  | t == p = case (ts,ps) of
               ([],(p':ps')) -> More (t,Just x) $ Rest (fromList ps) y :| []
               ((t':ts'),[]) -> More (p,Just y) $ Rest (fromList ts) x :| []
               (_,_) -> More (t,Nothing) $
                          (Rest (fromList ts) x) `union` (Rest (fromList ps) y) :| []
  -- root normalization
  | t == def = case ts of
                [] -> More (def,Just x) $ Rest
                        (if p == def then (fromList ps) else pss)
                        y :| []
                _  -> (Rest (fromList ts) x) `union` (Rest pss y)
  | p == def = case ps of
                [] -> More (def,Just y) $ Rest
                        (if t == def then (fromList ts) else tss)
                        y :| []
                _  -> (Rest tss x) `union` (Rest (fromList ps) y)
  | otherwise = Rest pss y
union (More (t,mx) xs) (More (p,my) ys)
  | t == p = let zs = (toList xs) ++ (toList ys) in
             More (p,my) $ fromList $
              foldl (\(z':zs') q -> z' `union` q : zs') [head zs] (tail zs)
  | t == def = More (def,mx) $
                 fmap (`union` (More (p,my) ys)) xs
  | p == def = More (def,my) $
                 fmap (`union` (More (t,mx) xs)) ys
  -- disjoint
  | otherwise = More (def,Nothing) $
                  (More (t,mx) xs) :| (More (p,my) ys) : []
union (More (t,mx) xs) (Rest pss@(p:|ps) y)
  | t == p = case ps of
               [] -> More (p,Just y) xs
               _  -> More (t,mx) $ fmap (`union` Rest (fromList ps) y) xs
  | t == def = More (def,mx) $ fmap (`union` Rest pss y) xs
  | p == def = (More (t,mx) xs) `union` (Rest (fromList ps) y)
  -- disjoint
  | otherwise = More (def,Nothing) $
                  (More (t,mx) xs) :| Rest pss y : []
union (Rest tss@(t:|ts) x) (More (p,my) ys)
  | t == p = case ts of
               [] -> More (t,Just x) ys
               _  -> More (p,my) $ fmap (Rest (fromList ts) x `union`) ys
  | t == def = (Rest (fromList ts) x) `union` (More (p,my) ys)
  | p == def = More (def,my) $ fmap (Rest tss x `union`) ys
  -- disjoint
  | otherwise = More (def,Nothing) $
                  Rest tss x :| (More (p,my) ys) : []

-- instance Default t =>

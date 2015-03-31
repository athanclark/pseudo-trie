{-# LANGUAGE DeriveFunctor #-}

module Data.Trie.Pseudo where

import           Data.Trie.Pseudo.Internal

import           Control.Applicative
import           Data.Default
import           Data.Foldable
import           Data.List.NonEmpty        (NonEmpty (..), fromList, toList)
import qualified Data.List.NonEmpty        as NE
import           Data.Maybe                (fromMaybe)
import           Data.Monoid
import qualified Data.Semigroup            as S
import           Prelude                   hiding (foldl, foldr, lookup, map)

-- TODO: normalize, difference
-- normalize:
--   - remove needless roots
--   - remove needless Nils

-- | Non-Empty Rose Tree with explicit emptyness
data PseudoTrie t a = More (t, Maybe a) (NonEmpty (PseudoTrie t a))
                    | Rest (NonEmpty t) a
                    | Nil
  deriving (Show, Eq, Functor)

instance Foldable (PseudoTrie t) where
  foldr _ acc Nil = acc
  foldr f acc (Rest _ x) = f x acc
  foldr f acc (More (t, Nothing) xs) = foldr go acc xs
    where
      go x bcc = foldr f bcc x
  foldr f acc (More (t, Just x) xs) = foldr go (f x acc) xs
    where
      go x bcc = foldr f bcc x

toAssocs :: (Default t) => PseudoTrie t a -> [(NonEmpty t, a)]
toAssocs = go (def :| []) []
  where
    go :: NonEmpty t -> [(NonEmpty t, a)] -> PseudoTrie t a -> [(NonEmpty t, a)]
    go depth acc Nil = acc
    go depth acc (Rest ts x) = (depth S.<> ts, x) : acc
    go depth acc (More (t, Nothing) xs) =
      foldr (flip $ go $ depth S.<> (t :| [])) acc $ NE.toList xs
    go depth acc (More (t, Just x) xs) =
      (depth S.<> (t :| []), x) :
        (foldr (flip $ go $ depth S.<> (t :| [])) acc $ NE.toList xs)

fromAssocs :: (Eq t, Default t) => [(NonEmpty t, a)] -> PseudoTrie t a
fromAssocs = foldr (uncurry add) Nil

instance (Eq t, Default t, Monoid a) => Monoid (PseudoTrie t a) where
  mempty = Nil
  mappend = unionWith mappend

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

add :: (Eq t, Default t) => NonEmpty t -> a -> PseudoTrie t a -> PseudoTrie t a
add ts = unionWith const . Rest ts

unionWith :: (Eq t, Default t) =>
             (a -> a -> a)
          -> PseudoTrie t a
          -> PseudoTrie t a
          -> PseudoTrie t a
unionWith _ Nil Nil = Nil
unionWith _ Nil y = y
unionWith _ x Nil = x
unionWith f (Rest tss@(t:|ts) x) (Rest pss@(p:|ps) y)
  | tss == pss = Rest pss $ f x y
  | t == p = case (ts,ps) of
               ([], p':ps') -> More (t, Just x) $ Rest (fromList ps) y :| []
               (t':ts', []) -> More (p, Just y) $ Rest (fromList ts) x :| []
               (_,_) -> More (t,Nothing) $ fromList
                          [unionWith f (Rest (fromList ts) x) (Rest (fromList ps) y)]
  -- root normalization
  | t == def = case ts of
                [] -> More (def,Just x) $ fromList [Rest pss y]
                _  -> unionWith f (Rest (fromList ts) x) (Rest pss y)
  | p == def = case ps of
                [] -> More (def,Just y) $ fromList [Rest tss y]
                _  -> unionWith f (Rest tss x) (Rest (fromList ps) y)
  | otherwise = More (def,Nothing) $ fromList [Rest tss x, Rest pss y]
unionWith f (More (t,mx) xs) (More (p,my) ys)
  | t == p = let zs = NE.toList xs ++ NE.toList ys in
             More (p,f <$> mx <*> my) $ fromList $
               foldl (\(z':zs') q -> unionWith f z' q : zs') [head zs] (tail zs)
  | t == def = More (def,mx) $
                 fmap ((flip $ unionWith f) $ More (p,my) ys) xs
  | p == def = More (def,my) $
                 fmap (unionWith f $ More (t,mx) xs) ys
  -- disjoint
  | otherwise = More (def,Nothing) $ fromList [More (t,mx) xs, More (p,my) ys]
unionWith f (More (t,mx) xs) (Rest pss@(p:|ps) y)
  | t == p = case ps of
               [] -> More (p,f <$> mx <*> Just y) xs
               _  -> More (t,mx) $ fmap ((flip $ unionWith f) $ Rest (fromList ps) y) xs
  | t == def = More (def,mx) $ fmap ((flip $ unionWith f) $ Rest pss y) xs
  | p == def = unionWith f (More (t,mx) xs) (Rest (fromList ps) y)
  -- disjoint
  | otherwise = More (def,Nothing) $ fromList [More (t,mx) xs, Rest pss y]
unionWith f (Rest tss@(t:|ts) x) (More (p,my) ys)
  | t == p = case ts of
               [] -> More (t,f <$> Just x <*> my) ys
               _  -> More (p,my) $ fmap (unionWith f $ Rest (fromList ts) x) ys
  | t == def = unionWith f (Rest (fromList ts) x) (More (p,my) ys)
  | p == def = More (def,my) $ fmap (unionWith f $ Rest tss x) ys
  -- disjoint
  | otherwise = More (def,Nothing) $ fromList [Rest tss x, More (p,my) ys]

intersectionWith :: (Eq t, Default t) =>
                    (a -> b -> c)
                 -> PseudoTrie t a
                 -> PseudoTrie t b
                 -> PseudoTrie t c
intersectionWith _ _ Nil = Nil
intersectionWith _ Nil _ = Nil
intersectionWith f (Rest tss@(t:|ts) x) (Rest pss@(p:|ps) y)
  | tss == pss = Rest pss $ f x y
  | t == def
 && p /= def = intersectionWith f (Rest (fromList ts) x) (Rest pss y)
  | p == def
 && t /= def = intersectionWith f (Rest tss x) (Rest (fromList ps) y)
  | otherwise = Nil
intersectionWith f (More (t,mx) xs) (More (p,my) ys)
  | t == p = case [intersectionWith f x' y' | x' <- NE.toList xs, y' <- NE.toList ys] of
               [] -> case f <$> mx <*> my of
                       Nothing -> Nil
                       Just c  -> Rest (p :| []) c
               zs -> More (p,f <$> mx <*> my) $ fromList $ zs
  -- implicit root
  | t == def = More (def,Nothing) $ fmap ((flip $ intersectionWith f) $ More (p,my) ys) xs
  | p == def = More (def,Nothing) $ fmap (intersectionWith f $ More (t,mx) xs) ys
  | otherwise = Nil
intersectionWith f (More (t,mx) xs) (Rest pss@(p:|ps) y)
  | t == p = case ps of
               [] -> case f <$> mx <*> Just y of
                     Nothing -> Nil
                     Just c  -> Rest (p :| []) c
               _  -> More (p,Nothing) $ fmap ((flip $ intersectionWith f) $ Rest (fromList ps) y) xs
  | otherwise = Nil
intersectionWith f (Rest tss@(t:|ts) x) (More (p,my) ys)
  | t == p = case ts of
               [] -> case f <$> Just x <*> my of
                     Nothing -> Nil
                     Just c  -> Rest (t :| []) c
               _  -> More (t,Nothing) $ fmap (intersectionWith f $ Rest (fromList ts) x) ys
  | otherwise = Nil

-- difference :: Eq t =>
--               PseudoTrie t a
--            -> PseudoTrie t a
--            -> PseudoTrie t a

-- instance Default t =>

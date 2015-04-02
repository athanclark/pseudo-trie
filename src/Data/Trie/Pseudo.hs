{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

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
import           Prelude                   hiding (foldl, foldr, foldr1, lookup,
                                            map)
import           Test.QuickCheck
import           Test.QuickCheck.Instances

-- TODO: difference
-- | Non-Empty Rose Tree with explicit emptyness
data PseudoTrie t a = More (t, Maybe a) (NonEmpty (PseudoTrie t a))
                    | Rest (NonEmpty t) a
                    | Nil
  deriving (Show, Eq, Functor)

instance (Arbitrary t, Arbitrary a) => Arbitrary (PseudoTrie t a) where
  arbitrary = do
    (ts :: [t]) <- listOf1 arbitrary
    (x :: a) <- arbitrary
    (t :: t) <- arbitrary
    (mx :: Maybe a) <- arbitrary
    (xs :: [PseudoTrie t a]) <- listOf1 arbitrary
    oneof [ return Nil
          , return $ Rest (fromList ts) x
          , return $ More (t,mx) $ fromList xs
          ]

-- | Depth first
instance Foldable (PseudoTrie t) where
  foldr _ acc Nil = acc
  foldr f acc (Rest _ x) = f x acc
  foldr f acc (More (t, Nothing) xs) = foldr go acc xs
    where
      go z bcc = foldr f bcc z
  foldr f acc (More (t, Just x) xs) = foldr go (f x acc) xs
    where
      go z bcc = foldr f bcc z

assign :: (Eq t) => NonEmpty t -> Maybe a -> PseudoTrie t a -> PseudoTrie t a
assign ts (Just x) Nil = Rest ts x
assign ts Nothing  Nil = Nil
assign tss@(t:|ts) mx (Rest pss@(p:|ps) y)
  | tss == pss = case mx of
                   (Just x) -> Rest pss x
                   Nothing  -> Nil
  | t == p = case ts of
               [] -> More (t,mx) $ Rest (NE.fromList ps) y :| []
               _  -> More (t,Nothing) $
                       (assign (NE.fromList ts) mx $ Rest (NE.fromList ps) y) :| []
assign (t:|ts) mx (More (p,my) ys)
  | t == p = case ts of
               [] -> More (p,mx) ys
               _  -> More (p,my) $ fmap (assign (NE.fromList ts) mx) ys

-- | Overwrite the LHS point-wise with the RHS's contents
merge :: (Eq t) => PseudoTrie t a -> PseudoTrie t a -> PseudoTrie t a
merge Nil y = y
merge x Nil = x
merge xx@(Rest tss@(t:|ts) x) (Rest pss@(p:|ps) y)
  | tss == pss = Rest pss y
  | t == p = case (ts,ps) of
               ([],p':ps') -> More (t,Just x) $ (Rest (NE.fromList ps) y) :| []
               (t':ts',[]) -> More (t,Just y) $ (Rest (NE.fromList ts) x) :| []
               (_,_)       -> More (t,Nothing) $
                                (merge (Rest (NE.fromList ts) x) $
                                       Rest (NE.fromList ps) y) :| []
  | otherwise = xx
merge xx@(More (t,mx) xs) (More (p,my) ys)
  | t == p = More (p,my) $ NE.fromList $
              foldr go [] (NE.toList xs) ++ (NE.toList ys)
  | otherwise = xx
  where
    go q [] = [q]
    go q (z:zs) | areDisjoint q z = q : z : zs
                | otherwise = merge q z : zs
merge xx@(More (t,mx) xs) (Rest pss@(p:|ps) y)
  | t == p = case ps of
               [] -> More (t,Just y) xs
               _  -> More (t,mx) $
                       fmap (flip merge $ Rest (NE.fromList ps) y) xs
  | otherwise = xx
merge xx@(Rest tss@(t:|ts) x) (More (p,my) ys)
  | t == p = case ts of
               [] -> More (p,Just x) ys
               _  -> More (p,my) $
                       fmap (merge $ Rest (NE.fromList ts) x) ys
  | otherwise = xx

toAssocs :: PseudoTrie t a -> [(NonEmpty t, a)]
toAssocs = go [] []
  where
    go :: [t] -> [(NonEmpty t, a)] -> PseudoTrie t a -> [(NonEmpty t, a)]
    go depth acc Nil = acc
    go depth acc (Rest ts x) = ((NE.fromList depth) S.<> ts, x) : acc
    go depth acc (More (t, Nothing) xs) =
      foldr (flip $ go $ depth ++ [t]) acc $ NE.toList xs
    go depth acc (More (t, Just x) xs) =
      (NE.fromList $ depth ++ [t], x) :
        ((foldr $ flip $ go $ depth ++ [t]) acc $ NE.toList xs)

fromAssocs :: (Eq t) => [(NonEmpty t, a)] -> PseudoTrie t a
fromAssocs = foldr (uncurry assign) Nil . fmap (\(x,y) -> (x,Just y))

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

areDisjoint :: (Eq t) => PseudoTrie t a -> PseudoTrie t a -> Bool
areDisjoint (More (t,_) _) (More (p,_) _)
  | t == p = False
  | otherwise = True
areDisjoint (Rest (t:|_) _) (Rest (p:|_) _)
  | t == p = False
  | otherwise = True
areDisjoint _ _ = True

data Rooted t a = Rooted (Maybe a) [PseudoTrie t a]
  deriving (Show, Eq, Functor)

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
                              [unionWith f (Rest (fromList ts) x) (Rest (fromList ps) y)]
    unionWith f (More (t,mx) xs) (More (p,my) ys)
      | t == p = let zs = NE.toList xs ++ NE.toList ys in
                 More (p,f <$> mx <*> my) $ fromList $
                   foldl (\(z':zs') q -> unionWith f z' q : zs') [head zs] (tail zs)
    unionWith f (More (t,mx) xs) (Rest pss@(p:|ps) y)
      | t == p = case ps of
                   [] -> More (p,f <$> mx <*> Just y) xs
                   _  -> More (t,mx) $ fmap ((flip $ unionWith f) $ Rest (fromList ps) y) xs
    unionWith f (Rest tss@(t:|ts) x) (More (p,my) ys)
      | t == p = case ts of
                   [] -> More (t,f <$> Just x <*> my) ys
                   _  -> More (p,my) $ fmap (unionWith f $ Rest (fromList ts) x) ys

intersectionWith :: (Eq t) =>
                    (a -> b -> c)
                 -> PseudoTrie t a
                 -> PseudoTrie t b
                 -> PseudoTrie t c
intersectionWith _ _ Nil = Nil
intersectionWith _ Nil _ = Nil
intersectionWith f (Rest tss@(t:|ts) x) (Rest pss@(p:|ps) y)
  | tss == pss = Rest pss $ f x y
  | otherwise = Nil
intersectionWith f (More (t,mx) xs) (More (p,my) ys)
  | t == p = case [intersectionWith f x' y' | x' <- NE.toList xs, y' <- NE.toList ys] of
               [] -> case f <$> mx <*> my of
                       Nothing -> Nil
                       Just c  -> Rest (p :| []) c
               zs -> More (p,f <$> mx <*> my) $ fromList $ zs
  -- implicit root
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

-- | Needless @More@ elements are turned into @Rest@, @Nil@'s in subtrees are
-- also removed.
prune :: (Eq t) => PseudoTrie t a -> PseudoTrie t a
prune = go Nothing
  where
    go :: (Eq t) => Maybe (NonEmpty t) -> PseudoTrie t a -> PseudoTrie t a
    go Nothing Nil = Nil
    go Nothing   (More (t,Nothing) xs) = foldr1 (flip merge) $
      fmap (go (Just $ NE.fromList [t])) $ removeNils $ NE.toList xs
    go (Just ts) (More (t,Nothing) xs) = foldr1 (flip merge) $
      fmap (go (Just $ NE.fromList $ (NE.toList ts) ++ [t])) $ removeNils $ NE.toList xs
    -- lookahead
    go (Just ts) (More (t,Just c) (Nil :| [])) =
      Rest (NE.fromList $ (NE.toList ts) ++ [t]) c
    go _         (More (t,Just c) xs) =
      More (t,Just c) $ NE.fromList $
        fmap (go Nothing) $ removeNils $ NE.toList xs
    go (Just ts) (Rest ps x) =
      Rest (NE.fromList $ NE.toList ts ++ NE.toList ps) x
    go Nothing x@(Rest _  _) = x

    removeNils :: [PseudoTrie t a] -> [PseudoTrie t a]
    removeNils [] = []
    removeNils (Nil:xs) = removeNils xs
    removeNils (x:xs) = x : removeNils xs

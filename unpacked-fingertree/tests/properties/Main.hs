{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Prelude hiding (null, reverse, lookup)

import Control.Monad.State
import qualified Data.List as List
import qualified Safe as List (atMay)
import Data.MonoTraversable

import Test.FingerTree.Internal

import Test.Tasty
import Test.Tasty.QuickCheck

import Debug.Trace

main :: IO ()
main = defaultMain properties

properties :: TestTree
properties = testGroup "list operations" $
  [ testProperty "ofoldMap" prop_ofoldMap
  , testProperty "ofoldr" prop_ofoldr
  , testProperty "ofoldl" prop_ofoldl
  , testProperty "ofoldr1Ex" prop_ofoldr1Ex
  , testProperty "ofoldl1Ex" prop_ofoldl1Ex
  , testProperty "otraverse" prop_otraverse
  , testProperty "(==)" prop_equality
  , testProperty "compare" prop_compare
  , testProperty "compare_eq" prop_compare_eq
  , testProperty "omap" prop_omap
  , testProperty "empty" prop_empty
  , testProperty "singleton" prop_singleton
  , testProperty "(<|)" prop_cons
  , testProperty "(|>)" prop_snoc
  , testProperty "mempty" prop_mempty
  , testProperty "mappend" prop_mappend
  , testProperty "fromList" prop_fromList
  , testProperty "null" prop_null
  , testProperty "viewl" prop_viewl
  , testProperty "viewr" prop_viewr
  , testProperty "search" prop_search
  , testProperty "split" prop_split
  , testProperty "takeUntil" prop_takeUntil
  , testProperty "dropUntil" prop_dropUntil
  , testProperty "lookup" prop_lookup
  , testProperty "reverse" prop_reverse
  , testProperty "omapWithPos" prop_omapWithPos
  , testProperty "omapWithContext" prop_omapWithContext
  , testProperty "otraverseWithPos" prop_otraverseWithPos
  , testProperty "otraverseWithContext" prop_otraverseWithContext
  ]

prop_ofoldMap :: FingerTree -> Bool
prop_ofoldMap xs = ofoldMap f xs == Prelude.foldMap f (otoList xs)
  where
    f = (:[])

prop_ofoldr :: FingerTree -> Bool
prop_ofoldr xs = ofoldr f z xs == Prelude.foldr f z (otoList xs)
  where
    f = (:)
    z = []

prop_ofoldl :: FingerTree -> Bool
prop_ofoldl xs = ofoldl' f z xs == List.foldl' f z (otoList xs)
  where
    f = flip (:)
    z = []

prop_ofoldr1Ex :: Gen Bool
prop_ofoldr1Ex = do
  xs <- arbitrary `suchThat` (not . null)
  pure $ ofoldr1Ex f xs == List.foldr1 f (otoList xs)
 where
  f = (+)

prop_ofoldl1Ex :: Gen Bool
prop_ofoldl1Ex = do
  xs <- arbitrary `suchThat` (not . null)
  pure $ ofoldl1Ex' f xs == List.foldl1' f (otoList xs)
 where
  f = (+)

prop_otraverse :: FingerTree -> Bool
prop_otraverse xs =
 let f :: Elem -> State Elem Elem
     f x = do
       modify' (+x)
       get
     xs' = flip evalState 0 (otraverse f xs)
     xs'' = flip evalState 0 (traverse f (otoList xs))
  in validateMeasures xs' && otoList xs' == xs''

-- Verify somewhat that internal structure is quotiented out
prop_equality :: FingerTree -> Bool
prop_equality xs
  =  xs == (foldr (<|) empty (otoList xs))
  && xs == (List.foldl' (|>) empty (otoList xs))

prop_compare :: FingerTree -> FingerTree -> Bool
prop_compare xs ys = compare xs ys == compare (otoList xs) (otoList ys)

prop_compare_eq :: FingerTree -> Bool
prop_compare_eq xs
  =  EQ == compare xs (foldr (<|) empty (otoList xs))
  && EQ == compare xs (List.foldl' (|>) empty (otoList xs))

prop_omap :: FingerTree -> Bool
prop_omap xs = otoList (omap f xs) == fmap f (otoList xs)
 where
  f = (*2)

prop_empty :: Bool
prop_empty = otoList empty == []

prop_singleton :: Elem -> Bool
prop_singleton x = otoList (singleton x) == pure x

prop_cons :: Elem -> FingerTree -> Bool
prop_cons x xs =
  let xxs = x <| xs
   in validateMeasures xxs && otoList (x <| xs) == x : otoList xs

prop_snoc :: FingerTree -> Elem -> Bool
prop_snoc xs x =
  let xsx = xs |> x
   in validateMeasures xsx && otoList (xs |> x) == List.reverse (x : List.reverse (otoList xs))

prop_mempty :: Bool
prop_mempty = otoList @FingerTree mempty == mempty

prop_mappend :: Gen Bool
prop_mappend = do
  xss <- replicateM 100 arbitrary
  let xs = foldMap fromList xss
  pure $ otoList xs == foldMap id xss

prop_fromList :: [Elem] -> Bool
prop_fromList xs =
  let xs' = fromList xs
   in validateMeasures xs' && otoList xs' == xs

prop_null :: FingerTree -> Property
prop_null xs = not (null xs) ==> not (List.null (otoList xs))

prop_viewl :: Elem -> FingerTree -> Bool
prop_viewl x xs = case viewl (x <| xs) of
  EmptyL -> False
  y :< ys -> x == y && otoList xs == otoList ys

prop_viewr :: FingerTree -> Elem -> Bool
prop_viewr xs x = case viewr (xs |> x) of
  EmptyR -> False
  ys :> y -> xs == ys && x == y

prop_search :: FingerTree -> Bool
prop_search xs = case search p xs of
  OnLeft -> False
  OnRight -> null xs
  Nowhere -> False
  Position as b bs ->
    let as' = otoList as
        bs' = otoList bs
     in validateMeasures as
        && validateMeasures bs
        && List.length (as' <> [b]) > List.length bs'
 where
  p m1 m2 = List.length m1 > List.length m2

prop_split :: Int -> FingerTree -> Bool
prop_split n xs =
  let f = (> n) . List.length
      (as, bs) = split f xs
   in validateMeasures as && validateMeasures bs && (otoList as, otoList bs) == Prelude.splitAt n (otoList xs)

prop_takeUntil :: Int -> FingerTree -> Bool
prop_takeUntil n xs =
  let f = (> n) . List.length
      xs' = takeUntil f xs
   in validateMeasures xs' && otoList xs' == take n (otoList xs)
 where

prop_dropUntil :: Int -> FingerTree -> Bool
prop_dropUntil n xs =
  let f = (> n) . List.length
      xs' = dropUntil f xs
   in validateMeasures xs' && otoList xs' == drop n (otoList xs)

prop_lookup :: Int -> FingerTree -> Bool
prop_lookup n xs =
  let f = (> n) . List.length
      x = lookup f xs
   in x == flip List.atMay n (otoList xs)

prop_reverse :: FingerTree -> Bool
prop_reverse xs = otoList (reverse xs) == List.reverse (otoList xs)

prop_omapWithPos :: FingerTree -> Bool
prop_omapWithPos xs =
  let f ys y = List.length ys + y
      xs' = omapWithPos f xs
   in validateMeasures xs' && otoList xs' == zipWith f (List.inits (otoList xs)) (otoList xs)

prop_omapWithContext :: FingerTree -> Bool
prop_omapWithContext xs =
  let f ys y zs = List.length ys + y - List.length zs
      xs' = omapWithContext f xs
      xs'' = zipWith3 f (List.inits (otoList xs)) (otoList xs) (fmap tail (List.tails (otoList xs)))
   in otoList xs' == xs''

prop_otraverseWithPos :: FingerTree -> Bool
prop_otraverseWithPos xs =
 let f :: Measure -> Elem -> State Elem Elem
     f ys x = do
       modify' (+x)
       modify' (subtract $ List.length ys)
       get
     xs' = flip evalState 0 (otraverseWithPos f xs)
     xs'' = flip evalState 0 $ traverse (uncurry f) $ zip (List.inits (otoList xs)) (otoList xs)
  in validateMeasures xs' && otoList xs' == xs''

prop_otraverseWithContext :: FingerTree -> Bool
prop_otraverseWithContext xs =
 let f :: Measure -> Elem -> Measure -> State Elem Elem
     f ys x zs = do
       modify' (+x)
       modify' (subtract $ List.length ys)
       modify' (* List.length zs)
       get
     xs' = flip evalState 0 (otraverseWithContext f xs)
     xs'' = flip evalState 0 $ traverse (\(x,y,z) -> f x y z) $ zip3
       (List.inits (otoList xs))
       (otoList xs)
       (fmap tail (List.tails (otoList xs)))
  in validateMeasures xs' && otoList xs' == xs''


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module FingerTree
  ( Elem
  , Measure
  , FingerTree
  , empty
  , singleton
  , (<|)
  , (|>)
  , (><)
  , fromList
  , null
  , ViewL(..)
  , viewl
  , ViewR(..)
  , viewr
  , SearchResult (..)
  , search
  , split
  , takeUntil
  , dropUntil
  , reverse
  , omapWithPos
  , omapWithContext
  , otraverseWithPos
  , otraverseWithContext
  ) where

import Control.DeepSeq
import Prelude hiding (null, reverse)
import Data.MonoTraversable
import GHC.Generics

import Measured

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

infixr 5 <<|, :<<
infixl 5 |>>, :>>

data ViewL
   = EmptyL
   | Elem :< FingerTree

deriving instance (Eq Elem, Eq Measure) => Eq ViewL
deriving instance (Ord Elem, Ord Measure) => Ord ViewL

data ViewR
   = EmptyR
   | FingerTree :> Elem

deriving instance (Eq Elem, Eq Measure) => Eq ViewR
deriving instance (Ord Elem, Ord Measure) => Ord ViewR

data ViewNL l
   = EmptyNL
   | Node l :<< DeepTree l

data ViewNR l
   = EmptyNR
   | DeepTree l :>> Node l

data Level = Level_Leaf | Level_Branch Level

data Node l where
  Node_Leaf2
    :: {-# UNPACK #-} !Measure
    -> {-# UNPACK #-} !Elem
    -> {-# UNPACK #-} !Elem
    -> Node 'Level_Leaf
  Node_Leaf3
    :: {-# UNPACK #-} !Measure
    -> {-# UNPACK #-} !Elem
    -> {-# UNPACK #-} !Elem
    -> {-# UNPACK #-} !Elem
    -> Node 'Level_Leaf
  Node_Branch2
    :: {-# UNPACK #-} !Measure
    -> Node l
    -> Node l
    -> Node ('Level_Branch l)
  Node_Branch3
    :: {-# UNPACK #-} !Measure
    -> Node l
    -> Node l
    -> Node l
    -> Node ('Level_Branch l)

deriving instance (Eq Measure, Eq Elem) => Eq (Node l)
deriving instance (Ord Measure, Ord Elem) => Ord (Node l)

measureNode :: Node l -> Measure
measureNode = \case
  Node_Leaf2 m _ _ -> m
  Node_Leaf3 m _ _ _ -> m
  Node_Branch2 m _ _ -> m
  Node_Branch3 m _ _ _ -> m

node2L :: Elem -> Elem -> Node 'Level_Leaf
node2L a b = Node_Leaf2 (measure a <> measure b) a b

node3L :: Elem -> Elem -> Elem -> Node 'Level_Leaf
node3L a b c = Node_Leaf3 (measure a <> measure b <> measure c) a b c

node2N :: Node l -> Node l -> Node ('Level_Branch l)
node2N a b = Node_Branch2 (measureNode a <> measureNode b) a b

node3N :: Node l -> Node l -> Node l -> Node ('Level_Branch l)
node3N a b c = Node_Branch3 (measureNode a <> measureNode b <> measureNode c) a b c

type DigitN l =
  (# Node l
  | (# Node l, Node l #)
  | (# Node l, Node l, Node l #)
  | (# Node l, Node l, Node l, Node l #)
  #)

pattern OneN :: forall (l :: Level). Node l -> DigitN l
pattern OneN x = (# x | | | #) :: DigitN l
pattern TwoN :: forall (l :: Level). Node l -> Node l -> DigitN l
pattern TwoN x y = (# | (# x, y #) | | #) :: DigitN l
pattern ThreeN :: forall (l :: Level). Node l -> Node l -> Node l -> DigitN l
pattern ThreeN x y z = (# | | (# x, y, z #) | #) :: DigitN l
pattern FourN :: forall (l :: Level). Node l -> Node l -> Node l -> Node l -> DigitN l
pattern FourN w x y z = (# | | | (# w, x, y, z #) #) :: DigitN l

{-# COMPLETE OneN, TwoN, ThreeN, FourN #-}

measureDigitN :: DigitN l -> Measure
measureDigitN = \case
  (# x | | | #) -> measureNode x
  (# | (# x, y #) | | #) -> measureNode x <> measureNode y
  (# | | (# x, y, z #) | #) -> measureNode x <> measureNode y <> measureNode z
  (# | | | (# w, x, y, z #) #) -> measureNode w <> measureNode x <> measureNode y <> measureNode z

eqDigitN :: (Eq Measure, Eq Elem) => DigitN l -> DigitN l -> Bool
eqDigitN = \case
  OneN a1 -> \case
    OneN a2 -> a1 == a2
    _ -> False
  TwoN a1 b1 -> \case
    TwoN a2 b2 -> a1 == a2 && b1 == b2
    _ -> False
  ThreeN a1 b1 c1 -> \case
    ThreeN a2 b2 c2 -> a1 == a2 && b1 == b2 && c1 == c2
    _ -> False
  FourN a1 b1 c1 d1 -> \case
    FourN a2 b2 c2 d2 -> a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2
    _ -> False

compareDigitN :: (Ord Measure, Ord Elem) => DigitN l -> DigitN l -> Ordering
compareDigitN = \case
  OneN a1 -> \case
    OneN a2 -> compare a1 a2
    _ -> LT
  TwoN a1 b1 -> \case
    OneN _ -> GT
    TwoN a2 b2 -> mconcat
      [ compare a1 a2
      , compare b1 b2
      ]
    _ -> LT
  ThreeN a1 b1 c1 -> \case
    OneN _ -> GT
    TwoN _ _ -> GT
    ThreeN a2 b2 c2 -> mconcat
      [ compare a1 a2
      , compare b1 b2
      , compare c1 c2
      ]
    _ -> LT
  FourN a1 b1 c1 d1 -> \case
    FourN a2 b2 c2 d2 -> mconcat
      [ compare a1 a2
      , compare b1 b2
      , compare c1 c2
      , compare d1 d2
      ]
    _ -> GT

type DigitL =
  (# Elem
  | (# Elem, Elem #)
  | (# Elem, Elem, Elem #)
  | (# Elem, Elem, Elem, Elem #)
  #)

pattern OneL :: Elem -> DigitL
pattern OneL x = (# x | | | #) :: DigitL
pattern TwoL :: Elem -> Elem -> DigitL
pattern TwoL x y = (# | (# x, y #) | | #) :: DigitL
pattern ThreeL :: Elem -> Elem -> Elem -> DigitL
pattern ThreeL x y z = (# | | (# x, y, z #) | #) :: DigitL
pattern FourL :: Elem -> Elem -> Elem -> Elem -> DigitL
pattern FourL w x y z = (# | | | (# w, x, y, z #) #) :: DigitL

{-# COMPLETE OneL, TwoL, ThreeL, FourL #-}

measureDigitL :: DigitL -> Measure
measureDigitL = \case
  OneL x -> measure x
  TwoL x y -> measure x <> measure y
  ThreeL x y z -> mconcat [ measure x, measure y, measure z ]
  FourL w x y z -> mconcat [ measure w, measure x, measure y, measure z ]

nodeToDigitN :: Node ('Level_Branch l) -> DigitN l
nodeToDigitN = \case
  Node_Branch2 _ x y -> (# | (# x, y #) | | #)
  Node_Branch3 _ x y z -> (# | | (# x, y, z #) | #)

nodeToDigitL :: Node 'Level_Leaf -> DigitL
nodeToDigitL = \case
  Node_Leaf2 _ x y -> TwoL x y
  Node_Leaf3 _ x y z -> ThreeL x y z

eqDigitL :: Eq Elem => DigitL -> DigitL -> Bool
eqDigitL = \case
  OneL a1 -> \case
    OneL a2 -> a1 == a2
    _ -> False
  TwoL a1 b1 -> \case
    TwoL a2 b2 -> a1 == a2 && b1 == b2
    _ -> False
  ThreeL a1 b1 c1 -> \case
    ThreeL a2 b2 c2 -> a1 == a2 && b1 == b2 && c1 == c2
    _ -> False
  FourL a1 b1 c1 d1 -> \case
    FourL a2 b2 c2 d2 -> a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2
    _ -> False

compareDigitL :: Ord Elem => DigitL -> DigitL -> Ordering
compareDigitL = \case
  OneL a1 -> \case
    OneL a2 -> compare a1 a2
    _ -> LT
  TwoL a1 b1 -> \case
    OneL _ -> GT
    TwoL a2 b2 -> mconcat
      [ compare a1 a2
      , compare b1 b2
      ]
    _ -> LT
  ThreeL a1 b1 c1 -> \case
    OneL _ -> GT
    TwoL _ _ -> GT
    ThreeL a2 b2 c2 -> mconcat
      [ compare a1 a2
      , compare b1 b2
      , compare c1 c2
      ]
    _ -> LT
  FourL a1 b1 c1 d1 -> \case
    FourL a2 b2 c2 d2 -> mconcat
      [ compare a1 a2
      , compare b1 b2
      , compare c1 c2
      , compare d1 d2
      ]
    _ -> GT

data DeepTree l where
  DeepTree_Empty
    :: DeepTree l
  DeepTree_Single
    :: Node l
    -> DeepTree l
  DeepTree_Deep
    :: {-# UNPACK #-} !Measure
    -> DigitN l
    -> DeepTree ('Level_Branch l)
    -> DigitN l
    -> DeepTree l

instance (Eq Elem, Eq Measure) => Eq (DeepTree l) where
  a == b = case (a, b) of
    (DeepTree_Empty, DeepTree_Empty) -> True
    (DeepTree_Single x, DeepTree_Single y) -> x == y
    (DeepTree_Deep m1 pr1 t1 sf1, DeepTree_Deep m2 pr2 t2 sf2)
      -> m1 == m2
      && eqDigitN pr1 pr2
      && t1 == t2
      && eqDigitN sf1 sf2
    (_, _) -> False

instance (Ord Elem, Ord Measure) => Ord (DeepTree l) where
  compare a b = case (a, b) of
    (DeepTree_Empty, DeepTree_Empty) -> EQ
    (DeepTree_Empty, _) -> LT
    (DeepTree_Single _, DeepTree_Empty) -> GT
    (DeepTree_Single x, DeepTree_Single y) -> compare x y
    (DeepTree_Single _, _) -> LT
    (DeepTree_Deep m1 pr1 t1 sf1, DeepTree_Deep m2 pr2 t2 sf2)
      -> mconcat
        [ compare m1 m2
        , compareDigitN pr1 pr2
        , compare t1 t2
        , compareDigitN sf1 sf2
        ]
    (DeepTree_Deep _ _ _ _, _) -> GT

measureDeepTree :: DeepTree l -> Measure
measureDeepTree = \case
  DeepTree_Empty -> mempty
  DeepTree_Single n -> measureNode n
  DeepTree_Deep m _ _ _ -> m

data FingerTree
   = FingerTree_Empty
   | FingerTree_Single {-# UNPACK #-} !Elem
   | FingerTree_Deep Measure DigitL (DeepTree 'Level_Leaf) DigitL

instance (NFData Elem, NFData Measure) => NFData FingerTree where
  rnf = \case
    FingerTree_Empty -> ()
    FingerTree_Single x -> rnf x
    FingerTree_Deep m pr t sf -> rnf m `seq` rnfDigitL pr `seq` rnfDeepTree t `seq` rnfDigitL sf

rnfDigitL :: NFData Elem => DigitL -> ()
rnfDigitL = \case
  OneL x -> rnf x
  TwoL x y -> rnf x `seq` rnf y
  ThreeL x y z -> rnf x `seq` rnf y `seq` rnf z
  FourL w x y z -> rnf w `seq` rnf x `seq` rnf y `seq` rnf z

rnfDeepTree :: (NFData Elem, NFData Measure) => DeepTree l -> ()
rnfDeepTree = \case
  DeepTree_Empty -> ()
  DeepTree_Single x -> rnfNode x
  DeepTree_Deep m pr t sf -> rnf m `seq` rnfDigitN pr `seq` rnfDeepTree t `seq` rnfDigitN sf

rnfDigitN :: (NFData Elem, NFData Measure) => DigitN l -> ()
rnfDigitN = \case
  OneN x -> rnfNode x
  TwoN x y -> rnfNode x `seq` rnfNode y
  ThreeN x y z -> rnfNode x `seq` rnfNode y `seq` rnfNode z
  FourN w x y z -> rnfNode w `seq` rnfNode x `seq` rnfNode y `seq` rnfNode z

rnfNode :: (NFData Elem, NFData Measure) => Node l -> ()
rnfNode = \case
  Node_Leaf2 m x y -> rnf m `seq` rnf x `seq` rnf y
  Node_Leaf3 m x y z -> rnf m `seq` rnf x `seq` rnf y `seq` rnf z
  Node_Branch2 m x y -> rnf m `seq` rnfNode x `seq` rnfNode y
  Node_Branch3 m x y z -> rnf m `seq` rnfNode x `seq` rnfNode y `seq` rnfNode z

instance (Eq Elem, Eq Measure) => Eq FingerTree where
  a == b = case (a, b) of
    (FingerTree_Empty, FingerTree_Empty) -> True
    (FingerTree_Single x, FingerTree_Single y) -> x == y
    (FingerTree_Deep m1 pr1 t1 sf1, FingerTree_Deep m2 pr2 t2 sf2)
      -> m1 == m2
      && eqDigitL pr1 pr2
      && t1 == t2
      && eqDigitL sf1 sf2
    (_, _) -> False

instance (Ord Elem, Ord Measure) => Ord FingerTree where
  compare a b = case (a, b) of
    (FingerTree_Empty, FingerTree_Empty) -> EQ
    (FingerTree_Empty, _) -> LT
    (FingerTree_Single _, FingerTree_Empty) -> GT
    (FingerTree_Single x, FingerTree_Single y) -> compare x y
    (FingerTree_Single _, _) -> LT
    (FingerTree_Deep m1 pr1 t1 sf1, FingerTree_Deep m2 pr2 t2 sf2)
      -> mconcat
        [ compare m1 m2
        , compareDigitL pr1 pr2
        , compare t1 t2
        , compareDigitL sf1 sf2
        ]
    (FingerTree_Deep _ _ _ _, _) -> GT

measureFingerTree :: FingerTree -> Measure
measureFingerTree = \case
  FingerTree_Empty -> mempty
  FingerTree_Single n -> measure n
  FingerTree_Deep m _ _ _ -> m

deepL
  :: DigitL
  -> DeepTree 'Level_Leaf
  -> DigitL
  -> FingerTree
deepL pr m sf = FingerTree_Deep
  (measureDigitL pr <> measureDeepTree m <> measureDigitL sf)
  pr
  m
  sf

deepN
  :: DigitN l
  -> DeepTree ('Level_Branch l)
  -> DigitN l
  -> DeepTree l
deepN pr m sf = DeepTree_Deep
  (measureDigitN pr <> measureDeepTree m <> measureDigitN sf)
  pr
  m
  sf

----

type instance Element FingerTree = Elem

instance MonoFunctor FingerTree where
  omap f = \case
    FingerTree_Empty -> FingerTree_Empty
    FingerTree_Single x -> FingerTree_Single (f x)
    FingerTree_Deep _ pr t sf -> deepL
      (omapDigitL f pr)
      (omapDeepTree f t)
      (omapDigitL f sf)

omapDigitL :: (Elem -> Elem) -> DigitL -> DigitL
omapDigitL f = \case
  OneL x -> OneL (f x)
  TwoL x y -> TwoL (f x) (f y)
  ThreeL x y z -> ThreeL (f x) (f y) (f z)
  FourL w x y z -> FourL (f w) (f x) (f y) (f z)

omapDeepTree :: (Elem -> Elem) -> DeepTree l -> DeepTree l
omapDeepTree f = \case
  DeepTree_Empty -> DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single (omapNode f x)
  DeepTree_Deep _ pr t sf -> deepN
    (omapDigitN f pr)
    (omapDeepTree f t)
    (omapDigitN f sf)

omapNode :: (Elem -> Elem) -> Node l -> Node l
omapNode f = \case
  Node_Leaf2 _ x y -> node2L (f x) (f y)
  Node_Leaf3 _ x y z -> node3L (f x) (f y) (f z)
  Node_Branch2 _ x y -> node2N (omapNode f x) (omapNode f y)
  Node_Branch3 _ x y z -> node3N (omapNode f x) (omapNode f y) (omapNode f z)

omapDigitN :: (Elem -> Elem) -> DigitN l -> DigitN l
omapDigitN f = \case
  OneN x -> OneN (omapNode f x)
  TwoN x y -> TwoN (omapNode f x) (omapNode f y)
  ThreeN x y z -> ThreeN (omapNode f x) (omapNode f y) (omapNode f z)
  FourN w x y z -> FourN (omapNode f w) (omapNode f x) (omapNode f y) (omapNode f z)

instance MonoFoldable FingerTree where
  ofoldMap f = \case
    FingerTree_Empty -> mempty
    FingerTree_Single x -> f x
    FingerTree_Deep _ pr t sf -> mconcat
      [ ofoldMapDigitL f pr
      , ofoldMapDeepTree f t
      , ofoldMapDigitL f sf
      ]
  ofoldr f x0 = \case
    FingerTree_Empty -> x0
    FingerTree_Single x -> f x x0
    FingerTree_Deep _ pr t sf -> ofoldrDigitL f (ofoldrDeepTree f (ofoldrDigitL f x0 sf) t) pr
  ofoldl' f x0 = \case
    FingerTree_Empty -> x0
    FingerTree_Single x -> f x0 x
    FingerTree_Deep _ pr t sf -> (ofoldlDigitL f $! (ofoldlDeepTree f $! ofoldlDigitL f x0 pr) t) sf
  ofoldr1Ex f = \case
    FingerTree_Empty -> error "ofoldr1Ex: empty FingerTree"
    FingerTree_Single x -> x
    FingerTree_Deep _ pr t sf -> ofoldrDigitL f (ofoldrDeepTree f (ofoldr1DigitL f sf) t) pr
  ofoldl1Ex' f = \case
    FingerTree_Empty -> error "ofoldr1Ex: empty FingerTree"
    FingerTree_Single x -> x
    FingerTree_Deep _ pr t sf -> (ofoldlDigitL f $! (ofoldlDeepTree f $! ofoldl1DigitL f pr) t) sf

ofoldMapDigitL :: Monoid m => (Elem -> m) -> DigitL -> m
ofoldMapDigitL f = \case
  OneL x -> f x
  TwoL x y -> f x <> f y
  ThreeL x y z -> f x <> f y <> f z
  FourL w x y z -> f w <> f x <> f y <> f z

ofoldMapDeepTree :: Monoid m => (Elem -> m) -> DeepTree l -> m
ofoldMapDeepTree f = \case
  DeepTree_Empty -> mempty
  DeepTree_Single x -> ofoldMapNode f x
  DeepTree_Deep _ pr t sf -> ofoldMapDigitN f pr <> ofoldMapDeepTree f t <> ofoldMapDigitN f sf

ofoldMapNode :: Monoid m => (Elem -> m) -> Node l -> m
ofoldMapNode f = \case
  Node_Leaf2 _ x y -> f x <> f y
  Node_Leaf3 _ x y z -> f x <> f y <> f z
  Node_Branch2 _ x y -> ofoldMapNode f x <> ofoldMapNode f y
  Node_Branch3 _ x y z -> ofoldMapNode f x <> ofoldMapNode f y <> ofoldMapNode f z

ofoldMapDigitN :: Monoid m => (Elem -> m) -> DigitN l -> m
ofoldMapDigitN f = \case
  OneN x -> ofoldMapNode f x
  TwoN x y -> ofoldMapNode f x <> ofoldMapNode f y
  ThreeN x y z -> ofoldMapNode f x <> ofoldMapNode f y <> ofoldMapNode f z
  FourN w x y z -> ofoldMapNode f w <> ofoldMapNode f x <> ofoldMapNode f y <> ofoldMapNode f z

ofoldrDigitL
  :: (Elem -> r -> r)
  -> r
  -> DigitL
  -> r
ofoldrDigitL f x0 = \case
  OneL x -> f x x0
  TwoL x y -> f x (f y x0)
  ThreeL x y z -> f x (f y (f z x0))
  FourL w x y z -> f w (f x (f y (f z x0)))

ofoldr1DigitL
  :: (Elem -> Elem -> Elem)
  -> DigitL
  -> Elem
ofoldr1DigitL f = \case
  OneL x -> x
  TwoL x y -> f x y
  ThreeL x y z -> f x (f y z)
  FourL w x y z -> f w (f x (f y z))

ofoldl1DigitL
  :: (Elem -> Elem -> Elem)
  -> DigitL
  -> Elem
ofoldl1DigitL f = \case
  OneL x -> x
  TwoL x y -> f x y
  ThreeL x y z -> (f $! f x y) z
  FourL w x y z -> (f $! (f $! f w x) y) z

ofoldrDeepTree
  :: (Elem -> r -> r)
  -> r
  -> DeepTree l
  -> r
ofoldrDeepTree f x0 = \case
  DeepTree_Empty -> x0
  DeepTree_Single x -> ofoldrNode f x0 x
  DeepTree_Deep _ pr t sf -> ofoldrDigitN f (ofoldrDeepTree f (ofoldrDigitN f x0 sf) t) pr

ofoldrDigitN
  :: (Elem -> r -> r)
  -> r
  -> DigitN l
  -> r
ofoldrDigitN f x0 = \case
  OneN x -> ofoldrNode f x0 x
  TwoN x y -> ofoldrNode f (ofoldrNode f x0 y) x
  ThreeN x y z -> ofoldrNode f (ofoldrNode f (ofoldrNode f x0 z) y) x
  FourN w x y z -> ofoldrNode f (ofoldrNode f (ofoldrNode f (ofoldrNode f x0 z) y) x) w

ofoldrNode
  :: (Elem -> r -> r)
  -> r
  -> Node l
  -> r
ofoldrNode f x0 = \case
  Node_Leaf2 _ x y -> f x (f y x0)
  Node_Leaf3 _ x y z -> f x (f y (f z x0))
  Node_Branch2 _ x y -> ofoldrNode f (ofoldrNode f x0 y) x
  Node_Branch3 _ x y z -> ofoldrNode f (ofoldrNode f (ofoldrNode f x0 z) y) x

ofoldlDigitL
  :: (r -> Elem -> r)
  -> r
  -> DigitL
  -> r
ofoldlDigitL f x0 = \case
  OneL x -> f x0 x
  TwoL x y -> (f $! f x0 x) y
  ThreeL x y z -> (f $! (f $! f x0 x) y) z
  FourL w x y z -> (f $! (f $! (f $! f x0 w) x) y) z

ofoldlDeepTree
  :: (r -> Elem -> r)
  -> r
  -> DeepTree l
  -> r
ofoldlDeepTree f x0 = \case
  DeepTree_Empty -> x0
  DeepTree_Single x -> ofoldlNode f x0 x
  DeepTree_Deep _ pr t sf -> (ofoldlDigitN f $! (ofoldlDeepTree f $! ofoldlDigitN f x0 pr) t) sf

ofoldlDigitN
  :: (r -> Elem -> r)
  -> r
  -> DigitN l
  -> r
ofoldlDigitN f x0 = \case
  OneN x -> ofoldlNode f x0 x
  TwoN x y -> (ofoldlNode f $! ofoldlNode f x0 y) x
  ThreeN x y z -> (ofoldlNode f $! (ofoldlNode f $! ofoldlNode f x0 x) y) z
  FourN w x y z -> (ofoldlNode f $! (ofoldlNode f $! (ofoldlNode f $! ofoldlNode f x0 w) x) y) z

ofoldlNode
  :: (r -> Elem -> r)
  -> r
  -> Node l
  -> r
ofoldlNode f x0 = \case
  Node_Leaf2 _ x y -> (f $! f x0 x) y
  Node_Leaf3 _ x y z -> (f $! (f $! f x0 x) y) z
  Node_Branch2 _ x y -> (ofoldlNode f $! ofoldlNode f x0 x) y
  Node_Branch3 _ x y z -> (ofoldlNode f $! (ofoldlNode f $! ofoldlNode f x0 x) y) z

instance MonoTraversable FingerTree where
  otraverse f = \case
    FingerTree_Empty -> pure FingerTree_Empty
    FingerTree_Single x -> FingerTree_Single <$> f x
    FingerTree_Deep _ pr t sf -> otraverseDigitL (otraverseDigitL (pure deepL) f pr <*> otraverseDeepTree f t) f sf

withOneL :: Functor f => f (DigitL -> b) -> f (Elem -> b)
withOneL = fmap (\f x -> f (OneL x))

withTwoL :: Applicative f => f (DigitL -> b) -> f (Elem -> Elem -> b)
withTwoL = fmap (\f x y -> f (TwoL x y))

withThreeL :: Applicative f => f (DigitL -> b) -> f (Elem -> Elem -> Elem -> b)
withThreeL = fmap (\f x y z -> f (ThreeL x y z))

withFourL :: Applicative f => f (DigitL -> b) -> f (Elem -> Elem -> Elem -> Elem -> b)
withFourL = fmap (\f w x y z -> f (FourL w x y z))

otraverseDigitL :: Applicative f => f (DigitL -> b) -> (Elem -> f Elem) -> DigitL -> f b
otraverseDigitL k f d = case d of
  OneL x -> withOneL k <*> f x
  TwoL x y -> withTwoL k <*> f x <*> f y
  ThreeL x y z -> withThreeL k <*> f x <*> f y <*> f z
  FourL w x y z -> withFourL k <*> f w <*> f x <*> f y <*> f z

otraverseDeepTree :: Applicative f => (Elem -> f Elem) -> DeepTree l -> f (DeepTree l)
otraverseDeepTree f = \case
  DeepTree_Empty -> pure DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single <$> otraverseNode f x
  DeepTree_Deep _ pr t sf -> otraverseDigitN (otraverseDigitN (pure deepN) f pr <*> otraverseDeepTree f t) f sf

withOneN :: Functor f => f (DigitN l -> b) -> f (Node l -> b)
withOneN = fmap (\f x -> f (OneN x))

withTwoN :: Applicative f => f (DigitN l -> b) -> f (Node l -> Node l -> b)
withTwoN = fmap (\f x y -> f (TwoN x y))

withThreeN :: Applicative f => f (DigitN l -> b) -> f (Node l -> Node l -> Node l -> b)
withThreeN = fmap (\f x y z -> f (ThreeN x y z))

withFourN :: Applicative f => f (DigitN l -> b) -> f (Node l -> Node l -> Node l -> Node l -> b)
withFourN = fmap (\f w x y z -> f (FourN w x y z))

otraverseDigitN :: Applicative f => f (DigitN l -> b) -> (Elem -> f Elem) -> DigitN l -> f b
otraverseDigitN k f d = case d of
  OneN x -> withOneN k <*> otraverseNode f x
  TwoN x y -> withTwoN k <*> otraverseNode f x <*> otraverseNode f y
  ThreeN x y z -> withThreeN k <*> otraverseNode f x <*> otraverseNode f y <*> otraverseNode f z
  FourN w x y z -> withFourN k <*> otraverseNode f w <*> otraverseNode f x <*> otraverseNode f y <*> otraverseNode f z

otraverseNode :: Applicative f => (Elem -> f Elem) -> Node l -> f (Node l)
otraverseNode f = \case
  Node_Leaf2 _ x y -> node2L <$> f x <*> f y
  Node_Leaf3 _ x y z -> node3L <$> f x <*> f y <*> f z
  Node_Branch2 _ x y -> node2N <$> otraverseNode f x <*> otraverseNode f y
  Node_Branch3 _ x y z -> node3N <$> otraverseNode f x <*> otraverseNode f y <*> otraverseNode f z

omapWithPos
  :: (Measure -> Elem -> Elem)
  -> FingerTree
  -> FingerTree
omapWithPos f = omapWithContext (\pr x _ -> f pr x)

omapWithContext
  :: (Measure -> Elem -> Measure -> Elem)
  -> FingerTree
  -> FingerTree
omapWithContext f = \case
  FingerTree_Empty -> FingerTree_Empty
  FingerTree_Single x -> FingerTree_Single (f mempty x mempty)
  FingerTree_Deep _ pr t sf ->
    let prm = measureDigitL pr
        tm = measureDeepTree t
        sfm = measureDigitL sf
     in deepL
       (omapWithContextDigitL mempty (tm <> sfm) f pr)
       (omapWithContextDeepTree prm sfm f t)
       (omapWithContextDigitL (prm <> tm) mempty f sf)

omapWithContextDigitL :: Measure -> Measure -> (Measure -> Elem -> Measure -> Elem) -> DigitL -> DigitL
omapWithContextDigitL m0 m1 f = \case
  OneL x -> OneL (f m0 x m1)
  TwoL x y ->
    let mx = measure x
        my = measure y
     in TwoL (f m0 x (my <> m1)) (f (m0 <> mx) y m1)
  ThreeL x y z ->
    let mx = measure x
        my = measure y
        mz = measure z
     in ThreeL (f m0 x (my <> mz <> m1)) (f (m0 <> mx) y (mz <> m1)) (f (m0 <> mx <> my) z m1)
  FourL w x y z ->
    let mw = measure w
        mx = measure x
        my = measure y
        mz = measure z
     in FourL
          (f m0 w (mx <> my <> mz <> m1))
          (f (m0 <> mw) x (my <> mz <> m1))
          (f (m0 <> mw <> mx) y (mz <> m1))
          (f (m0 <> mw <> mx <> my) z m1)

omapWithContextDeepTree :: Measure -> Measure -> (Measure -> Elem -> Measure -> Elem) -> DeepTree l -> DeepTree l
omapWithContextDeepTree m0 m1 f = \case
  DeepTree_Empty -> DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single (omapWithContextNode m0 m1 f x)
  DeepTree_Deep _ pr t sf ->
    let prm = measureDigitN pr
        tm = measureDeepTree t
        sfm = measureDigitN sf
     in deepN
       (omapWithContextDigitN m0 (tm <> sfm <> m1) f pr)
       (omapWithContextDeepTree (m0 <> prm) (sfm <> m1) f t)
       (omapWithContextDigitN (m0 <> prm <> tm) m1 f sf)

omapWithContextDigitN :: Measure -> Measure -> (Measure -> Elem -> Measure -> Elem) -> DigitN l -> DigitN l
omapWithContextDigitN m0 m1 f = \case
  OneN x -> OneN (omapWithContextNode m0 m1 f x)
  TwoN x y ->
    let mx = measureNode x
        my = measureNode y
     in TwoN (omapWithContextNode m0 (my <> m1) f x) (omapWithContextNode (m0 <> mx) m1 f y)
  ThreeN x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in ThreeN
          (omapWithContextNode m0 (my <> mz <> m1) f x)
          (omapWithContextNode (m0 <> mx) (mz <> m1) f y)
          (omapWithContextNode (m0 <> mx <> my) m1 f z)
  FourN w x y z ->
    let mw = measureNode w
        mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in FourN
          (omapWithContextNode m0 m1 f w)
          (omapWithContextNode (m0 <> mw) (my <> mz <> m1) f x)
          (omapWithContextNode (m0 <> mw <> mx) (mz <> m1) f y)
          (omapWithContextNode (m0 <> mw <> mx <> my) m1 f z)

omapWithContextNode :: Measure -> Measure -> (Measure -> Elem -> Measure -> Elem) -> Node l -> Node l
omapWithContextNode m0 m1 f = \case
  Node_Leaf2 _ x y ->
    let mx = measure x
        my = measure y
     in node2L (f m0 x (my <> m1)) (f (m0 <> mx) y m1)
  Node_Leaf3 _ x y z ->
    let mx = measure x
        my = measure y
        mz = measure z
     in node3L (f m0 x (my <> mz <> m1)) (f (m0 <> mx) y (mz <> m1)) (f (m0 <> mx <> my) z m1)
  Node_Branch2 _ x y ->
    let mx = measureNode x
        my = measureNode y
     in node2N (omapWithContextNode m0 (my <> m1) f x) (omapWithContextNode (m0 <> mx) m1 f y)
  Node_Branch3 _ x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in node3N
          (omapWithContextNode m0 (my <> mz <> m1) f x)
          (omapWithContextNode (m0 <> mx) (mz <> m1) f y)
          (omapWithContextNode (m0 <> mx <> my) m1 f z)

otraverseWithPos
  :: Applicative f
  => (Measure -> Elem -> f Elem)
  -> FingerTree
  -> f FingerTree
otraverseWithPos f = otraverseWithContext (\pr x _ -> f pr x)

otraverseWithContext
  :: Applicative f
  => (Measure -> Elem -> Measure -> f Elem)
  -> FingerTree
  -> f FingerTree
otraverseWithContext f = \case
  FingerTree_Empty -> pure FingerTree_Empty
  FingerTree_Single x -> FingerTree_Single <$> f mempty x mempty
  FingerTree_Deep _ pr t sf ->
    let mpr = measureDigitL pr
        mt = measureDeepTree t
        msf = measureDigitL sf
     in otraverseWithContextDigitL (mpr <> mt) mempty
          (otraverseWithContextDigitL mempty (mt <> msf) (pure deepL) f pr <*> otraverseWithContextDeepTree mpr msf f t) f sf

otraverseWithContextDigitL
  :: Applicative f
  => Measure
  -> Measure
  -> f (DigitL -> b)
  -> (Measure -> Elem -> Measure -> f Elem)
  -> DigitL
  -> f b
otraverseWithContextDigitL m0 m1 k f = \case
  OneL x -> withOneL k <*> f m0 x m1
  TwoL x y ->
    let mx = measure x
        my = measure y
     in withTwoL k <*> f m0 x (my <> m1) <*> f (m0 <> mx) y m1
  ThreeL x y z ->
    let mx = measure x
        my = measure y
        mz = measure z
     in withThreeL k
          <*> f m0 x (mx <> my <> m1)
          <*> f (m0 <> mx) y (mz <> m1)
          <*> f (m0 <> mx <> my) z m1
  FourL w x y z ->
   let mw = measure w
       mx = measure x
       my = measure y
       mz = measure z
    in withFourL k
         <*> f m0 w (mx <> my <> mz <> m1)
         <*> f (m0 <> mw) x (my <> mz <> m1)
         <*> f (m0 <> mw <> mx) y (mz <> m1)
         <*> f (m0 <> mw <> mx <> my) z m1

otraverseWithContextDeepTree
  :: Applicative f
  => Measure
  -> Measure
  -> (Measure -> Elem -> Measure -> f Elem)
  -> DeepTree l
  -> f (DeepTree l)
otraverseWithContextDeepTree m0 m1 f = \case
  DeepTree_Empty -> pure DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single <$> otraverseWithContextNode m0 m1 f x
  DeepTree_Deep _ pr t sf ->
    let mpr = measureDigitN pr
        mt = measureDeepTree t
        msf = measureDigitN sf
     in otraverseWithContextDigitN (m0 <> mpr <> mt) m1
          (otraverseWithContextDigitN m0 (mt <> msf <> m1) (pure deepN) f pr <*> otraverseWithContextDeepTree mpr msf f t) f sf

otraverseWithContextDigitN
  :: Applicative f
  => Measure
  -> Measure
  -> f (DigitN l -> b)
  -> (Measure -> Elem -> Measure -> f Elem)
  -> DigitN l
  -> f b
otraverseWithContextDigitN m0 m1 k f = \case
  OneN x -> withOneN k <*> otraverseWithContextNode m0 m1 f x
  TwoN x y ->
    let mx = measureNode x
        my = measureNode y
     in withTwoN k <*> otraverseWithContextNode m0 (my <> m1) f x <*> otraverseWithContextNode (m0 <> mx) m1 f y
  ThreeN x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in withThreeN k
          <*> otraverseWithContextNode m0 (mx <> my <> m1) f x
          <*> otraverseWithContextNode (m0 <> mx) (mz <> m1) f y
          <*> otraverseWithContextNode (m0 <> mx <> my) m1 f z
  FourN w x y z ->
   let mw = measureNode w
       mx = measureNode x
       my = measureNode y
       mz = measureNode z
    in withFourN k
         <*> otraverseWithContextNode m0 (mx <> my <> mz <> m1) f w
         <*> otraverseWithContextNode (m0 <> mw) (my <> mz <> m1) f x
         <*> otraverseWithContextNode (m0 <> mw <> mx) (mz <> m1) f y
         <*> otraverseWithContextNode (m0 <> mw <> mx <> my) m1 f z

otraverseWithContextNode
  :: Applicative f
  => Measure
  -> Measure
  ->(Measure -> Elem -> Measure -> f Elem)
  -> Node l
  -> f (Node l)
otraverseWithContextNode m0 m1 f = \case
  Node_Leaf2 _ x y ->
   let mx = measure x
       my = measure y
    in node2L <$> f m0 x (my <> m1) <*> f (m0 <> mx) y m1
  Node_Leaf3 _ x y z ->
   let mx = measure x
       my = measure y
       mz = measure z
    in node3L <$> f m0 x (my <> mz <> m1) <*> f (m0 <> mx) y (mz <> m1) <*> f (m0 <> mx <> my) z m1
  Node_Branch2 _ x y ->
   let mx = measureNode x
       my = measureNode y
    in node2N <$> otraverseWithContextNode m0 (my <> m1) f x <*> otraverseWithContextNode (m0 <> mx) m1 f y
  Node_Branch3 _ x y z ->
    let mx = measureNode x
        my = measureNode y
        mz = measureNode z
     in node3N
          <$> otraverseWithContextNode m0 (my <> mz <> m1) f x
          <*> otraverseWithContextNode (m0 <> mx) (mz <> m1) f y
          <*> otraverseWithContextNode (m0 <> mx <> my) m1 f z

----

empty :: FingerTree
empty = FingerTree_Empty

singleton :: Elem -> FingerTree
singleton = FingerTree_Single

fromList :: [Elem] -> FingerTree
fromList = foldr (<|) FingerTree_Empty

(<|) :: Elem -> FingerTree -> FingerTree
a <| t = case t of
  FingerTree_Empty -> FingerTree_Single a
  FingerTree_Single b -> deepL (OneL a) DeepTree_Empty (OneL b)
  FingerTree_Deep m (FourL b c d e) t' sf -> t' `seq` FingerTree_Deep
    (measure a <> m)
    (TwoL a b)
    (node3L c d e <<| t')
    sf
  FingerTree_Deep m pr t' sf -> FingerTree_Deep
    (measure a <> m)
    (consDigitL a pr)
    t'
    sf

(|>) :: FingerTree -> Elem -> FingerTree
t |> x = case t of
  FingerTree_Empty -> FingerTree_Single x
  FingerTree_Single a -> deepL (OneL a) DeepTree_Empty (OneL x)
  FingerTree_Deep m pr t' (FourL a b c d) -> t `seq` FingerTree_Deep
    (m <> measure x)
    pr
    (t' |>> node3L a b c) (TwoL d x)
  FingerTree_Deep m pr t' sf -> FingerTree_Deep
    (m <> measure x)
    pr
    t'
    (snocDigitL sf x)

(<<|) :: Node l -> DeepTree l -> DeepTree l
a <<| t = case t of
  DeepTree_Empty -> DeepTree_Single a
  DeepTree_Single b -> deepN (OneN a) DeepTree_Empty (OneN b)
  DeepTree_Deep m (FourN b c d e) t' sf -> t `seq` DeepTree_Deep
    (measureNode a <> m)
    (TwoN a b)
    (node3N c d e <<| t')
    sf
  DeepTree_Deep m pr t' sf -> DeepTree_Deep
    (measureNode a <> m)
    (consDigitN a pr)
    t'
    sf

(|>>) :: DeepTree l -> Node l -> DeepTree l
t |>> x = case t of
  DeepTree_Empty -> DeepTree_Single x
  DeepTree_Single a -> deepN (OneN a) DeepTree_Empty (OneN x)
  DeepTree_Deep m pr t' (FourN a b c d) -> DeepTree_Deep
    (m <> measureNode x)
    pr
    (t' |>> node3N a b c) (TwoN d x)
  DeepTree_Deep m pr t' sf -> DeepTree_Deep
    (m <> measureNode x)
    pr
    t'
    (snocDigitN sf x)

consDigitL :: Elem -> DigitL -> DigitL
consDigitL a = \case
  OneL b -> TwoL a b
  TwoL b c -> ThreeL a b c
  ThreeL b c d -> FourL a b c d
  FourL _ _ _ _ -> undefined

consDigitN :: Node l -> DigitN l -> DigitN l
consDigitN a = \case
  OneN b -> TwoN a b
  TwoN b c -> ThreeN a b c
  ThreeN b c d -> FourN a b c d
  FourN _ _ _ _ -> undefined

snocDigitL :: DigitL -> Elem -> DigitL
snocDigitL d x = case d of
  OneL a -> TwoL a x
  TwoL a b -> ThreeL a b x
  ThreeL a b c -> FourL a b c x
  FourL _ _ _ _ -> undefined

snocDigitN :: DigitN l -> Node l -> DigitN l
snocDigitN d x = case d of
  OneN a -> TwoN a x
  TwoN a b -> ThreeN a b x
  ThreeN a b c -> FourN a b c x
  FourN _ _ _ _ -> undefined

null :: FingerTree -> Bool
null = \case
  FingerTree_Empty -> True
  _ -> False

viewl :: FingerTree -> ViewL
viewl = \case
  FingerTree_Empty -> EmptyL
  FingerTree_Single x -> x :< FingerTree_Empty
  FingerTree_Deep _ (OneL x) t sf -> x :< rotLL t sf
  FingerTree_Deep _ pr t sf -> lheadDigitL pr :< deepL (ltailDigitL pr) t sf

viewNL :: DeepTree l -> ViewNL l
viewNL = \case
  DeepTree_Empty -> EmptyNL
  DeepTree_Single x -> x :<< DeepTree_Empty
  DeepTree_Deep _ (OneN x) t sf -> x :<< rotNL t sf
  DeepTree_Deep _ pr t sf -> lheadDigitN pr :<< deepN (ltailDigitN pr) t sf

rotLL :: DeepTree 'Level_Leaf -> DigitL -> FingerTree
rotLL t sf = case viewNL t of
  EmptyNL -> digitToTreeL sf
  a :<< t' -> FingerTree_Deep (measureDeepTree t <> measureDigitL sf) (nodeToDigitL a) t' sf

rotNL :: DeepTree ('Level_Branch l) -> DigitN l -> DeepTree l
rotNL t sf = case viewNL t of
  EmptyNL -> digitToTreeN sf
  a :<< t' -> DeepTree_Deep (measureDeepTree t <> measureDigitN sf) (nodeToDigitN a) t' sf

lheadDigitL :: DigitL -> Elem
lheadDigitL = \case
  (OneL a) -> a
  (TwoL a _) -> a
  (ThreeL a _ _) -> a
  (FourL a _ _ _) -> a

ltailDigitL :: DigitL -> DigitL
ltailDigitL = \case
  (OneL _) -> undefined
  (TwoL _ b) -> OneL b
  (ThreeL _ b c) -> TwoL b c
  (FourL _ b c d) -> ThreeL b c d

lheadDigitN :: DigitN l -> Node l
lheadDigitN = \case
  (OneN a) -> a
  (TwoN a _) -> a
  (ThreeN a _ _) -> a
  (FourN a _ _ _) -> a

ltailDigitN :: DigitN l -> DigitN l
ltailDigitN = \case
  (OneN _) -> undefined
  (TwoN _ b) -> OneN b
  (ThreeN _ b c) -> TwoN b c
  (FourN _ b c d) -> ThreeN b c d

viewr :: FingerTree -> ViewR
viewr = \case
  FingerTree_Empty -> EmptyR
  FingerTree_Single x -> FingerTree_Empty :> x
  FingerTree_Deep _ pr m (OneL x) -> rotLR pr m :> x
  FingerTree_Deep _ pr t sf -> deepL pr t (rtailDigitL sf) :> rheadDigitL sf

viewNR :: DeepTree l -> ViewNR l
viewNR = \case
  DeepTree_Empty -> EmptyNR
  DeepTree_Single x -> DeepTree_Empty :>> x
  DeepTree_Deep _ pr t (OneN x) -> rotNR pr t :>> x
  DeepTree_Deep _ pr t sf -> deepN pr t (rtailDigitN sf) :>> rheadDigitN sf

rotLR :: DigitL -> DeepTree 'Level_Leaf -> FingerTree
rotLR pr t = case viewNR t of
  EmptyNR -> digitToTreeL pr
  t' :>> a -> FingerTree_Deep
    (measureDigitL pr <> measureDeepTree t)
    pr
    t'
    (nodeToDigitL a)

rotNR :: DigitN l -> DeepTree ('Level_Branch l) -> DeepTree l
rotNR pr t = case viewNR t of
  EmptyNR -> digitToTreeN pr
  t' :>> a -> DeepTree_Deep
    (measureDigitN pr <> measureDeepTree t)
    pr
    t'
    (nodeToDigitN a)

rheadDigitL :: DigitL -> Elem
rheadDigitL = \case
  (OneL a) -> a
  (TwoL _ b) -> b
  (ThreeL _ _ c) -> c
  (FourL _ _ _ d) -> d

rtailDigitL :: DigitL -> DigitL
rtailDigitL = \case
  (OneL _) -> undefined
  (TwoL a _) -> OneL a
  (ThreeL a b _) -> TwoL a b
  (FourL a b c _) -> ThreeL a b c

rheadDigitN :: DigitN l -> Node l
rheadDigitN = \case
  (OneN a) -> a
  (TwoN _ b) -> b
  (ThreeN _ _ c) -> c
  (FourN _ _ _ d) -> d

rtailDigitN :: DigitN l -> DigitN l
rtailDigitN = \case
  (OneN _) -> undefined
  (TwoN a _) -> OneN a
  (ThreeN a b _) -> TwoN a b
  (FourN a b c _) -> ThreeN a b c

digitToTreeL :: DigitL -> FingerTree
digitToTreeL = \case
  OneL a -> FingerTree_Single a
  TwoL a b -> deepL (OneL a) DeepTree_Empty (OneL b)
  ThreeL a b c -> deepL (TwoL a b) DeepTree_Empty (OneL c)
  FourL a b c d -> deepL (TwoL a b) DeepTree_Empty (TwoL c d)

digitToTreeN :: DigitN l -> DeepTree l
digitToTreeN = \case
  OneN a -> DeepTree_Single a
  TwoN a b -> deepN (OneN a) DeepTree_Empty (OneN b)
  ThreeN a b c -> deepN (TwoN a b) DeepTree_Empty (OneN c)
  FourN a b c d -> deepN (TwoN a b) DeepTree_Empty (TwoN c d)

----------------
-- Concatenation
----------------

instance Semigroup FingerTree where
  (<>) = (><)

instance Monoid FingerTree where
  mempty = empty

-- | /O(log(min(n1,n2)))/. Concatenate two sequences.
(><) :: FingerTree -> FingerTree -> FingerTree
s >< t = case (s, t) of
  (FingerTree_Empty, x) -> x
  (x, FingerTree_Empty) -> x
  (FingerTree_Single x, xs) -> x <| xs
  (xs, FingerTree_Single x) -> xs |> x
  (FingerTree_Deep _ pr1 x1 sf1, FingerTree_Deep _ pr2 x2 sf2) ->
    deepL pr1 (addDigitsL0 x1 sf1 pr2 x2) sf2

addDigitsL0 :: DeepTree 'Level_Leaf -> DigitL -> DigitL -> DeepTree 'Level_Leaf -> DeepTree 'Level_Leaf
addDigitsL0 m1 (OneL a) (OneL b) m2 =
    appendTree1 m1 (node2L a b) m2
addDigitsL0 m1 (OneL a) (TwoL b c) m2 =
    appendTree1 m1 (node3L a b c) m2
addDigitsL0 m1 (OneL a) (ThreeL b c d) m2 =
    appendTree2 m1 (node2L a b) (node2L c d) m2
addDigitsL0 m1 (OneL a) (FourL b c d e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (TwoL a b) (OneL c) m2 =
    appendTree1 m1 (node3L a b c) m2
addDigitsL0 m1 (TwoL a b) (TwoL c d) m2 =
    appendTree2 m1 (node2L a b) (node2L c d) m2
addDigitsL0 m1 (TwoL a b) (ThreeL c d e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (TwoL a b) (FourL c d e f) m2 =
    appendTree2 m1 (node3L a b c) (node3L d e f) m2
addDigitsL0 m1 (ThreeL a b c) (OneL d) m2 =
    appendTree2 m1 (node2L a b) (node2L c d) m2
addDigitsL0 m1 (ThreeL a b c) (TwoL d e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (ThreeL a b c) (ThreeL d e f) m2 =
    appendTree2 m1 (node3L a b c) (node3L d e f) m2
addDigitsL0 m1 (ThreeL a b c) (FourL d e f g) m2 =
    appendTree3 m1 (node3L a b c) (node2L d e) (node2L f g) m2
addDigitsL0 m1 (FourL a b c d) (OneL e) m2 =
    appendTree2 m1 (node3L a b c) (node2L d e) m2
addDigitsL0 m1 (FourL a b c d) (TwoL e f) m2 =
    appendTree2 m1 (node3L a b c) (node3L d e f) m2
addDigitsL0 m1 (FourL a b c d) (ThreeL e f g) m2 =
    appendTree3 m1 (node3L a b c) (node2L d e) (node2L f g) m2
addDigitsL0 m1 (FourL a b c d) (FourL e f g h) m2 =
    appendTree3 m1 (node3L a b c) (node3L d e f) (node2L g h) m2

appendTree1 :: DeepTree l -> Node l -> DeepTree l -> DeepTree l
appendTree1 DeepTree_Empty a xs =
    a <<| xs
appendTree1 xs a DeepTree_Empty =
    xs |>> a
appendTree1 (DeepTree_Single x) a xs =
    x <<| a <<| xs
appendTree1 xs a (DeepTree_Single x) =
    xs |>> a |>> x
appendTree1 (DeepTree_Deep _ pr1 m1 sf1) a (DeepTree_Deep _ pr2 m2 sf2) =
    deepN pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

addDigits1 :: DeepTree ('Level_Branch l) -> DigitN l -> Node l -> DigitN l -> DeepTree ('Level_Branch l) -> DeepTree ('Level_Branch l)
addDigits1 m1 (OneN a) b (OneN c) m2 =
    appendTree1 m1 (node3N a b c) m2
addDigits1 m1 (OneN a) b (TwoN c d) m2 =
    appendTree2 m1 (node2N a b) (node2N c d) m2
addDigits1 m1 (OneN a) b (ThreeN c d e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits1 m1 (OneN a) b (FourN c d e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (TwoN a b) c (OneN d) m2 =
    appendTree2 m1 (node2N a b) (node2N c d) m2
addDigits1 m1 (TwoN a b) c (TwoN d e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits1 m1 (TwoN a b) c (ThreeN d e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (TwoN a b) c (FourN d e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits1 m1 (ThreeN a b c) d (OneN e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits1 m1 (ThreeN a b c) d (TwoN e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (ThreeN a b c) d (ThreeN e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits1 m1 (ThreeN a b c) d (FourN e f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits1 m1 (FourN a b c d) e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits1 m1 (FourN a b c d) e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits1 m1 (FourN a b c d) e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits1 m1 (FourN a b c d) e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2

appendTree2 :: DeepTree l -> Node l -> Node l -> DeepTree l -> DeepTree l
appendTree2 DeepTree_Empty a b xs =
    a <<| b <<| xs
appendTree2 xs a b DeepTree_Empty =
    xs |>> a |>> b
appendTree2 (DeepTree_Single x) a b xs =
    x <<| a <<| b <<| xs
appendTree2 xs a b (DeepTree_Single x) =
    xs |>> a |>> b |>> x
appendTree2 (DeepTree_Deep _ pr1 m1 sf1) a b (DeepTree_Deep _ pr2 m2 sf2) =
    deepN pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

addDigits2 :: DeepTree ('Level_Branch l) -> DigitN l -> Node l -> Node l -> DigitN l -> DeepTree ('Level_Branch l) -> DeepTree ('Level_Branch l)
addDigits2 m1 (OneN a) b c (OneN d) m2 =
    appendTree2 m1 (node2N a b) (node2N c d) m2
addDigits2 m1 (OneN a) b c (TwoN d e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits2 m1 (OneN a) b c (ThreeN d e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits2 m1 (OneN a) b c (FourN d e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (TwoN a b) c d (OneN e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits2 m1 (TwoN a b) c d (TwoN e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits2 m1 (TwoN a b) c d (ThreeN e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (TwoN a b) c d (FourN e f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits2 m1 (ThreeN a b c) d e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits2 m1 (ThreeN a b c) d e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (ThreeN a b c) d e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits2 m1 (ThreeN a b c) d e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits2 m1 (FourN a b c d) e f (OneN g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits2 m1 (FourN a b c d) e f (TwoN g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits2 m1 (FourN a b c d) e f (ThreeN g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits2 m1 (FourN a b c d) e f (FourN g h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2

appendTree3 :: DeepTree l -> Node l -> Node l -> Node l -> DeepTree l -> DeepTree l
appendTree3 DeepTree_Empty a b c xs =
    a <<| b <<| c <<| xs
appendTree3 xs a b c DeepTree_Empty =
    xs |>> a |>> b |>> c
appendTree3 (DeepTree_Single x) a b c xs =
    x <<| a <<| b <<| c <<| xs
appendTree3 xs a b c (DeepTree_Single x) =
    xs |>> a |>> b |>> c |>> x
appendTree3 (DeepTree_Deep _ pr1 m1 sf1) a b c (DeepTree_Deep _ pr2 m2 sf2) =
    deepN pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

addDigits3 :: DeepTree ('Level_Branch l) -> DigitN l -> Node l -> Node l -> Node l -> DigitN l -> DeepTree ('Level_Branch l) -> DeepTree ('Level_Branch l)
addDigits3 m1 (OneN a) b c d (OneN e) m2 =
    appendTree2 m1 (node3N a b c) (node2N d e) m2
addDigits3 m1 (OneN a) b c d (TwoN e f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits3 m1 (OneN a) b c d (ThreeN e f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits3 m1 (OneN a) b c d (FourN e f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (TwoN a b) c d e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits3 m1 (TwoN a b) c d e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits3 m1 (TwoN a b) c d e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (TwoN a b) c d e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits3 m1 (ThreeN a b c) d e f (OneN g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits3 m1 (ThreeN a b c) d e f (TwoN g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (ThreeN a b c) d e f (ThreeN g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits3 m1 (ThreeN a b c) d e f (FourN g h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits3 m1 (FourN a b c d) e f g (OneN h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits3 m1 (FourN a b c d) e f g (TwoN h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits3 m1 (FourN a b c d) e f g (ThreeN h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits3 m1 (FourN a b c d) e f g (FourN h i j k) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node2N j k) m2

appendTree4 :: DeepTree l -> Node l -> Node l -> Node l -> Node l -> DeepTree l -> DeepTree l
appendTree4 DeepTree_Empty a b c d xs =
    a <<| b <<| c <<| d <<| xs
appendTree4 xs a b c d DeepTree_Empty =
    xs |>> a |>> b |>> c |>> d
appendTree4 (DeepTree_Single x) a b c d xs =
    x <<| a <<| b <<| c <<| d <<| xs
appendTree4 xs a b c d (DeepTree_Single x) =
    xs |>> a |>> b |>> c |>> d |>> x
appendTree4 (DeepTree_Deep _ pr1 m1 sf1) a b c d (DeepTree_Deep _ pr2 m2 sf2) =
    deepN pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

addDigits4 :: DeepTree ('Level_Branch l) -> DigitN l -> Node l -> Node l -> Node l -> Node l -> DigitN l -> DeepTree ('Level_Branch l) -> DeepTree ('Level_Branch l)
addDigits4 m1 (OneN a) b c d e (OneN f) m2 =
    appendTree2 m1 (node3N a b c) (node3N d e f) m2
addDigits4 m1 (OneN a) b c d e (TwoN f g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits4 m1 (OneN a) b c d e (ThreeN f g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits4 m1 (OneN a) b c d e (FourN f g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (TwoN a b) c d e f (OneN g) m2 =
    appendTree3 m1 (node3N a b c) (node2N d e) (node2N f g) m2
addDigits4 m1 (TwoN a b) c d e f (TwoN g h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits4 m1 (TwoN a b) c d e f (ThreeN g h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (TwoN a b) c d e f (FourN g h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits4 m1 (ThreeN a b c) d e f g (OneN h) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node2N g h) m2
addDigits4 m1 (ThreeN a b c) d e f g (TwoN h i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (ThreeN a b c) d e f g (ThreeN h i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits4 m1 (ThreeN a b c) d e f g (FourN h i j k) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node2N j k) m2
addDigits4 m1 (FourN a b c d) e f g h (OneN i) m2 =
    appendTree3 m1 (node3N a b c) (node3N d e f) (node3N g h i) m2
addDigits4 m1 (FourN a b c d) e f g h (TwoN i j) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node2N g h) (node2N i j) m2
addDigits4 m1 (FourN a b c d) e f g h (ThreeN i j k) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node2N j k) m2
addDigits4 m1 (FourN a b c d) e f g h (FourN i j k l) m2 =
    appendTree4 m1 (node3N a b c) (node3N d e f) (node3N g h i) (node3N j k l) m2
----------------
-- 4.4 Splitting
----------------

data MaybeDigitN l = NothingN | JustN (DigitN l)
data MaybeDigitL = NothingL | JustL DigitL

data Split t a = Split t a t

-- | A result of 'search', attempting to find a point where a predicate
-- on splits of the sequence changes from 'False' to 'True'.
data SearchResult
    = Position FingerTree Elem FingerTree
        -- ^ A tree opened at a particular element: the prefix to the
        -- left, the element, and the suffix to the right.
    | OnLeft
        -- ^ A position to the left of the sequence, indicating that the
        -- predicate is 'True' at both ends.
    | OnRight
        -- ^ A position to the right of the sequence, indicating that the
        -- predicate is 'False' at both ends.
    | Nowhere
        -- ^ No position in the tree, returned if the predicate is 'True'
        -- at the left end and 'False' at the right end.  This will not
        -- occur if the predicate in monotonic on the tree.
  deriving Generic

deriving instance (Eq Elem, Eq Measure) => Eq SearchResult
deriving instance (Ord Elem, Ord Measure) => Ord SearchResult

-- | /O(log(min(i,n-i)))/. Search a sequence for a point where a predicate
-- on splits of the sequence changes from 'False' to 'True'.
--
-- The argument @p@ is a relation between the measures of the two
-- sequences that could be appended together to form the sequence @t@.
-- If the relation is 'False' at the leftmost split and 'True' at the
-- rightmost split, i.e.
--
-- @not (p 'mempty' ('measure' t)) && p ('measure' t) 'mempty'@
--
-- then there must exist an element @x@ in the sequence such that @p@
-- is 'False' for the split immediately before @x@ and 'True' for the
-- split just after it:
--
-- In this situation, @'search' p t@ returns such an element @x@ and the
-- pieces @l@ and @r@ of the sequence to its left and right respectively.
-- That is, it returns @'Position' l x r@ such that
--
-- * @l >< (x <| r) = t@
--
-- * @not (p (measure l) (measure (x <| r))@
--
-- * @p (measure (l |> x)) (measure r)@
--
-- For predictable results, one should ensure that there is only one such
-- point, i.e. that the predicate is /monotonic/ on @t@.
search
  :: (Measure -> Measure -> Bool)
  -> FingerTree
  -> SearchResult
search p t
  | p_left && p_right = OnLeft
  | not p_left && p_right = case searchTree p mempty t mempty of
        Split l x r -> Position l x r
  | not p_left && not p_right = OnRight
  | otherwise = Nowhere
  where
    p_left = p mempty vt
    p_right = p vt mempty
    vt = measureFingerTree t

searchTree
  :: (Measure -> Measure -> Bool)
  -> Measure
  -> FingerTree
  -> Measure
  -> Split FingerTree Elem
searchTree p vl t vr = case t of
  FingerTree_Empty -> illegal_argument "searchTree"
  FingerTree_Single x -> Split FingerTree_Empty x FingerTree_Empty
  FingerTree_Deep _ pr m sf
    | p vlp vmsr
    -> let Split l x r = searchDigitL p vl pr vmsr
           l' = case l of
             NothingL -> FingerTree_Empty
             JustL lx -> digitToTreeL lx
        in Split l' x (deepLL r m sf)
    | p vlpm vsr
    -> let Split ml xs mr = searchDeepTree p vlp m vsr
           Split l x r = searchLeaf p (vlp <> measureDeepTree ml) xs (measureDeepTree mr <> vsr)
        in Split (deepLR pr ml l) x (deepLL r mr sf)
    | otherwise
    -> let Split l x r = searchDigitL p vlpm sf vr
           r' = case r of
             NothingL -> FingerTree_Empty
             JustL rx -> digitToTreeL rx
        in Split (deepLR pr m l) x r'
    where
      vlp = vl <> measureDigitL pr
      vlpm = vlp <> vm
      vmsr = vm <> vsr
      vsr = measureDigitL sf <> vr
      vm = measureDeepTree m

searchDeepTree
  :: (Measure -> Measure -> Bool)
  -> Measure
  -> DeepTree l
  -> Measure
  -> Split (DeepTree l) (Node l)
searchDeepTree p vl t vr = case t of
  DeepTree_Empty -> illegal_argument "searchTree"
  DeepTree_Single x -> Split DeepTree_Empty x DeepTree_Empty
  DeepTree_Deep _ pr m sf
    | p vlp vmsr
    -> let Split l x r = searchDigitN p vl pr vmsr
           l' = case l of
             NothingN -> DeepTree_Empty
             JustN lx -> digitToTreeN lx
        in Split l' x (deepNL r m sf)
    | p vlpm vsr
    -> let Split ml xs mr = searchDeepTree p vlp m vsr
           Split l x r = searchNode p (vlp <> measureDeepTree ml) xs (measureDeepTree mr <> vsr)
        in Split (deepNR pr ml l) x (deepNL r mr sf)
    | otherwise
    -> let Split l x r = searchDigitN p vlpm sf vr
           r' = case r of
             NothingN -> DeepTree_Empty
             JustN rx -> digitToTreeN rx
        in Split (deepNR pr m l) x r'
    where
      vlp = vl <> measureDigitN pr
      vlpm = vlp <> vm
      vmsr = vm <> vsr
      vsr = measureDigitN sf <> vr
      vm = measureDeepTree m

searchLeaf
  :: (Measure -> Measure -> Bool)
  -> Measure
  -> Node 'Level_Leaf
  -> Measure
  -> Split MaybeDigitL Elem
searchLeaf p vl n vr = case n of
  Node_Leaf2 _ a b
    | p va vb
    -> Split NothingL a (JustL (OneL b))
    | otherwise
    -> Split (JustL (OneL a)) b NothingL
    where
      va = vl <> measure a
      vb = measure b <> vr
  Node_Leaf3 _ a b c
    | p va vbc
    -> Split NothingL a (JustL (TwoL b c))
    | p vab vc
    -> Split (JustL (OneL a)) b (JustL (OneL c))
    | otherwise
    -> Split (JustL (TwoL a b)) c NothingL
    where
      va = vl <> measure a
      vab = va <> measure b
      vc = measure c <> vr
      vbc = measure b <> vc

searchNode
  :: (Measure -> Measure -> Bool)
  -> Measure
  -> Node ('Level_Branch l)
  -> Measure
  -> Split (MaybeDigitN l) (Node l)
searchNode p vl n vr = case n of
  Node_Branch2 _ a b
    | p va vb
    -> Split NothingN a (JustN (OneN b))
    | otherwise
    -> Split (JustN (OneN a)) b NothingN
    where
      va = vl <> measureNode a
      vb = measureNode b <> vr
  Node_Branch3 _ a b c
    | p va vbc
    -> Split NothingN a (JustN (TwoN b c))
    | p vab vc
    -> Split (JustN (OneN a)) b (JustN (OneN c))
    | otherwise
    -> Split (JustN (TwoN a b)) c NothingN
    where
      va = vl <> measureNode a
      vab = va <> measureNode b
      vc = measureNode c <> vr
      vbc = measureNode b <> vc

searchDigitL
  :: (Measure -> Measure -> Bool)
  -> Measure
  -> DigitL
  -> Measure
  -> Split MaybeDigitL Elem
searchDigitL p vl d' vr = case d' of
  OneL a -> vl `seq` vr `seq` Split NothingL a NothingL
  TwoL a b
    | p va vb
    -> Split NothingL a (JustL (OneL b))
    | otherwise
    -> Split (JustL (OneL a)) b NothingL
    where
     va = vl <> measure a
     vb = measure b <> vr
  ThreeL a b c
    | p va vbc
    -> Split NothingL a (JustL (TwoL b c))
    | p vab vc
    -> Split (JustL (OneL a)) b (JustL (OneL c))
    | otherwise
    -> Split (JustL (TwoL a b)) c NothingL
    where
     va = vl <> measure a
     vab = va <> measure b
     vc = measure c <> vr
     vbc = measure b <> vc
  FourL a b c d
    | p va vbcd
    -> Split NothingL a (JustL (ThreeL b c d))
    | p vab vcd
    -> Split (JustL (OneL a)) b (JustL (TwoL c d))
    | p vabc vd
    -> Split (JustL (TwoL a b)) c (JustL (OneL d))
    | otherwise
    -> Split (JustL (ThreeL a b c)) d NothingL
    where
     va = vl <> measure a
     vab = va <> measure b
     vabc = vab <> measure c
     vd = measure d <> vr
     vcd = measure c <> vd
     vbcd = measure b <> vcd

searchDigitN
  :: (Measure -> Measure -> Bool)
  -> Measure
  -> DigitN l
  -> Measure
  -> Split (MaybeDigitN l) (Node l)
searchDigitN p vl d' vr = case d' of
  OneN a -> vl `seq` vr `seq` Split NothingN a NothingN
  TwoN a b
    | p va vb
    -> Split NothingN a (JustN (OneN b))
    | otherwise
    -> Split (JustN (OneN a)) b NothingN
    where
     va = vl <> measureNode a
     vb = measureNode b <> vr
  ThreeN a b c
    | p va vbc
    -> Split NothingN a (JustN (TwoN b c))
    | p vab vc
    -> Split (JustN (OneN a)) b (JustN (OneN c))
    | otherwise
    -> Split (JustN (TwoN a b)) c NothingN
    where
     va = vl <> measureNode a
     vab = va <> measureNode b
     vc = measureNode c <> vr
     vbc = measureNode b <> vc
  FourN a b c d
    | p va vbcd
    -> Split NothingN a (JustN (ThreeN b c d))
    | p vab vcd
    -> Split (JustN (OneN a)) b (JustN (TwoN c d))
    | p vabc vd
    -> Split (JustN (TwoN a b)) c (JustN (OneN d))
    | otherwise
    -> Split (JustN (ThreeN a b c)) d NothingN
    where
     va = vl <> measureNode a
     vab = va <> measureNode b
     vabc = vab <> measureNode c
     vd = measureNode d <> vr
     vcd = measureNode c <> vd
     vbcd = measureNode b <> vcd

-- | /O(log(min(i,n-i)))/. Split a sequence at a point where the predicate
-- on the accumulated measure of the prefix changes from 'False' to 'True'.
--
-- For predictable results, one should ensure that there is only one such
-- point, i.e. that the predicate is /monotonic/.
split :: (Measure -> Bool) -> FingerTree -> (FingerTree, FingerTree)
split _ FingerTree_Empty = (FingerTree_Empty, FingerTree_Empty)
split p xs
  | p (measureFingerTree xs) = (l, x <| r)
  | otherwise = (xs, FingerTree_Empty)
  where
    Split l x r = splitTree p mempty xs

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'takeUntil' p t@ is the largest
-- prefix of @t@ whose measure does not satisfy @p@.
--
-- *  @'takeUntil' p t = 'fst' ('split' p t)@
takeUntil :: (Measure -> Bool) -> FingerTree -> FingerTree
takeUntil p  =  fst . split p

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'dropUntil' p t@ is the rest of @t@
-- after removing the largest prefix whose measure does not satisfy @p@.
--
-- * @'dropUntil' p t = 'snd' ('split' p t)@
dropUntil :: (Measure -> Bool) -> FingerTree -> FingerTree
dropUntil p =  snd . split p

splitTree :: (Measure -> Bool) -> Measure -> FingerTree -> Split FingerTree Elem
splitTree p i = \case
  FingerTree_Empty -> illegal_argument "splitTree"
  FingerTree_Single x -> Split FingerTree_Empty x FingerTree_Empty
  FingerTree_Deep _ pr m sf
    | p vpr
    -> let Split l x r = splitDigitL p i pr
           l' = case l of
             NothingL -> FingerTree_Empty
             JustL lx -> digitToTreeL lx
        in Split l' x (deepLL r m sf)
    | p vm
    -> let Split ml xs mr = splitDeepTree p vpr m
           Split l x r = splitLeaf p (vpr <> measureDeepTree ml) xs
        in Split (deepLR pr ml l) x (deepLL r mr sf)
    | otherwise
    -> let Split l x r = splitDigitL p vm sf
           r' = case r of
             NothingL -> FingerTree_Empty
             JustL rx -> digitToTreeL rx
        in Split (deepLR pr m l) x r'
    where
      vpr = i <> measureDigitL pr
      vm = vpr <> measureDeepTree m

splitDeepTree :: (Measure -> Bool) -> Measure -> DeepTree l -> Split (DeepTree l) (Node l)
splitDeepTree p i = \case
  DeepTree_Empty -> illegal_argument "splitDeepTree"
  DeepTree_Single x -> Split DeepTree_Empty x DeepTree_Empty
  DeepTree_Deep _ pr m sf
    | p vpr
    -> let Split l x r = splitDigitN p i pr
           l' = case l of
             NothingN -> DeepTree_Empty
             JustN lx -> digitToTreeN lx
        in Split l' x (deepNL r m sf)
    | p vm
    -> let Split ml xs mr = splitDeepTree p vpr m
           Split l x r =  splitNode p (vpr <> measureDeepTree ml) xs
        in Split (deepNR pr ml l) x (deepNL r mr sf)
    | otherwise
    -> let Split l x r = splitDigitN p vm sf
           r' = case r of
             NothingN -> DeepTree_Empty
             JustN rx -> digitToTreeN rx
        in Split (deepNR pr m l) x r'
    where
      vpr = i <> measureDigitN pr
      vm = vpr <> measureDeepTree m

deepLL :: MaybeDigitL -> DeepTree 'Level_Leaf -> DigitL -> FingerTree
deepLL mpr m sf = case mpr of
  NothingL -> rotLL m sf
  JustL pr -> deepL pr m sf

deepNL :: MaybeDigitN l -> DeepTree ('Level_Branch l) -> DigitN l -> DeepTree l
deepNL mpr m sf = case mpr of
  NothingN -> rotNL m sf
  JustN pr -> deepN pr m sf

deepLR :: DigitL -> DeepTree 'Level_Leaf -> MaybeDigitL -> FingerTree
deepLR pr m = \case
  NothingL -> rotLR pr m
  JustL sf -> deepL pr m sf

deepNR :: DigitN l -> DeepTree ('Level_Branch l) -> MaybeDigitN l -> DeepTree l
deepNR pr m = \case
  NothingN -> rotNR pr m
  JustN sf -> deepN pr m sf

splitLeaf :: (Measure -> Bool) -> Measure -> Node 'Level_Leaf -> Split MaybeDigitL Elem
splitLeaf p i = \case
  (Node_Leaf2 _ a b)
    | p (i <> measure a)
    -> Split NothingL a (JustL (OneL b))
    | otherwise
    -> Split (JustL (OneL a)) b NothingL
  (Node_Leaf3 _ a b c)
    | p (i <> measure a)
    -> Split NothingL a (JustL (TwoL b c))
    | p (i <> measure a <> measure b)
    -> Split (JustL (OneL a)) b (JustL (OneL c))
    | otherwise
    ->Split (JustL (TwoL a b)) c NothingL

splitNode :: (Measure -> Bool) -> Measure -> Node ('Level_Branch l) -> Split (MaybeDigitN l) (Node l)
splitNode p i = \case
  (Node_Branch2 _ a b)
    | p (i <> measureNode a)
    -> Split NothingN a (JustN (OneN b))
    | otherwise
    -> Split (JustN (OneN a)) b NothingN
  (Node_Branch3 _ a b c)
    | p (i <> measureNode a)
    -> Split NothingN a (JustN (TwoN b c))
    | p (i <> measureNode a <> measureNode b)
    -> Split (JustN (OneN a)) b (JustN (OneN c))
    | otherwise
    ->Split (JustN (TwoN a b)) c NothingN

splitDigitL :: (Measure -> Bool) -> Measure -> DigitL -> Split MaybeDigitL Elem
splitDigitL p i = \case
  OneL a -> i `seq` Split NothingL a NothingL
  TwoL a b
    | p (i <> measure a)
    -> Split NothingL a (JustL (OneL b))
    | otherwise
    -> Split (JustL (OneL a)) b NothingL
  ThreeL a b c
    | p (i <> measure a)
    -> Split NothingL a (JustL (TwoL b c))
    | p (i <> measure a <> measure b)
    -> Split (JustL (OneL a)) b (JustL (OneL c))
    | otherwise
    -> Split (JustL (TwoL a b)) c NothingL
  FourL a b c d
    | p (i <> measure a)
    -> Split NothingL a (JustL (ThreeL b c d))
    | p (i <> measure a <> measure b)
    -> Split (JustL (OneL a)) b (JustL (TwoL c d))
    | p (i <> measure a <> measure b <> measure c)
    -> Split (JustL (TwoL a b)) c (JustL (OneL d))
    | otherwise
    -> Split (JustL (ThreeL a b c)) d NothingL

splitDigitN :: (Measure -> Bool) -> Measure -> DigitN l -> Split (MaybeDigitN l) (Node l)
splitDigitN p i = \case
  OneN a -> i `seq` Split NothingN a NothingN
  TwoN a b
    | p (i <> measureNode a)
    -> Split NothingN a (JustN (OneN b))
    | otherwise
    -> Split (JustN (OneN a)) b NothingN
  ThreeN a b c
    | p (i <> measureNode a)
    -> Split NothingN a (JustN (TwoN b c))
    | p (i <> measureNode a <> measureNode b)
    -> Split (JustN (OneN a)) b (JustN (OneN c))
    | otherwise
    -> Split (JustN (TwoN a b)) c NothingN
  FourN a b c d
    | p (i <> measureNode a)
    -> Split NothingN a (JustN (ThreeN b c d))
    | p (i <> measureNode a <> measureNode b)
    -> Split (JustN (OneN a)) b (JustN (TwoN c d))
    | p (i <> measureNode a <> measureNode b <> measureNode c)
    -> Split (JustN (TwoN a b)) c (JustN (OneN d))
    | otherwise
    -> Split (JustN (ThreeN a b c)) d NothingN

------------------
-- Transformations
------------------

reverse :: FingerTree -> FingerTree
reverse = \case
  FingerTree_Empty -> FingerTree_Empty
  FingerTree_Single x -> FingerTree_Single x
  FingerTree_Deep _ pr t sf -> deepL
    (reverseDigitL sf)
    (reverseDeep reverseLeaf t)
    (reverseDigitL pr)

-- | /O(n)/. The reverse of a sequence.
reverseDeep :: (Node l -> Node l) -> DeepTree l -> DeepTree l
reverseDeep f = \case
  DeepTree_Empty -> DeepTree_Empty
  DeepTree_Single x -> DeepTree_Single x
  DeepTree_Deep _ pr t sf -> deepN
    (reverseDigitN f sf)
    (reverseDeep (reverseNode f) t)
    (reverseDigitN f pr)

reverseDigitL :: DigitL -> DigitL
reverseDigitL = \case
  OneL x -> OneL x
  TwoL x y -> TwoL y x
  ThreeL x y z -> ThreeL z y x
  FourL w x y z -> FourL z y x w

reverseDigitN :: (Node l -> Node l) -> DigitN l -> DigitN l
reverseDigitN f = \case
  OneN x -> OneN (f x)
  TwoN x y -> TwoN (f y) (f x)
  ThreeN x y z -> ThreeN (f z) (f y) (f x)
  FourN w x y z -> FourN (f z) (f y) (f x) (f w)

reverseNode :: (Node l -> Node l) -> Node ('Level_Branch l) -> Node ('Level_Branch l)
reverseNode f = \case
  Node_Branch2 _ a b -> node2N (f b) (f a)
  Node_Branch3 _ a b c -> node3N (f c) (f b) (f a)

reverseLeaf :: Node 'Level_Leaf -> Node 'Level_Leaf
reverseLeaf = \case
  Node_Leaf2 _ a b -> node2L b a
  Node_Leaf3 _ a b c -> node3L c b a

illegal_argument :: String -> a
illegal_argument name =
    error $ "Logic error: " ++ name ++ " called with illegal argument"

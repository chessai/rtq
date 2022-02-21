{-# language
    BangPatterns
  , DeriveGeneric
  , DeriveTraversable
  , DerivingStrategies
  , GADTs
  , GeneralisedNewtypeDeriving
  , InstanceSigs
  , LambdaCase
  , ImportQualifiedPost
  , MagicHash
  , PackageImports
  , RankNTypes
  , RoleAnnotations
  , ScopedTypeVariables
#-}

{-# options_ghc -Wall #-}

module Rtq.Internal
  ( Queue(..)
  , empty
  , singleton
  , push
  , pop
  , head
  , size
  , Rtq.Internal.map
  , fromList
  , toList
  )
  where

import "base" Control.Monad.ST (ST, runST)
import "base" Control.Monad.ST.Unsafe (unsafeInterleaveST)
import "base" Data.Coerce (coerce)
import "base" Data.List qualified as List
import "base" Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)
import "base" GHC.Generics (Generic)
import "base" Prelude hiding (head, map)
import "base" Text.Read (ReadPrec, Lexeme(Ident), readPrec, readListPrec, readListPrecDefault, parens, prec, lexP)

data Queue a = Queue !Int [a] !Int !(SpineStrictList a) !Progress
  deriving stock (Generic)
  deriving stock (Traversable)
type role Queue representational

instance (Eq a) => Eq (Queue a) where
  (==) :: Queue a -> Queue a -> Bool
  Queue f1 xs1 r1 ys1 _p1 == Queue f2 xs2 r2 ys2 _p2
    -- i wish we could do some parallel execution here
    | f1 == f2 && r1 == r2 = xs1 == xs2 && ys1 == ys2
    | otherwise = False
  {-# inline (==) #-}

instance (Show a) => Show (Queue a) where
  showsPrec :: Int -> Queue a -> ShowS
  showsPrec p q = showParen (p > appPrec) $ showString "fromList " . shows (toList q)

instance (Read a) => Read (Queue a) where
  readPrec :: ReadPrec (Queue a)
  readPrec = parens $ prec appPrec $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    pure (fromList xs)

  readListPrec :: ReadPrec [Queue a]
  readListPrec = readListPrecDefault

instance Functor Queue where
  fmap = Rtq.Internal.map
  {-# inline fmap #-}

instance Foldable Queue where
  foldMap k (Queue _ xs _ ys _) = foldMap k xs <> foldMap k ys
  {-# inline foldMap #-}

empty :: Queue a
empty = Queue 0 [] 0 Nil Done
{-# inline empty #-}

singleton :: a -> Queue a
singleton x = Queue 1 [x] 0 Nil (NotYet Done)
{-# inline singleton #-}

push :: a -> Queue a -> Queue a
push a (Queue f xs r ys p) = invariant (Queue f xs (r + 1) (Cons a ys) (step p))
{-# inline push #-}

pop :: Queue a -> Maybe (a, Queue a)
pop (Queue f xs r ys p) = case xs of
  (a : as) -> Just (a, invariant (Queue (f - 1) as r ys (step p)))
  []       -> Nothing
{-# inline pop #-}

head :: Queue a -> Maybe a
head (Queue _ xs _ _ _) = case xs of
  [] -> Nothing
  (x : _) -> Just x
{-# inline head #-}

size :: Queue a -> Int
size (Queue f _ r _ _) = f + r
{-# inline size #-}

map :: (a -> b) -> Queue a -> Queue b
map m (Queue f xs r ys p) = Queue f (List.map m xs) r (fmap m ys) p
{-# noinline [0] map #-}

--traverse :: (Applicative f) => (a -> f b) -> Queue a -> f (Queue b)
--traverse m (Queue f xs r ys p) =
fromList :: [a] -> Queue a
fromList = List.foldl' (flip push) empty
{-# inline [0] fromList #-}

toList :: Queue a -> [a]
toList q1 = case pop q1 of
  Just (x, q2) -> x : toList q2
  Nothing -> []
{-# inline [0] toList #-}

invariant :: Queue a -> Queue a
invariant q@(Queue f xs1 r ys1 _)
  | f < r =
      let (ys2, p1) = runDelay (delayReverse ys1)
          xs2       = xs1 ++ ys2
          p2        = forceSpine f xs2
      in Queue (f + r) xs2 0 Nil (parProgress p1 p2)
  | otherwise = q

data Progress = Done | NotYet Progress
  deriving stock (Show)

step :: Progress -> Progress
step = \case
  Done     -> Done
  NotYet p -> p

parProgress :: Progress -> Progress -> Progress
parProgress !p          Done        = p
parProgress Done        !p          = p
parProgress (NotYet p1) (NotYet p2) = NotYet (parProgress p1 p2)

data SpineStrictList a = Nil | Cons a !(SpineStrictList a)
  deriving stock (Eq, Show)
  deriving stock (Functor, Foldable, Traversable)

forceSpine :: Int -> [a] -> Progress
forceSpine 0 _        = Done
forceSpine _ []       = Done
forceSpine n (_ : xs) = NotYet (forceSpine (n - 1) xs)

data Delay a = Now a | Later (Delay a)

delayReverse :: SpineStrictList a -> Delay [a]
delayReverse = go []
  where
    go acc = \case
      Nil       -> Now acc
      Cons x xs -> Later (go (x : acc) xs)

runDelay :: Delay a -> (a, Progress)
runDelay = \xs -> runST $ do
  r <- newSTRef xs
  x <- unsafeInterleaveST (readSTRef r)
  p <- next r
  pure (runNow x, p)
  where
    next :: STRef s (Delay a) -> ST s Progress
    next r = do
      xs <- readSTRef r
      case xs of
        Now   _ -> do
          pure Done
        Later d -> do
          writeSTRef r d
          p <- next r
          pure (NotYet p)

    runNow :: Delay a -> a
    runNow = \case
      Now   a -> a
      Later d -> runNow d

-- for Show/Read instances
appPrec :: Int
appPrec = 10

-- Commented out for now: fusion might disturb optimisations from inling push
{-
build :: forall a. (forall b. (a -> b -> b) -> b -> b) -> Queue a
build g = g push empty

mapFB :: (a -> q -> q) -> (x -> a) -> x -> q -> q
mapFB c f = \x ys -> c (f x) ys
{-# inline [0] mapFB #-}

"map build" [~1] forall f q. map f q = build (\cons nil -> foldr (mapFB cons f) nil q)
"map queue" [1]  forall f.   foldr (mapFB push f) empty = map f
-}

-- map id = id rule eta-expands id, because id is very likely to inline first
{-# RULES
"toList . fromList = id" [1] forall q. toList (fromList q) = q

"map coerce = coerce" [1] Rtq.Internal.map coerce    = coerce
"map id = id"         [1] Rtq.Internal.map (\x -> x) = id
#-}



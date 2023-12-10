{-# LANGUAGE BangPatterns                            #-}
{-# LANGUAGE DerivingStrategies                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving              #-}
{-# LANGUAGE LambdaCase                              #-}
{-# LANGUAGE OverloadedStrings                       #-}
{-# LANGUAGE StrictData                              #-}
{-# OPTIONS_GHC -fno-warn-compat-unqualified-imports #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing             #-}
{-# OPTIONS_GHC -fno-warn-unused-imports             #-}

module Lib where


import Data.Foldable
import Data.Containers.ListUtils
import Control.Monad.State
import qualified Data.Map as M
import Data.Map (Map)
import Control.Arrow
import Data.Functor
import qualified Data.ByteString.Lazy as BS
import Sound.MIDI (decodeMidi)
import Data.Foldable
import Control.Monad
import Data.Ord
import Data.Function
import Data.List
import Control.Lens (ix, (.~))
import qualified Data.IntMap as IM
import Data.IntMap (IntMap)
import Control.Applicative
import Data.Sequence (Seq(..))
import GHC.Exts (fromList)
import Data.Maybe (maybeToList, mapMaybe)
import Data.Semigroup
import Codec.ByteString.Parser (runParser)
import Codec.Midi (parseMidi, Message(..), tracks)

newtype Pitch = P Int
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

newtype Time = T Int
  deriving (Eq, Ord, Show, Read, Num, Enum, Bounded)

data Note = N
  { n_pitch    :: !Pitch
  , n_start    :: !Time
  , n_duration :: !Time
  }
  deriving (Eq, Ord, Show, Read)

newtype Line = L (Seq Note)
  deriving newtype (Eq, Ord, Show, Read, Semigroup, Monoid)

data Score = S
  { ps_lines :: !(IntMap Line)
  }
  deriving (Eq, Ord, Show, Read)

c, d, e, f, g :: Int -> Pitch
c n = P $ n * 12 + 0
d n = P $ n * 12 + 1
e n = P $ n * 12 + 2
f n = P $ n * 12 + 3
g n = P $ n * 12 + 4

ode_melody :: [Pitch]
ode_melody =
  [ e 1, e 1, f 1, g 1, g 1, f 1, e 1, d 1
  , c 1, c 1, d 1, e 1, e 1, d 1, d 1, d 1
  , e 1, e 1, f 1, g 1, g 1, f 1, e 1, d 1
  , c 1, c 1, d 1, e 1, d 1, c 1, c 1, c 1
  ]

ode_chords :: [[Pitch]]
ode_chords =
  [ [c 0, g 0]
  , [d 0, g 0]
  , [e 0, g 0]
  , [f 0, g 0]
  , [c 0, g 0]
  , [d 0, g 0]
  , [e 0, g 0]
  , [c 0, e 0, g 0]
  ]

ode :: [Note]
ode = sortBy (comparing n_start)
  $  zipWith (\p i -> N p (T i) 1) ode_melody [0..]
  ++ join (zipWith (\c i -> fmap (\p -> N p (T $ i * 4) 4) c) ode_chords [0..])

appendLine :: Note -> Line -> Maybe Line
appendLine n (L Empty) = pure $ L $ pure n
appendLine n@(N _ s2 _) (L l@(_ :|> (N _ s d)))
  | s + d <= s2 = pure $ L $ l :|> n
  | otherwise   = empty

appendScore :: Note -> Score -> [Score]
appendScore n (S ls) =
  (do
    i <- [0 .. IM.size ls - 1]
    let l = ls IM.! i
    l' <- maybeToList $ appendLine n l
    pure $ S $ ix i .~ l' $ ls
  ) ++ [S $ IM.insert (IM.size ls) (L $ Empty :|> n) ls
       | all (/= L Empty) ls
       ]

data VisualScore = VS
  { vs_width  :: !(Max Time)
  , vs_height :: !(Max Pitch)
  , vs_data   :: Pitch -> Time -> Maybe (Max Int)
  }

instance Semigroup VisualScore where
  VS w1 h1 d1 <> VS w2 h2 d2
    = VS (w1 <> w2) (h1 <> h2) (d1 <> d2)

instance Monoid VisualScore where
  mempty = VS (Max $ T 0) (Max $ P 0) $ pure $ pure empty

visualizeLine :: Int -> Line -> VisualScore
visualizeLine i (L l) = flip foldMap (toList l) $ \(N p (T s) (T d)) ->
  mconcat $! do
    t <- [0 .. d]
    pure $! VS (Max $ T $ s + d) (Max p) $! \p' (T t') ->
      if p' == p && s <= t' && t' < s + t
         then pure $! pure i
         else mempty

visualizeScore :: Score -> VisualScore
visualizeScore = mconcat . fmap (uncurry visualizeLine) . IM.assocs . ps_lines

visualize :: VisualScore -> IO ()
visualize (VS w h d) = putStrLn $ unlines $ fmap ('.' :) $ reverse $ do
  y <- enumFromTo (P 0) (getMax h) -- (getMax h - 1) 0
  pure $ do
    x <- [0 .. getMax w]
    pure $ case d y x of
      Just v -> toEnum $ fromEnum '0' + getMax v
      Nothing -> ' '

numLines :: Score -> Int
numLines = IM.size . ps_lines

lineOf :: Int -> Score -> Line
lineOf i = (IM.! i) . ps_lines

parse :: [Note] -> [Score]
parse = foldl' (\ls n -> ls >>= appendScore n) [S $ IM.singleton 0 $ L Empty]

test :: [Score]
test = parse ode

toNoteMsg :: Message -> Maybe (Pitch, Bool)
toNoteMsg (NoteOn _ k 0) = pure (P k, False)
toNoteMsg (NoteOn _ k _) = pure (P k, True)
toNoteMsg _ = Nothing

track :: [(Int, (Pitch, Bool))] -> State (Map Pitch Int) [Note]
track [] = pure []
track ((t, (p, False)) : xs) =
  gets (M.lookup p) >>= \case
    Just t0 -> do
      modify $ M.delete p
      (:) <$> pure (N p (T t0) (T $ t - t0)) <*> track xs
    Nothing -> track xs -- do
      -- st <- get
      -- error $ unlines
      --   [ "not found: " <> show p
      --   , "state: " <> show st
      --   ]
track ((t, (p, True)) : xs) = do
  modify $ M.insert p t
  track xs

main :: IO ()
main = do
  bs <- BS.readFile "/home/sandy/monty.mid"
  Right ms <- pure $ runParser parseMidi bs
  print $ length $ tracks ms

  let pairs = fmap (flip evalState mempty . track . sortOn fst) $ fmap (mapMaybe $ traverse toNoteMsg) $ tracks ms
  let notes = sortOn n_start $ filter ((/= T 0) . n_duration) $ nubOrd $ join pairs
  visualize $ visualizeScore $ head $ parse notes


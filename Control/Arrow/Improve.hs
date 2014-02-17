{-# LANGUAGE GADTs #-}

module Control.Arrow.Improve(ImproveArrow, lowerImprove) where

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

data ImproveArrow a b c where
  IArrow :: a b c    -> ImproveArrow a b c
  IArr   :: (b -> c) -> ImproveArrow a b c
  IId    ::             ImproveArrow a b b
  IConst :: c        -> ImproveArrow a b c

lowerImprove :: (Arrow a) => ImproveArrow a b c -> a b c
lowerImprove (IArrow a) = a
lowerImprove (IArr f)   = arr f
lowerImprove IId        = id
lowerImprove (IConst k) = arr (\_ -> k)


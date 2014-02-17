{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Arrow.Improve(ImproveArrow, lowerImprove) where

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

import Control.Arrow.Transformer

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

instance (Arrow a) => Category (ImproveArrow a) where
  id = IId
  IId      . x        = x
  x        . IId      = x
  IConst k . IArr _   = IConst k
  IConst k . IConst _ = IConst k
  IConst k . IArrow f = IArrow (f >>^ (\_ -> k))
  IArr f   . IArr g   = IArr (f . g)
  IArr f   . IConst k = IConst (f k)
  IArr f   . IArrow g = IArrow (g >>^ f)
  IArrow f . IArr g   = IArrow (g ^>> f)
  IArrow f . IConst k = IArrow ((\_ -> k) ^>> f)
  IArrow f . IArrow g = IArrow (g >>> f)

instance (Arrow a) => Arrow (ImproveArrow a) where
  arr = IArr
  first (IArrow x) = IArrow (first x)
  first (IArr f)   = IArr (first f)
  first (IConst k) = IArr (first (\_ -> k))
  first IId        = IId

  second (IArrow x) = IArrow (second x)
  second (IArr f)   = IArr (second f)
  second (IConst k) = IArr (second (\_ -> k))
  second IId        = IId

  IId      *** IId      = IId
  f        *** IId      = first f
  IId      *** f        = second f
  IConst k *** IConst j = IConst (k, j)
  IArr f   *** IArr g   = IArr (f *** g)
  IArr f   *** IConst k = IArr (f *** (\_ -> k))
  IConst k *** IArr f   = IArr ((\_ -> k) *** f)
  f        *** g        = first f >>> second g

instance (Arrow a) => ArrowTransformer ImproveArrow a where
  lift = IArrow


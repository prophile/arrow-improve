{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.Improve(ImproveArrow, lowerImprove) where

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

import Control.Applicative

import Control.Arrow.Transformer
import Control.Arrow.Operations

import Data.Profunctor

import Data.Monoid

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

  IId      &&& IId      = IArr (\x -> (x, x))
  IArr f   &&& IId      = IArr (\x -> (f x, x))
  IId      &&& IArr f   = IArr (\x -> (x, f x))
  IArr f   &&& IArr g   = IArr (\x -> (f x, g x))
  IConst k &&& IConst j = IConst (k, j)
  IId      &&& IConst k = IArr (\x -> (x, k))
  IConst k &&& IId      = IArr (\x -> (k, x))
  IConst k &&& IArr f   = IArr (\x -> (k, f x))
  IArr f   &&& IConst k = IArr (\x -> (f x, k))
  IArrow f &&& IConst k = IArrow f >>> IArr (\x -> (x, k))
  IConst k &&& IArrow f = IArrow f >>> IArr (\x -> (k, x))
  f        &&& g        = IArr (\x -> (x, x)) >>> (f *** g)

instance (ArrowZero a) => ArrowZero (ImproveArrow a) where
  zeroArrow = IArrow zeroArrow

instance (ArrowPlus a) => ArrowPlus (ImproveArrow a) where
  f <+> g = lift (lowerImprove f <+> lowerImprove g)

instance (ArrowChoice a) => ArrowChoice (ImproveArrow a) where
  left  = lift . left . lowerImprove
  right = lift . right . lowerImprove

instance (ArrowApply a) => ArrowApply (ImproveArrow a) where
  app = lift $ first lowerImprove ^>> app

instance (ArrowLoop a) => ArrowLoop (ImproveArrow a) where
  loop IId             = IId
  loop (IArr f)        = IArr f'
    where f' x         = let (y, k) = f (x, k) in y
  loop (IConst (k, _)) = IConst k
  loop (IArrow f)      = IArrow (loop f)

instance (ArrowCircuit a) => ArrowCircuit (ImproveArrow a) where
  delay = lift . delay

instance (ArrowState s a) => ArrowState s (ImproveArrow a) where
  fetch = lift fetch
  store = lift store

instance (ArrowReader r a) => ArrowReader r (ImproveArrow a) where
  readState = lift readState
  newReader IId = IArr fst
  newReader (IConst k) = IConst k
  newReader x = IArrow (newReader (lowerImprove x))

instance (Monoid w, ArrowWriter w a) => ArrowWriter w (ImproveArrow a) where
  write = lift write
  newWriter IId        = IArr (\x -> (x, mempty))
  newWriter (IConst k) = IConst (k, mempty)
  newWriter (IArr f)   = IArr ((\x -> (x, mempty)) . f)
  newWriter (IArrow a) = IArrow (newWriter a)

instance (ArrowError ex a) => ArrowError ex (ImproveArrow a) where
  raise = lift raise

  handle IId _        = IId
  handle (IConst k) _ = IConst k
  handle (IArr f) _   = IArr f
  handle (IArrow f) e = IArrow (handle f (lowerImprove e))

  tryInUnless IId f _        = IArr (\x -> (x, x)) >>> f
  tryInUnless (IConst k) f _ = IArr (\x -> (x, k)) >>> f
  tryInUnless (IArr g) f _   = IArr (\x -> (x, g x)) >>> f
  tryInUnless (IArrow a) f e = IArrow (tryInUnless a (lowerImprove f) (lowerImprove e))

  newError IId        = IArr Right
  newError (IConst k) = IConst (Right k)
  newError (IArr f)   = IArr (Right . f)
  newError (IArrow f) = IArrow (newError f)

instance (Arrow a) => Functor (ImproveArrow a b) where
  fmap f = (>>^ f)

instance (Arrow a) => Applicative (ImproveArrow a b) where
  pure = IConst
  f <*> x = (f &&& x) >>> arr (uncurry id)

instance (ArrowPlus a) => Alternative (ImproveArrow a b) where
  empty = zeroArrow
  (<|>) = (<+>)

instance (ArrowApply a) => Monad (ImproveArrow a b) where
  return = IConst
  IConst k >>= f = f k
  x >>= f = ((x >>^ f) &&& id) >>> app

instance (Arrow a) => Profunctor (ImproveArrow a) where
  dimap f g x = f ^>> x >>^ g
  lmap f x = f ^>> x
  rmap g x = x >>^ g

instance (Arrow a) => Strong (ImproveArrow a) where
  first' = first
  second' = second

instance (ArrowChoice a) => Choice (ImproveArrow a) where
  left' = left
  right' = right

instance (Arrow a) => ArrowTransformer ImproveArrow a where
  lift = IArrow


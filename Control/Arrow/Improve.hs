{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- |Improved arrows, with a whole host of minor optimisations and instances.
module Control.Arrow.Improve(ImproveArrow, lowerImprove) where

import Prelude hiding (id, (.))

import Control.Category
import Control.Arrow

import Control.Applicative
import Control.Monad
import Control.Monad.Zip

import Control.Arrow.Transformer
import Control.Arrow.Operations

import Data.Profunctor
import Data.Semigroupoid
import Data.Functor.Plus
import Data.Functor.Bind
import Data.Pointed

import Data.Monoid

-- |Basic improved arrow type.
data ImproveArrow a b c where
  IArr   :: (b -> c)                      -> ImproveArrow a b c
  IArrow :: (i -> b) -> a b c -> (c -> o) -> ImproveArrow a i o

-- |Lower an improved arrow to the original arrow type.
--
-- prop>  lowerImprove . lift = id
-- prop>  lift . lowerImprove = id
lowerImprove :: (Arrow a) => ImproveArrow a b c -> a b c
lowerImprove (IArrow f a g) = f ^>> a >>^ g
lowerImprove (IArr f)   = arr f

instance (Arrow a) => Category (ImproveArrow a) where
  id = arr id
  {-# INLINE id #-}
  IArr f . IArr g             = IArr (f . g)
  IArr h . IArrow f a g       = IArrow f a (h . g)
  IArrow f a g . IArr h       = IArrow (f . h) a g
  IArrow f a g . IArrow h b i = IArrow h (b >>> arr (f . i) >>> a) g
  {-# INLINABLE (.) #-}

instance (Arrow a) => Arrow (ImproveArrow a) where
  arr = IArr
  {-# INLINE arr #-}

  first (IArr f) = IArr (first f)
  first (IArrow f a g) = IArrow (first f) (first a) (first g)
  {-# INLINABLE first #-}

  second (IArr f) = IArr (second f)
  second (IArrow f a g) = IArrow (second f) (second a) (second g)
  {-# INLINABLE second #-}

  IArr f *** IArr g             = IArr   (f *** g)
  IArr h *** IArrow f a g       = IArrow (second f) (second a) (h *** g)
  IArrow f a g *** IArr h       = IArrow (first f) (first a) (g *** h)
  IArrow f a g *** IArrow h b i = IArrow (f *** h) (a *** b) (g *** i)
  {-# INLINABLE (***) #-}

  IArr f &&& IArr g = IArr (f &&& g)
  IArrow f a g &&& IArr h = IArrow (f &&& h) (first a) (first g)
  IArr h &&& IArrow f a g = IArrow (h &&& f) (second a) (second g)
  -- TODO: use a rule to use a &&& b instead when f == h
  IArrow f a g &&& IArrow h b i = IArrow (f &&& h) (a *** b) (g *** i)
  {-# INLINABLE (&&&) #-}

instance (ArrowZero a) => ArrowZero (ImproveArrow a) where
  zeroArrow = lift zeroArrow
  {-# INLINE zeroArrow #-}

instance (ArrowPlus a) => ArrowPlus (ImproveArrow a) where
  f <+> g = lift (lowerImprove f <+> lowerImprove g)
  {-# INLINE (<+>) #-}

instance (ArrowChoice a) => ArrowChoice (ImproveArrow a) where
  left (IArr f) = IArr (left f)
  left (IArrow f a g) = IArrow (left f) (left a) (left g)
  {-# INLINE left #-}

  right (IArr f) = IArr (right f)
  right (IArrow f a g) = IArrow (right f) (right a) (right g)
  {-# INLINE right #-}

  IArr f +++ IArr g = IArr (f +++ g)
  IArrow f a g +++ IArr h = IArrow (left f) (left a) (g +++ h)
  IArr h +++ IArrow f a g = IArrow (right f) (right a) (h +++ g)
  IArrow f a g +++ IArrow h b i = IArrow (f +++ h) (a +++ b) (g +++ i)
  {-# INLINABLE (+++) #-}

  IArr f ||| IArr g = IArr (f ||| g)
  IArrow f a g ||| IArr h = IArrow (left f) (left a) (g ||| h)
  IArr h ||| IArrow f a g = IArrow (right f) (right a) (h ||| g)
  -- TODO: use rules to turn the +++ into a ||| on the arrow when g == i
  IArrow f a g ||| IArrow h b i = IArrow (f +++ h) (a +++ b) (g ||| i)
  {-# INLINABLE (|||) #-}

instance (ArrowApply a) => ArrowApply (ImproveArrow a) where
  app = lift $ first lowerImprove ^>> app
  {-# INLINE app #-}

instance (ArrowLoop a) => ArrowLoop (ImproveArrow a) where
  loop (IArr f)        = IArr f'
    where f' x         = let (y, k) = f (x, k) in y
  loop (IArrow f a g)  = lift (loop (f ^>> a >>^ g))
  {-# INLINE loop #-}

instance (ArrowCircuit a) => ArrowCircuit (ImproveArrow a) where
  delay = lift . delay
  {-# INLINE delay #-}

instance (ArrowState s a) => ArrowState s (ImproveArrow a) where
  fetch = lift fetch
  {-# INLINE fetch #-}
  store = lift store
  {-# INLINE store #-}

instance (ArrowReader r a) => ArrowReader r (ImproveArrow a) where
  readState = lift readState
  {-# INLINE readState #-}
  newReader (IArr f) = lift $ newReader $ arr f
  newReader (IArrow f a g) = IArrow id (newReader (f ^>> a)) g
  {-# INLINE newReader #-}

instance (Monoid w, ArrowWriter w a) => ArrowWriter w (ImproveArrow a) where
  write = lift write
  {-# INLINE write #-}
  newWriter (IArr f)       = IArr ((\x -> (x, mempty)) . f)
  newWriter (IArrow f a g) = IArrow f (newWriter (a >>^ g)) id
  {-# INLINABLE newWriter #-}

instance (ArrowError ex a) => ArrowError ex (ImproveArrow a) where
  raise = lift raise
  {-# INLINE raise #-}

  handle (IArr f) _       = IArr f
  handle a@(IArrow _ _ _) e = lift (handle (lowerImprove a) (lowerImprove e))
  {-# INLINABLE handle #-}

  tryInUnless (IArr g) f _   = IArr (\x -> (x, g x)) >>> f
  tryInUnless a@(IArrow _ _ _) f e = lift (tryInUnless (lowerImprove a)
                                                         (lowerImprove f)
                                                         (lowerImprove e))
  {-# INLINABLE tryInUnless #-}

  newError (IArr f) = IArr (Right . f)
  newError a@(IArrow _ _ _) = lift (newError (lowerImprove a))
  {-# INLINABLE newError #-}

instance (Arrow a) => Functor (ImproveArrow a b) where
  fmap f = (>>^ f)
  {-# INLINE fmap #-}

instance (Arrow a) => Applicative (ImproveArrow a b) where
  pure k = IArr (\_ -> k)
  {-# INLINE pure #-}
  f <*> x = (f &&& x) >>^ uncurry id
  {-# INLINE (<*>) #-}

instance (ArrowPlus a) => Alternative (ImproveArrow a b) where
  empty = zeroArrow
  {-# INLINE empty #-}
  (<|>) = (<+>)
  {-# INLINE (<|>) #-}

instance (ArrowApply a) => Monad (ImproveArrow a b) where
  return = pure
  {-# INLINE return #-}
  x >>= f = ((x >>^ f) &&& id) >>> app
  {-# INLINE (>>=) #-}

instance (ArrowPlus a, ArrowApply a) => MonadPlus (ImproveArrow a b) where
  mzero = zeroArrow
  {-# INLINE mzero #-}
  mplus = (<+>)
  {-# INLINE mplus #-}

instance (ArrowApply a) => MonadZip (ImproveArrow a b) where
  mzip = (&&&)
  {-# INLINE mzip #-}

instance (Arrow a) => Profunctor (ImproveArrow a) where
  dimap f g x = f ^>> x >>^ g
  {-# INLINE dimap #-}
  lmap f x = f ^>> x
  {-# INLINE lmap #-}
  rmap g x = x >>^ g
  {-# INLINE rmap #-}

instance (Arrow a) => Strong (ImproveArrow a) where
  first' = first
  {-# INLINE first' #-}
  second' = second
  {-# INLINE second' #-}

instance (ArrowChoice a) => Choice (ImproveArrow a) where
  left' = left
  {-# INLINE left' #-}
  right' = right
  {-# INLINE right' #-}

instance (Arrow a) => Pointed (ImproveArrow a b) where
  point = pure
  {-# INLINE point #-}

instance (Arrow a) => Semigroupoid (ImproveArrow a) where
  o = (.)
  {-# INLINE o #-}

instance (ArrowPlus a) => Alt (ImproveArrow a b) where
  (<!>) = (<+>)
  {-# INLINE (<!>) #-}

instance (Arrow a) => Apply (ImproveArrow a b) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

instance (ArrowApply a) => Bind (ImproveArrow a b) where
  (>>-) = (>>=)
  {-# INLINE (>>-) #-}

instance (ArrowPlus a) => Plus (ImproveArrow a b) where
  zero = zeroArrow
  {-# INLINE zero #-}

instance (ArrowPlus a) => Monoid (ImproveArrow a b c) where
  mempty = zeroArrow
  {-# INLINE mempty #-}
  mappend = (<+>)
  {-# INLINE mappend #-}

instance (Arrow a, Num c) => Num (ImproveArrow a b c) where
  (+) = liftA2 (+)
  {-# INLINE (+) #-}
  (-) = liftA2 (-)
  {-# INLINE (-) #-}
  (*) = liftA2 (*)
  {-# INLINE (*) #-}

  negate = fmap negate
  {-# INLINE negate #-}

  abs = fmap abs
  {-# INLINE abs #-}
  signum = fmap signum
  {-# INLINE signum #-}

  fromInteger = pure . fromInteger
  {-# INLINE fromInteger #-}

instance (Arrow a) => ArrowTransformer ImproveArrow a where
  lift x = IArrow id x id
  {-# INLINE lift #-}


{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.GADT.Show where

import Data.Constraint.Forall
import Data.Constraint.Extras
import Data.Functor.Sum (Sum (..))
import Data.Functor.Product (Product (..))
import Data.Type.Equality ((:~:) (..))

#if MIN_VERSION_base(4,10,0)
import qualified Type.Reflection as TR
#endif

-- $setup
-- >>> import Data.Some

-- |'Show'-like class for 1-type-parameter GADTs.  @GShow t => ...@ is equivalent to something
-- like @(forall a. Show (t a)) => ...@.  The easiest way to create instances would probably be
-- to write (or derive) an @instance Show (T a)@, and then simply say:
--
-- > instance GShow t
--
-- with any additional constraints as might be required by the Show instance.
class GShow t where
    gshowsPrec :: Int -> t a -> ShowS
    default gshowsPrec :: ForallF Show t => Int -> t a -> ShowS
    gshowsPrec n (x :: t a) = whichever @Show @t @a (showsPrec n x)

gshows :: GShow t => t a -> ShowS
gshows = gshowsPrec (-1)

gshow :: (GShow t) => t a -> String
gshow x = gshows x ""

instance GShow ((:~:) a) where
    gshowsPrec _ Refl = showString "Refl"

#if MIN_VERSION_base(4,10,0)
instance GShow TR.TypeRep where
    gshowsPrec = showsPrec
#endif

--
-- | >>> gshow (InL Refl :: Sum ((:~:) Int) ((:~:) Bool) Int)
-- "InL Refl"
instance (GShow a, GShow b) => GShow (Sum a b) where
    gshowsPrec d = \s -> case s of
        InL x -> showParen (d > 10) (showString "InL " . gshowsPrec 11 x)
        InR x -> showParen (d > 10) (showString "InR " . gshowsPrec 11 x)

-- | >>> gshow (Pair Refl Refl :: Product ((:~:) Int) ((:~:) Int) Int)
-- "Pair Refl Refl"
instance (GShow a, GShow b) => GShow (Product a b) where
    gshowsPrec d (Pair x y) = showParen (d > 10)
        $ showString "Pair "
        . gshowsPrec 11 x
        . showChar ' '
        . gshowsPrec 11 y

newtype GReadResult t = GReadResult
  { getGReadResult :: forall b . (forall a . t a -> b) -> b }

-- |@GReadS t@ is equivalent to @ReadS (forall b. (forall a. t a -> b) -> b)@, which is 
-- in turn equivalent to @ReadS (Exists t)@ (with @data Exists t where Exists :: t a -> Exists t@)
type GReadS t = String -> [(GReadResult t, String)]

-- |'Read'-like class for 1-type-parameter GADTs.  Unlike 'GShow', this one cannot be 
-- mechanically derived from a 'Read' instance because 'greadsPrec' must choose the phantom
-- type based on the 'String' being parsed.
class GRead t where
    greadsPrec :: Int -> GReadS t

greads :: GRead t => GReadS t
greads = greadsPrec (-1)

gread :: GRead t => String -> (forall a. t a -> b) -> b
gread s g = case hd [f | (f, "") <- greads s] of
              GReadResult res -> res g
    where
        hd (x:_) = x
        hd _ = error "gread: no parse"

-- |
--
-- >>> greadMaybe "InL Refl" mkSome :: Maybe (Some (Sum ((:~:) Int) ((:~:) Bool)))
-- Just (Some (InL Refl))
--
-- >>> greadMaybe "garbage" mkSome :: Maybe (Some ((:~:) Int))
-- Nothing
--
greadMaybe :: GRead t => String -> (forall a. t a -> b) -> Maybe b
greadMaybe s g = case [f | (f, "") <- greads s] of
    (GReadResult res : _) -> Just (res g)
    _                     -> Nothing

instance GRead ((:~:) a) where
    greadsPrec p s = readsPrec p s >>= f
        where
            f :: forall x. (x :~: x, String) -> [(GReadResult ((:~:) x), String)]
            f (Refl, rest) = return (GReadResult (\x -> x Refl) , rest)

instance (GRead a, GRead b) => GRead (Sum a b) where
    greadsPrec d s = concat
        [ readParen (d > 10)
            (\s1 -> [ (GReadResult $ \k -> getGReadResult r (k . InL), t)
                    | ("InL", s2) <- lex s1
                    , (r, t) <- greadsPrec 11 s2 ]) s
        , readParen (d > 10)
            (\s1 -> [ (GReadResult $ \k -> getGReadResult r (k . InR), t)
                    | ("InR", s2) <- lex s1
                    , (r, t) <- greadsPrec 11 s2 ]) s
        ]

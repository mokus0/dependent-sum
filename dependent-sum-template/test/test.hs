{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
import Control.Monad
import Data.Dependent.Sum
import Data.Functor.Identity
import Data.Constraint.Extras.TH
import Data.GADT.Compare
import Data.GADT.Compare.TH
import Data.GADT.Show
import Data.GADT.Show.TH
import Data.Type.Equality

data MySum :: * -> * where
  MySum_Int :: MySum Int
  MySum_String :: MySum String

deriving instance Eq (MySum a)
deriving instance Ord (MySum a)
deriving instance Show (MySum a)

deriveGShow ''MySum
deriveGEq ''MySum
deriveGCompare ''MySum
deriveArgDict ''MySum

data MyNestedSum :: * -> * where
  MyNestedSum_MySum :: MySum a -> MyNestedSum a
  MyNestedSum_Int :: Int -> MyNestedSum Int
  MyNestedSum_String :: [Int] -> MyNestedSum String

deriving instance Eq (MyNestedSum a)
deriving instance Ord (MyNestedSum a)
deriving instance Show (MyNestedSum a)

deriveGShow ''MyNestedSum
deriveGEq ''MyNestedSum
deriveGCompare ''MyNestedSum
deriveArgDict ''MyNestedSum

polyTests
  :: forall m f
  .  ( MonadPlus m, Show (f Int), Show (f String)
     , GCompare f, GShow f)
  => (forall a. MySum a -> f a)
  -> m ()
polyTests f = do
  do
    let showSame :: forall a. Show (f a) => f a -> Bool
        showSame gadt = show gadt == gshow gadt
    guard $ showSame $ f MySum_Int
    guard $ showSame $ f MySum_String
  guard $ (f MySum_Int `geq` f MySum_Int) == Just Refl
  guard $ (f MySum_Int `gcompare` f MySum_Int) == GEQ
  guard $ (f MySum_String `geq` f MySum_String) == Just Refl
  guard $ (f MySum_String `gcompare` f MySum_String) == GEQ
  guard $ (f MySum_Int `gcompare` f MySum_String) == GLT
  guard $ (f MySum_String `gcompare` f MySum_Int) == GGT

main :: IO ()
main = do
  polyTests id
  polyTests MyNestedSum_MySum
  return ()

--TODO: Figure out how to best use these test cases; just checking that they
-- compile is useful, but it's probably more useful to check some properties as
-- well

-- test cases: should be able to generate instances for these
-- (Bar requiring the existence of an instance for Foo)
data Foo a where
    I :: Foo Int
    D :: Foo Double
    A :: Foo a -> Foo b -> Foo (a -> b)

data Bar a where
    F :: Foo a -> Bar a
    S :: Bar String

data Baz a where
    L :: Qux a -> Int -> Baz [a]

data Qux a where
    FB :: Foo (a -> b) -> Bar b -> Qux (a -> (b, b))

deriveGEq ''Foo
deriveGEq ''Bar
deriveGEq ''Qux
deriveGEq ''Baz

deriveGCompare ''Foo
deriveGCompare ''Bar
deriveGCompare ''Qux
deriveGCompare ''Baz

deriveGShow ''Foo
instance Show (Foo a) where showsPrec = gshowsPrec
deriveGShow ''Bar
instance Show (Bar a) where showsPrec = gshowsPrec
deriveGShow ''Qux
instance Show (Qux a) where showsPrec = gshowsPrec
deriveGShow ''Baz
instance Show (Baz a) where showsPrec = gshowsPrec

data Squudge a where
    E :: Ord a => Foo a -> Squudge a

deriveGEq ''Squudge
deriveGCompare ''Squudge
deriveGShow ''Squudge
instance Show (Squudge a) where showsPrec = gshowsPrec

data Splort a where
    Splort :: Squudge a -> a -> Splort a

-- -- deriveGEq ''Splort
-- This one theoretically could work (instance explicitly given below), but I don't think
-- it's something I want to try to automagically support.  It would require actually
-- matching on sub-constructors, which could get pretty ugly, especially since it may
-- not even be the case that a finite number of matches would suffice.
instance GEq Splort where
    geq (Splort (E x1) x2) (Splort (E y1) y2) = do
        Refl <- geq x1 y1
        guard (x2 == y2)
        Just Refl

deriving instance Show a => Show (Splort a)

instance GCompare Splort where
    gcompare (Splort (E x1) x2) (Splort (E y1) y2) =
        runGComparing $ do
            Refl <- geq' x1 y1
            compare' x2 y2
            return GEQ

-- Also should work for empty types
data Empty a
deriveGEq ''Empty
deriveGCompare ''Empty

-- Also supports types with multiple parameters, by quoting empty instance declarations
-- ([t||] brackets won't work because they can only quote types of kind *).
data Spleeb a b where
    P :: a Double -> Qux b -> Spleeb a b
-- need a cleaner 'one-shot' way of defining these - the empty instances need to appear
-- in the same quotation because the GEq context of the GCompare class causes stage
-- restriction errors... seems like GHC shouldn't actually check things like that till
-- the final splice, but whatever.
do
    [geqInst, gcompareInst, gshowInst] <-
        [d|
            instance GEq a => GEq (Spleeb a)
            instance GCompare a => GCompare (Spleeb a)
            instance Show (a Double) => GShow (Spleeb a)
          |]

    concat <$> sequence
        [ deriveGEq      geqInst
        , deriveGCompare gcompareInst
        , deriveGShow    gshowInst
        ]

instance Show (a Double) => Show (Spleeb a b) where showsPrec = gshowsPrec

-- another option; start from the declaration and juggle that a bit
do
    decs <- [d|
        data Fnord a where Yarr :: Fnord Double; Grr :: Fnord (Int -> String)
     |]

    geqInst         <- deriveGEq      decs
    gcompareInst    <- deriveGCompare decs
    gshowInst       <- deriveGShow    decs

    return $ concat
        [ decs
        , geqInst
        , gcompareInst
        , gshowInst
        ]

instance Show (Fnord a) where showsPrec = gshowsPrec

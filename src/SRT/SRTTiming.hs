{-# LANGUAGE InstanceSigs       #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE QuasiQuotes        #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE UnicodeSyntax      #-}

module SRT.SRTTiming
  ( SRTTiming( SRTTiming ), tests )
where

-- base --------------------------------

import Data.Either    ( Either( Right ) )
import Data.Eq        ( Eq )
import Data.Function  ( ($) )
import Data.Maybe     ( Maybe( Just ) )
import Data.String    ( String )
import System.Exit    ( ExitCode )
import System.IO      ( IO )
import Text.Show      ( Show )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ), Textual( textual ), fromText,toText )

-- duration ----------------------------

import Duration  ( Duration( MS ) )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFunctor( omap ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋫) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Natural      ( ℕ )

-- parsec-plus -------------------------

import ParsecPlus  ( Parsecable( parsec, parser ), ParseError )

-- parsers -----------------------------

import Text.Parser.Char  ( string )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary ( Arbitrary( arbitrary ) )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( (@=?), testCase )

-- tasty-plus --------------------------

import TastyPlus  ( (≟)
                  , propInvertibleText, runTestsP, runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( testProperty )

-- text --------------------------------

import Data.Text  ( Text )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Shifty        ( Shifty( shift ) )
import SRT.Skew          ( Skew( MS_S ) )
import SRT.SRTTimeStamp  ( SRTTimeStamp )

--------------------------------------------------------------------------------

data SRTTiming = SRTTiming SRTTimeStamp SRTTimeStamp
  deriving (Eq, Show)

type instance Element SRTTiming = SRTTimeStamp

instance MonoFunctor SRTTiming where
  omap ∷ (SRTTimeStamp → SRTTimeStamp) → SRTTiming → SRTTiming
  omap f (SRTTiming start end) = SRTTiming (f start) (f end)

instance Shifty SRTTiming where
  shift ∷ Duration → Skew → SRTTiming → SRTTiming
  shift off sf (SRTTiming t t') = SRTTiming (shift off sf t) (shift off sf t')

instance Printable SRTTiming where
  print (SRTTiming begin end) = P.text $ [fmt|%T --> %T|] begin end

instance Textual SRTTiming where
  textual = SRTTiming ⊳ textual ⊵ string " --> " ⋫ textual

instance Parsecable SRTTiming where
  parser = textual

instance Arbitrary SRTTiming where
  arbitrary = SRTTiming ⊳ arbitrary ⊵ arbitrary

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test-data -----------------------------------------------

srtTiming ∷ Text
srtTiming = "00:00:01,000 --> 00:00:04,074"

srtTimingRef ∷ SRTTiming
srtTimingRef = SRTTiming 1_000 4_074

------------------------------------------------------------

tests ∷ TestTree
tests =
  testGroup "SRTTiming"
            [ testCase "fromText" $ Just srtTimingRef @=? fromText srtTiming
            , testCase "toText"   $ srtTiming ≟ toText srtTimingRef
            , testCase "parsec"   $
                    Right (SRTTiming 1_000 4_074)
                @=? parsec @SRTTiming @ParseError @(Either ParseError)
                           @Text @String "srtTimestamp" srtTiming
            , testProperty "invertibleText" (propInvertibleText @SRTTiming)
            , testCase "shift" $
                    SRTTiming 1800 4_567
                  ≟ shift (MS 1000) (MS_S (-100)) srtTimingRef
            ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------

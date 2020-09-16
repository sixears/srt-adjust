{-# LANGUAGE InstanceSigs       #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE UnicodeSyntax      #-}

module SRT.SRTSubtitle
  ( SRTSubtitle( SRTSubtitle ), subtitle, timing

  , tests )
where

-- base --------------------------------

import Data.Either    ( Either( Right ) )
import Data.Eq        ( Eq )
import Data.Function  ( ($), (&) )
import Data.Maybe     ( Maybe( Just ) )
import Data.String    ( String )
import Data.Word      ( Word32 )
import System.Exit    ( ExitCode )
import System.IO      ( IO )
import Text.Show      ( Show )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode  ( (≢) )

-- data-textual ------------------------

import Data.Textual           ( Printable( print ), Textual( textual )
                              , fromText, toText )
import Data.Textual.Integral  ( Decimal( Decimal ), nnBounded )

-- duration ----------------------------

import Duration  ( Duration( MS ) )

-- lens --------------------------------

import Control.Lens.Lens    ( Lens', lens )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋪) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Lens         ( (⊧) )
import Data.MoreUnicode.Natural      ( ℕ )

-- parsec-plus -------------------------

import ParsecPlus  ( ParseError )
import ParsecPlus  ( Parsecable( parsec, parser ) )

-- parser-plus -------------------------

import ParserPlus  ( nl, whitespaces )

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

import Data.Text  ( Text, filter, intercalate, unlines )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Shifty           ( Shifty( shift ) )
import SRT.SRTSubtitleText  ( SRTSubtitleText( SRTSubtitleText ) )
import SRT.SRTTiming        ( SRTTiming( SRTTiming ) )
import SRT.Skew             ( Skew( MS_S ) )
import SRT.TFunctor         ( TFunctor( tmap ) )

--------------------------------------------------------------------------------

data SRTSubtitle = SRTSubtitle { _id       ∷ Word32
                               , _timing   ∷ SRTTiming
                               , _subtitle ∷ SRTSubtitleText
                               }
  deriving (Eq, Show)

timing ∷ Lens' SRTSubtitle SRTTiming
timing = lens (\ SRTSubtitle { _timing = t } → t)
              (\ subt t → subt { _timing = t })

subtitle ∷ Lens' SRTSubtitle SRTSubtitleText
subtitle = lens (\ SRTSubtitle { _subtitle = t } → t)
                (\ subt t → subt { _subtitle = t })


instance TFunctor SRTSubtitle where
  tmap ∷ (Text → Text) → SRTSubtitle → SRTSubtitle
  tmap f (SRTSubtitle i t s) = SRTSubtitle i t (f `tmap` s)

instance Shifty SRTSubtitle where
  shift ∷ Duration → Skew → SRTSubtitle → SRTSubtitle
  shift off sf subt = subt & timing ⊧ (shift off sf)

instance Printable SRTSubtitle where
  print (SRTSubtitle i t s) = P.text $ intercalate "\n" [ toText i
                                                        , toText t
                                                        , toText s
                                                        ]

instance Textual SRTSubtitle where
  textual = SRTSubtitle ⊳ nnBounded Decimal ⋪ whitespaces ⋪ nl
                        ⊵ textual ⋪ whitespaces ⋪ nl
                        ⊵ textual

instance Parsecable SRTSubtitle where
  parser = textual

instance Arbitrary SRTSubtitle where
  arbitrary = SRTSubtitle ⊳ arbitrary ⊵ arbitrary ⊵ arbitrary

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test data -----------------------------------------------

srtSubtitle ∷ Text
srtSubtitle = unlines
  [ "1"
  , "00:00:01,000 --> 00:00:04,074\r"
  , "Subtitles downloaded from www.OpenSubtitles.org\r"
  ]

srtSubtitleRef ∷ SRTSubtitle
srtSubtitleRef =
  let expectText =
        SRTSubtitleText $
            unlines [ "Subtitles downloaded from www.OpenSubtitles.org" ]
      expectTimeStampBegin = 1_000
      expectTimeStampEnd   = 4_074
      expectTiming = SRTTiming expectTimeStampBegin expectTimeStampEnd
   in SRTSubtitle 1 expectTiming expectText

------------------------------------------------------------

tests ∷ TestTree
tests =
  testGroup "SRTSubtitle"
            [ testCase "fromText" $ Just srtSubtitleRef @=? fromText srtSubtitle
            , testCase "toText"   $
                  filter (≢'\r') srtSubtitle ≟ toText srtSubtitleRef
            , testCase "parsec"   $
                    Right srtSubtitleRef
                @=? parsec @SRTSubtitle @ParseError @(Either ParseError)
                           @Text @String "srtTimestamp" srtSubtitle
            , testProperty "invertibleText" (propInvertibleText @SRTSubtitle)
            , testCase "shift" $
                    srtSubtitleRef { _timing = SRTTiming 1530 4665 }
                  ≟ shift (MS 500) (MS_S 20) srtSubtitleRef
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

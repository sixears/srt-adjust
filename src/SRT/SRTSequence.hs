{-# LANGUAGE InstanceSigs       #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE UnicodeSyntax      #-}

module SRT.SRTSequence
  ( tests )
where

-- base --------------------------------

import qualified  Data.List

import Data.Bool      ( Bool )
import Data.Either    ( Either( Left, Right ) )
import Data.Eq        ( Eq )
import Data.Function  ( ($) )
import Data.Maybe     ( Maybe( Just  ) )
import Data.String    ( String )
import System.Exit    ( ExitCode )
import System.IO      ( IO )
import Text.Show      ( Show )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≢) )
import Data.Function.Unicode  ( (∘) )
import Data.Monoid.Unicode    ( (⊕) )

-- data-textual ------------------------

import Data.Textual             ( Parsed( Malformed, Parsed )
                                , Printable( print ) , Textual( textual )
                                , fromText, parseText, toText
                                )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFunctor( omap ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⋫))
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Natural      ( ℕ )
import Data.MoreUnicode.Tasty        ( (≟) )

-- parsec-plus -------------------------

import ParsecPlus  ( ParseError )
import ParsecPlus  ( Parsecable( parsec, parser ) )

-- parser-plus -------------------------

import ParserPlus  ( nl, utf8BOM )

-- parsers -----------------------------

import Text.Parser.Combinators  ( sepEndBy, skipOptional )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary ( Arbitrary( arbitrary ) )
import Test.QuickCheck.Gen       ( listOf )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( testCase )

-- tasty-plus --------------------------

import TastyPlus  ( assertListEq, assertListEqR, propInvertibleText, runTestsP
                  , runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( testProperty )

-- text --------------------------------

import Data.Text     ( Text, filter, intercalate, isInfixOf, unlines )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Duration             ( Duration( MS ) )
import SRT.Shifty           ( Shifty( shift ) )
import SRT.Skew             ( Skew( MS_S ) )
import SRT.SRTSubtitle      ( SRTSubtitle( SRTSubtitle ), subtitle, timing )
import SRT.SRTSubtitleText  ( SRTSubtitleText( SRTSubtitleText
                                             , unSRTSubtitleText ) )
import SRT.SRTTiming        ( SRTTiming( SRTTiming ) )
import SRT.TFunctor         ( TFunctor( tmap ) )

--------------------------------------------------------------------------------

data SRTSequence = SRTSequence { unSRTSequence ∷ [SRTSubtitle] }
  deriving (Eq, Show)

type instance Element SRTSequence = Text

instance MonoFunctor SRTSequence where
  omap ∷ (Text → Text) → SRTSequence → SRTSequence
  omap f (SRTSequence ss) = SRTSequence ((f `tmap`) ⊳ ss)

instance TFunctor SRTSequence where
  tmap f (SRTSequence ss) = SRTSequence ((f `tmap`) ⊳ ss)

instance Shifty SRTSequence where
  shift ∷ Duration → Skew → SRTSequence → SRTSequence
  shift off sf (SRTSequence subts) = SRTSequence $ shift off sf ⊳ subts

instance Printable SRTSequence where
  print (SRTSequence ss) = P.text $ intercalate "\n" $ toText ⊳ ss

instance Textual SRTSequence where
  textual = SRTSequence ⊳
              (skipOptional utf8BOM ⋫ (textual `sepEndBy` nl))

instance Parsecable SRTSequence where
  parser = textual

instance Arbitrary SRTSequence where
  arbitrary = SRTSequence ⊳ listOf arbitrary

find ∷ (Text → Bool) → SRTSequence → [SRTTiming]
find p seq =
  view timing ⊳ Data.List.filter (p ∘ unSRTSubtitleText ∘ view subtitle)
                                 (unSRTSequence seq)

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test data -----------------------------------------------

srtSequenceT ∷ Text
srtSequenceT = unlines
  [ "1\r"
  , "00:00:01,000 --> 00:00:04,074\r" -- and some carriage-returns :-(
  , "Subtitles downloaded from www.OpenSubtitles.org\r"
  ]

srtSequenceS ∷ Text
srtSequenceS = unlines
  [ "\65279\&1\r" -- add UTF-8 BOM, since so many files include it
  , "00:00:01,000 --> 00:00:04,074\r" -- and some carriage-returns :-(
  , "Subtitles downloaded from www.OpenSubtitles.org\r"
  ]

srtSequenceSRef ∷ SRTSequence
srtSequenceSRef =
  SRTSequence [ SRTSubtitle 1 (SRTTiming 1_000 4_074)
                            "Subtitles downloaded from www.OpenSubtitles.org\n"
              ]

srtSequence ∷ Text
srtSequence = unlines
  [ "\65279\&1\r" -- add UTF-8 BOM, since so many files include it
  , "00:00:01,000 --> 00:00:04,074\r" -- and some carriage-returns :-(
  , "Subtitles downloaded from www.OpenSubtitles.org\r"
  , ""
  , "2"
  , "00:00:35,935 --> 00:00:37,346"
  , "This is Benjamin Mee."
  , ""
  , "3"
  , "00:00:37,436 --> 00:00:41,612"
  , "I am surrounded by hundreds,"
  , "probably thousands of killer bees."
  , ""
  , "4"
  , "00:00:41,740 --> 00:00:45,381"
  , "If I wasn't wearing this suit,"
  , "I would be dead in an instant!"
  , ""
  , "5"
  , "00:00:45,778 --> 00:00:48,691"
  , "<i>May I have"
  , "your attention, please?</i>"
  ]

srtSequenceRef ∷ SRTSequence
srtSequenceRef =
  let text3 = SRTSubtitleText $ unlines [ "I am surrounded by hundreds,"
                                        , "probably thousands of killer bees." ]
      text4 = SRTSubtitleText $ unlines [ "If I wasn't wearing this suit,"
                                        , "I would be dead in an instant!" ]
      text5 = SRTSubtitleText $ unlines [ "<i>May I have"
                                        , "your attention, please?</i>" ]

   in SRTSequence [ SRTSubtitle 1 (SRTTiming 1_000 4_074)
                             "Subtitles downloaded from www.OpenSubtitles.org\n"
                  , SRTSubtitle 2 (SRTTiming 35_935 37_346)
                                "This is Benjamin Mee.\n"
                  , SRTSubtitle 3 (SRTTiming 37_436 41_612)
                                text3
                  , SRTSubtitle 4 (SRTTiming 41_740 45_381)
                                text4
                  , SRTSubtitle 5 (SRTTiming 45_778 48_691)
                                text5
                  ]


  {- 37,436 → 38; 45,778 → 47
   Distance between original points: 8.342s (t2-t1)
   Distance between target points: 9s (m2-m1)
   Original shift: +564ms (m1-t1)
   Target shift: +1222ms (m2-t2)

   Slew:
   Gain 658ms (m2-t2-m1+t1) in 8.342 seconds = 0.079 s/s = 79 ms/s (m2-t2-m1+t1)/(t2-t1)

   m1 = (t1+off)*slew; off=(m1/slew) - t1
   Offset = -2218
 -}

srtSequenceRefShifted ∷ SRTSequence
srtSequenceRefShifted =
  let text3 = SRTSubtitleText $ unlines [ "I am surrounded by hundreds,"
                                        , "probably thousands of killer bees." ]
      text4 = SRTSubtitleText $ unlines [ "If I wasn't wearing this suit,"
                                        , "I would be dead in an instant!" ]
      text5 = SRTSubtitleText $ unlines [ "<i>May I have"
                                        , "your attention, please?</i>" ]

   in SRTSequence [ SRTSubtitle 1 (SRTTiming 2_020 5_125)
                             "Subtitles downloaded from www.OpenSubtitles.org\n"
                  , SRTSubtitle 2 (SRTTiming 37_304 38_729)
                                "This is Benjamin Mee.\n"
                  , SRTSubtitle 3 (SRTTiming 38_820 43_038)
                                text3
                  , SRTSubtitle 4 (SRTTiming 43_167 46_845)
                                text4
                  , SRTSubtitle 5 (SRTTiming 47_246 50_188)
                                text5
                  ]

------------------------------------------------------------

tests ∷ TestTree
tests =
  let parsedE ∷ Parsed β → Either ([String],String) β
      parsedE z = case z of Parsed a → Right a; Malformed xs x → Left (xs,x)
      filtCR  = filter (≢ '\r')
      filtBOM = filter (≢ '\65279')
   in testGroup "SRTSequence" $
                  [ testCase "fromText (T)" $
                          Just (filtCR `tmap` srtSequenceSRef)
                        ≟ fromText srtSequenceT
                  , testCase "toText (T)"   $
                        filtCR srtSequenceT ≟  toText srtSequenceSRef
                  , testCase "fromText (S)" $
                          Just (filtCR `tmap` srtSequenceSRef)
                        ≟ fromText srtSequenceS
                  , testCase "toText (S)"   $
                        filtBOM (filtCR srtSequenceS) ≟ toText srtSequenceSRef
                  ]
                ⊕ assertListEqR "fromText"
                              (unSRTSequence ⊳ (parsedE(parseText srtSequence)))
                              (unSRTSequence srtSequenceRef)
                ⊕ [ testCase "toText"   $
                        filtBOM (filtCR srtSequence) ≟ toText srtSequenceRef
                  , testCase "parsec"   $
                          Right srtSequenceRef
                        ≟ parsec @SRTSequence @ParseError @(Either ParseError)
                                 @Text @String "srtTimestamp" srtSequence
                  , testProperty "invertibleText"
                                 (propInvertibleText @SRTSequence)
                  ]
                ⊕ assertListEq "shift" (unSRTSequence srtSequenceRefShifted)
                    (unSRTSequence (shift (MS 1000) (MS_S 10) srtSequenceRef))
                ⊕ [ testCase "find" $
                        [SRTTiming 37_436 41_612]
                      ≟ find (isInfixOf "hundreds") srtSequenceRef
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

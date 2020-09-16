{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UnicodeSyntax              #-}

module SRT.SRTSubtitleText
  ( SRTSubtitleText( SRTSubtitleText, unSRTSubtitleText ), tests )
where

-- base --------------------------------

import Control.Applicative  ( many, some )
import Data.Bool            ( Bool, not )
import Data.Char            ( Char )
import Data.Either          ( Either( Right ) )
import Data.Eq              ( Eq )
import Data.Function        ( ($) )
import Data.List            ( elem )
import Data.Maybe           ( Maybe( Just ) )
import Data.String          ( IsString, String )
import System.Exit          ( ExitCode )
import System.IO            ( IO )
import Text.Show            ( Show )

-- base-unicode-symbols ----------------

import Data.Bool.Unicode      ( (∨) )
import Data.Eq.Unicode        ( (≢) )
import Data.Function.Unicode  ( (∘) )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ), Textual( textual ), fromText,toText )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋪), (⋫) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Natural      ( ℕ )

-- parsec-plus -------------------------

import ParsecPlus  ( Parsecable( parsec, parser ), ParseError )

-- parser-plus -------------------------

import ParserPlus  ( nl, whitespaces )

-- parsers -----------------------------

import Text.Parser.Char  ( noneOf )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary ( Arbitrary( arbitrary ) )
import Test.QuickCheck.Gen       ( Gen, listOf1, suchThat )
import Test.QuickCheck.Modifiers ( PrintableString( getPrintableString ) )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( (@=?), testCase )

-- tasty-plus --------------------------

import TastyPlus  ( (≟), propInvertibleText, runTestsP, runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( testProperty )

-- text --------------------------------

import Data.Text  ( Text, filter, head, null, pack, unlines )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.TFunctor  ( TFunctor( tmap ) )

--------------------------------------------------------------------------------

type 𝔹 = Bool

------------------------------------------------------------

newtype SRTSubtitleText = SRTSubtitleText { unSRTSubtitleText ∷ Text }
  deriving (Eq, IsString, Show)

instance TFunctor SRTSubtitleText where
  tmap ∷ (Text → Text) → SRTSubtitleText → SRTSubtitleText
  tmap f (SRTSubtitleText t) = SRTSubtitleText (f t)

instance Printable SRTSubtitleText where
  print (SRTSubtitleText t) = P.text t

instance Textual SRTSubtitleText where
  textual = SRTSubtitleText ⊳ unlines ⊳
              some (pack ⊳ ((:) ⊳ (whitespaces ⋫ noneOf " \t\n\v\r")
                                ⊵ many (noneOf "\n\r") ⋪ nl))

instance Parsecable SRTSubtitleText where
  parser = textual

instance Arbitrary SRTSubtitleText where
  arbitrary ∷ Gen SRTSubtitleText
  -- create a list of texts, none beginning with a space, none containing a
  -- newline; and join them with a newline (incl. a terminating newline)
  arbitrary = let isValidLine ∷ Text → 𝔹
                  isValidLine t = not (null t ∨ (head t `elem` (" \t"∷ [Char])))
                  genPrintableText ∷ Gen Text
                  genPrintableText = pack ∘ getPrintableString ⊳ arbitrary
                  genLine ∷ Gen Text
                  genLine = suchThat (filter (≢ '\n') ⊳ genPrintableText)
                                     isValidLine
               in SRTSubtitleText ∘ unlines ⊳ listOf1 genLine

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test data -----------------------------------------------

srtSubtitleText ∷ Text
srtSubtitleText = unlines
  [ "Subtitles downloaded from www.OpenSubtitles.org"
  , "Deklan, that's enough."
  ]

srtSubtitleTextRef ∷ SRTSubtitleText
srtSubtitleTextRef =
  SRTSubtitleText $ unlines [ "Subtitles downloaded from www.OpenSubtitles.org"
                            , "Deklan, that's enough." ]

------------------------------------------------------------

tests ∷ TestTree
tests =
  testGroup "SRTSubtitleText"
            [ testCase "fromText" $
                    Just srtSubtitleTextRef @=? fromText srtSubtitleText
            , testCase "toText"   $ srtSubtitleText ≟ toText srtSubtitleTextRef
            , testCase "parsec"   $
                    Right srtSubtitleTextRef
                @=? parsec @SRTSubtitleText @ParseError @(Either ParseError)
                           @Text @String "srtTimestamp" srtSubtitleText
            , testProperty "invertibleText"
                           (propInvertibleText @SRTSubtitleText)
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

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}

module SRT.T.Tests
  ( tests )
where

-- base --------------------------------

import Data.String  ( String )
import System.Exit  ( ExitCode )
import System.IO    ( IO )

-- more-unicode ------------------------

import Data.MoreUnicode.Natural  ( ℕ )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-plus --------------------------

import TastyPlus  ( runTestsP, runTestsReplay, runTestTree )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import qualified  SRT.SRTAdjust
import qualified  SRT.SRTTimeStamp
import qualified  SRT.SRTTiming
import qualified  SRT.SRTSequence
import qualified  SRT.SRTSubtitle
import qualified  SRT.SRTSubtitleText

--------------------------------------------------------------------------------

tests ∷ TestTree
tests = testGroup "srt-adjust" [ SRT.SRTAdjust.tests
                               , SRT.SRTTimeStamp.tests
                               , SRT.SRTTiming.tests
                               , SRT.SRTSequence.tests
                               , SRT.SRTSubtitle.tests
                               , SRT.SRTSubtitleText.tests
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

{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE QuasiQuotes        #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE UnicodeSyntax      #-}

module SRT.SRTAdjust
  ( optionsAdjust, tests )
where

import Prelude  ( Fractional( (/) ), Num( (+), (-), (*) ), (/) ) 

-- base --------------------------------

import Control.Monad  ( return, when )
import Data.Either    ( Either( Right ) )
import Data.Function  ( ($) )
import Data.Maybe     ( Maybe( Just, Nothing ) )
import Data.String    ( String )
import System.Exit    ( ExitCode )
import System.IO      ( IO )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≡) )
import Data.Function.Unicode  ( (∘) )

-- duration ----------------------------

import Duration  ( Duration )
import Duration  ( Duration( MS ), asMilliseconds )

-- fpath -------------------------------

import FPath.AsFilePath  ( filepath )
import FPath.File        ( File )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( AsIOError, IOError, userE )

-- more-unicode ------------------------

-- more-unicode ------------------------

import Data.MoreUnicode.Lens     ( (⊣), (⫥) )
import Data.MoreUnicode.Natural  ( ℕ )
import Data.MoreUnicode.Tasty    ( (≟) )

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError, throwError )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( testCase )

-- tasty-plus --------------------------

import TastyPlus  ( runTestsP, runTestsReplay, runTestTree )

-- text --------------------------------

import Data.Text  ( isInfixOf )

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.SRTAdjust.Types    ( AdjustmentOpts( AdjDelOff, AdjMarkers ), Marker
                              , position, mtext )

import SRT.Shifty             ( Shifty( shift ) )
import SRT.Skew               ( Skew( MS_S, Skew ) )
import SRT.SRTSequence        ( SRTSequence, find )
import SRT.SRTTimeStamp       ( SRTTimeStamp( unSRTTimeStamp ) )
import SRT.SRTTiming          ( SRTTiming( SRTTiming ) )


--------------------------------------------------------------------------------

findMarker ∷ (AsIOError ε, MonadError ε η) ⇒
             Marker → SRTSequence → Maybe File → η SRTTiming
findMarker m seq fn =
  let mt = m ⊣ mtext
      inf = case fn of Just f  → [fmt| in '%s'|] (f ⫥ filepath); Nothing → ""
  in case find (isInfixOf (m ⊣ mtext)) seq of
       []  → throwError ∘ userE $ [fmt|text '%t' not found%s|] mt inf
       [x] → return x
       xs  → throwError ∘ userE $ [fmt|text '%t' found multiple times%s (%L)|]
                                  mt inf xs

----------------------------------------

calcShift ∷ (AsIOError ε, MonadError ε η) ⇒
            SRTTimeStamp → SRTTimeStamp → SRTTimeStamp → SRTTimeStamp
          → η (Skew, Duration)

calcShift t1 t2 m1p m2p = do
  when (m1p ≡ m2p) $
    throwError (userE $ [fmt|two positions with the same value! (%T)|] m1p)
  let off = (m2p*t1-m1p*t2) / (m1p-m2p)
      sf  = unSRTTimeStamp (m2p / (off+t2)) ⊣ asMilliseconds
  return (Skew sf, unSRTTimeStamp off)

----------------------------------------

optionsAdjust ∷ (AsIOError ε, MonadError ε η) ⇒
                SRTSequence → Maybe File → AdjustmentOpts
              → η (Skew, Duration)
optionsAdjust _ _ (AdjDelOff  d  o)  = return (d,o)
optionsAdjust seq fn (AdjMarkers m1 (Just m2)) = do
  (SRTTiming t1 _) ← findMarker m1 seq fn
  (SRTTiming t2 _) ← findMarker m2 seq fn
  {- So, t1 is the incoming position of text m1.  t2 is the incoming position of
     text m2.  We want to shift t1,t2 to the timestamps of m1,m2 respectively.
     Thus, m1 = speedfactor * (offset+t1); m2 = speedfactor * (offset+t2)
           m1/(offset+t1)   = speedfactor = m2/(offset+t2)

           m1 * (offset+t2) = m2 * (offset+t1)
           m1*offset + m1*t2 = m2*offset + m2*t1
           offset * (m1-m2) = m2*t1 - m1*t2
           offset = (m2*t1 - m1*t2) / (m1-m2)
   -}
  let m1p = m1 ⊣ position
      m2p = m2 ⊣ position
  calcShift t1 t2 m1p m2p

optionsAdjust seq fn (AdjMarkers mkr Nothing) = do
  (SRTTiming t _) ← findMarker mkr seq fn
  return (MS_S 0, unSRTTimeStamp (mkr ⊣ position - t))

----------

optionsAdjustTests ∷ TestTree
optionsAdjustTests =
  let
   in testGroup "optionsAdjust"
                [ testCase "just offset (1)" $
                      Right (MS_S 0, MS 1000)
                    ≟ calcShift @IOError 10_000 20_000 11_000 21_000
                , testCase "just offset (2)" $
                      Right (MS_S 0, MS 2000)
                    ≟ calcShift @IOError 10_000 20_000 12_000 22_000
                , testCase "offset shift (1)" $
                      let Right (skew,off) = calcShift @IOError 10_000 20_000
                                                                12_000 22_000
                       in do 12_000 ≟ shift off skew (10_000 ∷ SRTTimeStamp)
                             22_000 ≟ shift off skew (20_000 ∷ SRTTimeStamp)
                , testCase "just skew (1)" $
                      Right (MS_S 100, MS 0)
                    ≟ calcShift @IOError 10_000 20_000 11_000 22_000
                , testCase "just skew (2)" $
                      Right (MS_S 200, MS 0)
                    ≟ calcShift @IOError 10_000 20_000 12_000 24_000
                , testCase "real world" $
                    let t1 = 37_436
                        t2 = 45_778
                        m1 = 38_000
                        m2 = 47_000
                        Right (skew,off) = calcShift @IOError t1 t2 m1 m2
                     in do m1 ≟ shift off skew (t1 ∷ SRTTimeStamp)
                           m2 ≟ shift off skew (t2 ∷ SRTTimeStamp)
                ]

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

tests ∷ TestTree
tests = testGroup "SRTAdjust" [ optionsAdjustTests ]
                
----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------

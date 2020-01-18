-- {-# LANGUAGE FlexibleContexts      #-}
-- {-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
-- {-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UnicodeSyntax         #-}

-- TODO:
-- split out components
-- add completion for duration/timestamp?
-- add completion for marker texts?

import Prelude  ( Fractional( (/) ), Int, Num( (+), (-), (*) ), (/), floor ) 

-- base --------------------------------

import Control.Exception  ( Exception )
import Control.Monad      ( forM_, return, when )
import Data.Either        ( Either( Right ) )
import Data.Eq            ( Eq )
import Data.Function      ( ($) )
import Data.Maybe         ( Maybe( Just, Nothing ) )
import Data.String        ( String )
import System.Exit        ( ExitCode( ExitSuccess ) )
import System.IO          ( IO, hSetEncoding, stdin, utf8 )
import Text.Show          ( Show )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≡) )
import Data.Function.Unicode  ( (∘) )
import Prelude.Unicode        ( ℤ )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ) )

-- duration ----------------------------

import Duration  ( Duration( MS ), asMilliseconds )

-- exited ------------------------------

import Exited  ( doMain )

-- fluffy ------------------------------

import Fluffy.Options  ( parseOpts )

-- fpath -------------------------------

import FPath.AsFilePath        ( filepath )
import FPath.Error.FPathError  ( AsFPathError( _FPathError ), FPathError
                               , FPathIOError, _FPIO_IO_ERROR,_FPIO_PATH_ERROR )
import FPath.File              ( File )

-- lens --------------------------------

import Control.Lens.Prism   ( Prism', prism' )

-- monaderror-io -----------------------

import MonadError           ( ѥ )
import MonadError.IO.Error  ( AsIOError( _IOError ), IOError, userE )

-- monadio-plus ------------------------

import MonadIO  ( MonadIO, liftIO, say, warn )

-- more-unicode ------------------------

import Data.MoreUnicode.Functor  ( (⊳) )
import Data.MoreUnicode.Lens     ( (⊣), (⫥) )
import Data.MoreUnicode.Natural  ( ℕ )
import Data.MoreUnicode.Tasty    ( (≟) )

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError, throwError )

-- parsec-plus -------------------------

import ParsecPlus  ( AsParseError( _ParseError ), IOParseError, ParseError )
import ParsecPlus  ( Parsecable( parsec ), parsecFileUTF8 )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( testCase )

-- tasty-plus --------------------------

import TastyPlus  ( runTestsP, runTestsReplay, runTestTree )

-- text --------------------------------

import Data.Text     ( Text, isInfixOf )
import Data.Text.IO  ( hGetContents )

-- tfmt --------------------------------

import Text.Fmt  ( fmt, fmtT )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.SRTAdjust.Options  ( AdjustmentOpts( AdjDelOff, AdjMarkers )
                              , Marker
                              , adj, infns, mtext, parseOptions, position
                              )
import SRT.Shifty             ( Shifty( shift ) )
import SRT.Skew               ( Skew( MS_S, Skew ), to_ms_s )
import SRT.SRTSequence        ( SRTSequence, find )
import SRT.SRTTimeStamp       ( SRTTimeStamp( unSRTTimeStamp ) )
import SRT.SRTTiming          ( SRTTiming( SRTTiming ) )

--------------------------------------------------------------------------------

------------------------------------------------------------

-- factor out run, etc. (to ProcLib?)
-- make ProcLib Errors to be Exceptions

pf ∷ File → IO (Either IOParseError SRTSequence)
pf f = ѥ (parsecFileUTF8 f)

pf' ∷ (MonadIO μ, MonadError IOParseError η) ⇒ File → μ (η SRTSequence)
pf' f = ѥ (parsecFileUTF8 f)

pf'' ∷ (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε η, Parsecable α) ⇒
       File → μ (η α)
pf'' f = ѥ (parsecFileUTF8 f)

pf''' ∷ (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε μ, Parsecable α) ⇒
        File → μ α
pf''' f = parsecFileUTF8 f

pf_ ∷ (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε μ) ⇒
      File → μ SRTSequence
pf_ f = parsecFileUTF8 f

pf__ ∷ (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε μ) ⇒
        Maybe File → μ SRTSequence
pf__ mf = case mf of
           Just f  → parsecFileUTF8 f
-- EMBED THIS INTO PARSECFILEUTF8
           Nothing → do -- MAKE THIS GETUTF8CONTENTS
                        liftIO $ hSetEncoding stdin utf8
                        txt ← liftIO $ hGetContents stdin
                        parsec ("stdin" ∷ Text) txt

------------------------------------------------------------

data FPathIOParseError = FPIOP_FPATHIOERROR FPathIOError
                       | FPIOP_PARSEERROR   ParseError
  deriving (Eq, Show)

_FPIOP_FPATHIOERROR ∷ Prism' FPathIOParseError FPathIOError
_FPIOP_FPATHIOERROR = prism' (\ e → FPIOP_FPATHIOERROR e)
                             (\ case FPIOP_FPATHIOERROR e → Just e; _ → Nothing)

_FPIOP_PARSEERROR ∷ Prism' FPathIOParseError ParseError
_FPIOP_PARSEERROR = prism' (\ e → FPIOP_PARSEERROR e)
                           (\ case FPIOP_PARSEERROR e → Just e; _ → Nothing)

instance Exception FPathIOParseError

instance AsIOError FPathIOParseError where
  _IOError = _FPIOP_FPATHIOERROR ∘ _FPIO_IO_ERROR

instance AsFPathError FPathIOParseError where
  _FPathError ∷ Prism' FPathIOParseError FPathError
  _FPathError = _FPIOP_FPATHIOERROR ∘ _FPIO_PATH_ERROR

instance AsParseError FPathIOParseError where
  _ParseError ∷ Prism' FPathIOParseError ParseError
  _ParseError = prism' FPIOP_PARSEERROR
                       (\ case FPIOP_PARSEERROR e → Just e; _ → Nothing)

instance Printable FPathIOParseError where
  print (FPIOP_FPATHIOERROR e) = print e
  print (FPIOP_PARSEERROR   e) = print e

------------------------------------------------------------

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


calcShift ∷ (AsIOError ε, MonadError ε η) ⇒
            SRTTimeStamp → SRTTimeStamp → SRTTimeStamp → SRTTimeStamp
          → η (Skew, Duration)

calcShift t1 t2 m1p m2p = do
  when (m1p ≡ m2p) $
    throwError (userE $ [fmt|two positions with the same value! (%T)|] m1p)
  let off = (m2p*t1-m1p*t2) / (m1p-m2p)
      sf  = unSRTTimeStamp (m2p / (off+t2)) ⊣ asMilliseconds
  return (Skew sf, unSRTTimeStamp off)
-- NOW REVIEW TimeStamp ARITHMETIC.  SPECIALIST OPERATORS FOR ADDING DURATION,MULT, etc.?


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
                      let Right (skew,off) = calcShift @IOError 10_000 20_000 12_000 22_000
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



main ∷ IO ()
main = doMain @FPathIOParseError $ do
  opts ← parseOpts Nothing "greet thee all" parseOptions

  let fns = case opts ⊣ infns of
              [] → [Nothing] -- read stdin
              xs → Just ⊳ xs

  forM_ fns $ \ fn → do
    seq ← pf__ fn

    (del,off) ← optionsAdjust seq fn $ opts ⊣ adj
      -- ADD MODE TO SHOW CALC BUT DO NOTHING
    let MS off_ms = off
    warn $ [fmtT|Using offset %dms, delay %fms/s|] (floor @_ @Int off_ms)
                                                   (to_ms_s del)

    say $ shift off del seq


  return ExitSuccess

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

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

two ∷ ℤ
two = 2

three ∷ ℤ
three = 3

----------------------------------------

tests ∷ TestTree
tests = testGroup "srt-adjust" [ optionsAdjustTests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------

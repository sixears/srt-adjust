-- {-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
-- {-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE OverloadedStrings          #-}
-- {-# LANGUAGE PatternSynonyms            #-}

-- do we need this?  can we get rid of the foralls?
-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE QuasiQuotes                #-}
-- {-# LANGUAGE ScopedTypeVariables        #-}
-- {-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UnicodeSyntax              #-}
-- {-# LANGUAGE ViewPatterns               #-}

-- TODO:
-- split out components
-- add completion for duration/timestamp?
-- add completion for marker texts?

import Prelude  ( Fractional( (/) ), Int, Num( (+), (-), (*) ), (/), floor ) 

-- base --------------------------------

import qualified  Data.List

import Control.Applicative  ( many )
import Control.Exception    ( Exception )
import Control.Monad        ( forM_, return, when )
import Data.Bifunctor       ( bimap )
import Data.Bool            ( Bool )
import Data.Char            ( Char )
import Data.Either          ( Either( Left, Right ) )
import Data.Eq              ( Eq )
import Data.Function        ( ($), (&) )
import Data.Maybe           ( Maybe( Just, Nothing ) )
import Data.String          ( String )
import Data.Word            ( Word32 )
import System.Exit          ( ExitCode( ExitSuccess ) )
import System.IO            ( IO, hSetEncoding, stdin, utf8 )
import Text.Show            ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≡), (≢) )
import Data.Function.Unicode  ( (∘) )
import Data.Monoid.Unicode    ( (⊕) )
import Prelude.Unicode        ( ℚ, ℤ )

-- data-textual ------------------------

import Data.Textual             ( Parsed( Malformed, Parsed )
                                , Printable( print ) , Textual( textual )
                                , fromText, parseText, toText
                                )
import Data.Textual.Fractional  ( Optional( Optional ), decExpSign, fractional'
                                , optSign )
import Data.Textual.Integral    ( Decimal( Decimal ), nnBounded )

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

import Control.Lens.Getter  ( view )
import Control.Lens.Lens    ( Lens', lens )
import Control.Lens.Prism   ( Prism', prism' )

-- monaderror-io -----------------------

import MonadError           ( ѥ )
import MonadError.IO.Error  ( AsIOError( _IOError ), IOError, userE )

-- monadio-plus ------------------------

import MonadIO  ( MonadIO, liftIO, say, warn )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFunctor( omap ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋪), (⋫), (∤) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Lens         ( (⊣), (⊧), (⫥) )
import Data.MoreUnicode.Monoid       ( ф, ю )
import Data.MoreUnicode.Natural      ( ℕ )
import Data.MoreUnicode.Tasty        ( (≟) )

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError, throwError )

-- optparse-plus -----------------------

import OptParsePlus  ( argT, optT )

-- options-applicative -----------------

import Options.Applicative  ( ArgumentFields, Mod, Parser, ReadM
                            , action, eitherReader, long, metavar, option
                            , optional, pure, short, value
                            )

-- parsec ------------------------------

import Text.Parsec.Prim  ( ParsecT, Stream, parse )

-- parsers -----------------------------

import Text.Parser.Char         ( anyChar, char, string )
import Text.Parser.Combinators  ( sepEndBy, skipOptional )

-- parsec-plus -------------------------

import ParsecPlus  ( AsParseError( _ParseError ), IOParseError, ParseError )
import ParsecPlus  ( Parsecable( parsec, parser ), parsecFileUTF8 )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary ( Arbitrary( arbitrary ) )
import Test.QuickCheck.Gen       ( listOf )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( testCase )

-- tasty-plus --------------------------

import TastyPlus  ( assertListEqR, assertListEq, propInvertibleText, runTestsP
                  , runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( testProperty )

-- text --------------------------------

import Data.Text     ( Text, filter, intercalate, isInfixOf, pack, unlines )
import qualified  Data.Text.IO  as  TextIO

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt, fmtT )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.ParserHelp      ( nl, whitespaces )
import SRT.Shifty          ( Shifty( shift ) )
import SRT.TFunctor        ( TFunctor( tmap ) )

import SRT.Skew            ( Skew( MS_S, Skew ), to_ms_s )
import SRT.SRTSubtitleText ( SRTSubtitleText( SRTSubtitleText
                                            , unSRTSubtitleText ) )
import SRT.SRTTimeStamp    ( SRTTimeStamp( unSRTTimeStamp ) )
import SRT.SRTTiming       ( SRTTiming( SRTTiming ) )

--------------------------------------------------------------------------------

-- type 𝔹 = Bool

(⧐) ∷ MonoFunctor mono ⇒ (Element mono → Element mono) → mono → mono
(⧐) = omap

-- `Text.Parser.Char.spaces` parses *all* spaces, including newline.  That's not
-- what we need for parsing/skipping spaces at the end of the line, hence this
-- function
-- whitespaces ∷ CharParsing η ⇒ η String
-- whitespaces = many $ oneOf " \t"

-- Parse a newline, optionally preceded by a carriage-return
-- (flucking windoze...)
-- nl ∷ (CharParsing η, Monad η) ⇒ η ()
-- nl = skipOptional (char '\r') ⋫ char '\n' ⋫ return () <?> "cr/nl"

------------------------------------------------------------

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


-- type instance Element SRTSubtitle = SRTTimeStamp

{-
instance MonoFunctor SRTSubtitle where
  omap ∷ (Text → Text) → SRTSubtitle → SRTSubtitle
  omap f (SRTSubtitle i t s) = SRTSubtitle i t (f `tmap` s)
-}

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

--------------------

srtSubtitleTests ∷ TestTree
srtSubtitleTests =
  testGroup "SRTSubtitle"
            [ testCase "fromText" $ Just srtSubtitleRef ≟ fromText srtSubtitle
            , testCase "toText"   $
                  filter (≢'\r') srtSubtitle ≟ toText srtSubtitleRef
            , testCase "parsec"   $
                    Right srtSubtitleRef
                  ≟ parsec @SRTSubtitle @ParseError @(Either ParseError)
                           @Text @String "srtTimestamp" srtSubtitle
            , testProperty "invertibleText" (propInvertibleText @SRTSubtitle)
            , testCase "shift" $
                    srtSubtitleRef { _timing = SRTTiming 1530 4665 }
                  ≟ shift (MS 500) (MS_S 20) srtSubtitleRef
            ]

------------------------------------------------------------

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
              (skipOptional (string "\65279") ⋫ (textual `sepEndBy` nl))

instance Parsecable SRTSequence where
  parser = textual

instance Arbitrary SRTSequence where
  arbitrary = SRTSequence ⊳ listOf arbitrary

find ∷ (Text → Bool) → SRTSequence → [SRTTiming]
find p seq =
  view timing ⊳ Data.List.filter (p ∘ unSRTSubtitleText ∘ view subtitle)
                                 (unSRTSequence seq)

--------------------

srtSequenceTests ∷ TestTree
srtSequenceTests =
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

------------------------------------------------------------
--                        Options                         --
------------------------------------------------------------

data RunTests = NoRunTests | RunTests

data Marker = Marker { _position ∷ SRTTimeStamp, _mtext ∷ Text }
  deriving (Eq,Show)

mtext ∷ Lens' Marker Text
mtext = lens _mtext (\ m t → m { _mtext = t })

position ∷ Lens' Marker SRTTimeStamp
position = lens _position (\ m p → m { _position = p })

instance Printable Marker where
  print (Marker pos txt) = P.text $ [fmt|%T=%t|] pos txt

instance Printable (Maybe Marker) where
  print (Just m) = print m
  print Nothing  = P.text "--"

instance Textual Marker where
  textual = Marker ⊳ textual ⊵ char '=' ⋫ (pack ⊳ many anyChar)

data AdjustmentOpts = AdjDelOff  { _d ∷ Skew  , _o ∷ Duration }
                    | AdjMarkers { _m1 ∷ Marker, _m2 ∷ Maybe Marker }

data Options = Options { _infns   ∷ [File]
                       , _adj ∷ AdjustmentOpts
                       }

infns ∷ Lens' Options [File]
infns = lens _infns (\ o is → o { _infns = is })

adj ∷ Lens' Options AdjustmentOpts
adj = lens _adj (\ o a → o { _adj = a })

parseMarkers ∷ Parser AdjustmentOpts
parseMarkers = let parseMarker ∷ Parser Marker
                   parseMarker =
--                     option readT (long "marker" ⊕ short 'm'
                     optT (long "marker" ⊕ short 'm' ⊕ metavar "TIMESTAMP=TEXT")

                in AdjMarkers ⊳ parseMarker ⊵ optional parseMarker

parseDelOff ∷ Parser AdjustmentOpts
parseDelOff = let parseOffset ∷ Parser Duration
                  parseOffset = optT (short 'f' ⊕ long "offset"
                                                ⊕ metavar "OFFSET" ⊕ value 0)

                  -- parse a decimal value, with optional leading +/-, and
                  -- optional value in front of the decimal point (i.e.,
                  -- +2, -0.2, 0.2, .2 are all valid)
                  decimal ∷ Stream σ η Char ⇒ ParsecT σ ν η ℚ
                  decimal = fractional' optSign Decimal Optional
                                        (char '.' ⋫ pure ()) decExpSign
                  readSkew ∷ ReadM Skew
                  readSkew =
                      eitherReader $ bimap show MS_S ⊳ parse decimal "cmdline"
                  parseSkew ∷ Parser Skew
                  parseSkew = option readSkew
                                      (ю [ short 's', long "skew"
                                         , metavar "SKEW", value (MS_S 0) ])
               in AdjDelOff ⊳ parseSkew ⊵ parseOffset


parseOptions ∷ Parser Options
parseOptions = Options ⊳ many (parseFile ф) ⊵ (parseMarkers ∤ parseDelOff)

{-
class PrintOut σ where
  toP ∷ Printable ρ ⇒ ρ → σ

parseTextual ∷ ∀ β τ α .
      (Textual β, PrintOut τ, Printable α, Typeable β) ⇒
      α → Either τ β
parseTextual (toText → z) =
  let fromParsed (Parsed a)      = a
      -- this function exists solely to provide a hypothetical value to reflect
      -- on
      fromParsed (Malformed _ _) = error "this should never be evaluated"
      parsedZ                    = parseText z
      typ                        = typeOf $ fromParsed parsedZ
   in case parsedZ of
        Parsed a       → Right a
        Malformed [] x → Left ∘ toP $
                           [fmtT|failed to parse '%t' as '%w': %s|] z typ x
        Malformed xs x → let msg = [fmtT|failed to parse '%t' as '%w': [%L] %s|]
                                   z typ xs x
                          in Left (toP msg)

instance PrintOut Text where
  toP = toText

instance PrintOut String where
  toP = toString

readS ∷ (Textual α, Typeable α) ⇒ ReadM α
readS = eitherReader parseTextual

argS ∷ (Textual α, Typeable α) ⇒ Mod ArgumentFields α → Parser α
argS = argument readS

optS ∷ (Textual α, Typeable α) ⇒ Mod OptionFields α → Parser α
optS = option readS

-}

parseFile ∷ Mod ArgumentFields File → Parser File
parseFile ms = argT (action "file" ⊕ metavar "FILE" ⊕ ms)

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
                        txt ← liftIO $ TextIO.hGetContents stdin
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

-- srtTimestamp ∷ Text
-- srtTimestamp = "01:20:34,567"

-- srtTimestampRef ∷ SRTTimeStamp
-- srtTimestampRef = SRTTimeStamp (MS 4834_567)

--------------------

-- srtTiming ∷ Text
-- srtTiming = "00:00:01,000 --> 00:00:04,074"

-- srtTimingRef ∷ SRTTiming
-- srtTimingRef = SRTTiming 1_000 4_074

--------------------

-- srtSubtitleText ∷ Text
-- srtSubtitleText = unlines
--   [ "Subtitles downloaded from www.OpenSubtitles.org"
--   , "Deklan, that's enough."
--   ]

-- srtSubtitleTextRef ∷ SRTSubtitleText
-- srtSubtitleTextRef =
--   SRTSubtitleText $ unlines [ "Subtitles downloaded from www.OpenSubtitles.org"
--                             , "Deklan, that's enough." ]
--------------------

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

--------------------

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

----------------------------------------

tests ∷ TestTree
tests = testGroup "srt-adjust" [ srtSubtitleTests
                               , srtSequenceTests, optionsAdjustTests
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

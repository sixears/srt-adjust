{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ViewPatterns               #-}

-- TODO:
-- split out components
-- add completion for duration/timestamp?
-- add completion for marker texts?

import Prelude  ( Bounded( minBound, maxBound ), Double, Enum, Float
                , Fractional( (/), fromRational ), Int
                , Integral( quotRem, toInteger )
                , Num( (+), (-), (*), abs, signum , fromInteger, negate )
                , Real( toRational )
                , (^), div, divMod, error, floor, fromIntegral, mod, realToFrac, round

                )

-- base --------------------------------

import qualified  Data.List

import Control.Applicative  ( many, some )
import Control.DeepSeq      ( NFData )
import Control.Exception    ( ArithException( Overflow, Underflow ), Exception
                            , SomeException, catch, evaluate, throw )
import Control.Monad        ( Monad, forM_, return, when )
import Control.Monad.IO.Class  ( MonadIO, liftIO )
import Data.Bifunctor       ( bimap )
import Data.Bool            ( Bool, not, otherwise )
import Data.Char            ( Char )
import Data.Either          ( Either( Left, Right ) )
import Data.Eq              ( Eq )
import Data.Foldable        ( foldl1, sum, toList )
import Data.Function        ( ($), (&), const, id )
import Data.Int             ( Int64 )
import Data.List            ( dropWhileEnd, elem, reverse )
import Data.Maybe           ( Maybe( Just, Nothing ), isJust, isNothing )
import Data.Ord             ( Ord, (<), (>), (>=), max, min )
import Data.Ratio           ( (%) )
import Data.String          ( IsString, String )
import Data.Typeable        ( Typeable, typeOf )
import Data.Word            ( Word8, Word16, Word32, Word64 )
import System.Exit          ( ExitCode( ExitSuccess ) )
import System.IO            ( IO, hSetEncoding, stdin, utf8 )
import Text.Read            ( read )
import Text.Show            ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Bool.Unicode      ( (∧), (∨) )
import Data.Eq.Unicode        ( (≡), (≢) )
import Data.Function.Unicode  ( (∘) )
import Data.Monoid.Unicode    ( (⊕) )
import Data.Ord.Unicode       ( (≤), (≥) )
import Prelude.Unicode        ( ℚ, ℤ, (÷) )

-- boundedn ----------------------------

import BoundedN  ( 𝕎, pattern 𝕎 )
import ToNum     ( toNum, toNumI )

-- data-textual ------------------------

import Data.Textual             ( Parsed( Malformed, Parsed )
                                , Printable( print )
                                , Textual( textual )
                                , fromString, fromText, parseText
                                , toString, toText
                                )
import Data.Textual.Fractional  ( Optional( Optional, Required )
                                , Sign( NonNegative )
                                , decExpSign, fraction', fractional, fractional'
                                , optSign, optSlash
                                )
import Data.Textual.Integral    ( Decimal( Decimal )
                                , bounded', nnBounded, nnUpTo, nonNegative )

-- deepseq -----------------------------

import Control.DeepSeq  ( force )

-- exited ------------------------------

import Exited  ( doMain )

-- fluffy ------------------------------

import Fluffy.MonadIO  ( warn )
import Fluffy.Options  ( parseOpts )

-- fpath -------------------------------

import FPath.AsFilePath        ( filepath )
import FPath.Error.FPathError  ( AsFPathError( _FPathError ), FPathError
                               , FPathIOError, _FPIO_IO_ERROR,_FPIO_PATH_ERROR )
import FPath.File              ( File )

-- lens --------------------------------

import Control.Lens.Getter  ( view )
import Control.Lens.Iso     ( Iso', iso )
import Control.Lens.Lens    ( Lens', lens )
import Control.Lens.Prism   ( Prism', prism' )

-- monaderror-io -----------------------

import MonadError           ( ѥ )
import MonadError.IO.Error  ( AsIOError( _IOError ), IOError, userE )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFunctor( omap ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋪), (⋫), (∤) )
import Data.MoreUnicode.Function     ( (⅋) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Lens         ( (⊣), (⫣), (⊢), (⊧), (⫥) )
import Data.MoreUnicode.Monoid       ( ф, ю )
import Data.MoreUnicode.Natural      ( ℕ )
import Data.MoreUnicode.Tasty        ( (≟) )

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError, throwError )

-- non-empty-containers ----------------

import NonEmptyContainers.SeqNE       ( SeqNE, (⋗), pattern (:⫸) )

-- options-applicative -----------------

import Options.Applicative  ( ArgumentFields, Mod, OptionFields, Parser, ReadM
                            , action, argument, eitherReader, long, metavar
                            , option, optional, pure, short, value
                            )

-- parsec ------------------------------

import Text.Parsec.Prim  ( ParsecT, Stream, parse )

-- parsers -----------------------------

import qualified Text.Parser.Combinators

import Text.Parser.Char         ( CharParsing
                                , anyChar, char, digit, noneOf, oneOf, string )
import Text.Parser.Combinators  ( Parsing, (<?>)
                                , count, sepEndBy, skipOptional, try )

-- parsec-plus-base -------------------------

import ParsecPlus  ( AsParseError( _ParseError ), IOParseError, ParseError )

-- parsec-plus -------------------------

import ParsecPlus  ( Parsecable( parsec, parser ), parsecFileUTF8 )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary
                              ( Arbitrary( arbitrary ), arbitraryBoundedIntegral
                              , arbitrarySizedNatural )
import Test.QuickCheck.Gen    ( Gen, listOf, listOf1, suchThat )
import Test.QuickCheck.Modifiers
                              ( PrintableString( getPrintableString ) )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( testCase )

-- tasty-plus --------------------------

import TastyPlus  ( assertListEqR, assertListEq, propInvertibleText, runTestsP
                  , runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( Property, forAll, ioProperty, testProperty )

-- text --------------------------------

import Data.Text     ( Text, filter, head, intercalate
                     , isInfixOf, null, pack, unlines )
import qualified  Data.Text.IO  as  TextIO

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt, fmtT )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

{- | Much like `signum`, but using a strong type. -}
data NumSign = MINUS | NOUGHT | PLUS
  deriving (Eq,Show)

toNumSign ∷ (Ord α, Num α) ⇒ α → NumSign
toNumSign a | a < 0     = MINUS
            | a > 0     = PLUS
            | otherwise = NOUGHT

fromNumSign ∷ Num α ⇒ NumSign → α
fromNumSign MINUS  = -1
fromNumSign PLUS   =  1
fromNumSign NOUGHT =  0

type 𝔹 = Bool

ePatSymExhaustive ∷ String → α
ePatSymExhaustive s =
    error $ s ⊕ "https://gitlab.haskell.org/ghc/ghc/issues/10339"

(⧐) ∷ MonoFunctor mono ⇒ (Element mono → Element mono) → mono → mono
(⧐) = omap

{- | A `MonoFunctor` over Text; defined explicitly to allow types to be an
     instance of this as well as a regular MonoFunctor -}
class TFunctor α where
  tmap ∷ (Text → Text) → α → α

-- `Text.Parser.Char.spaces` parses *all* spaces, including newline.  That's not
-- what we need for parsing/skipping spaces at the end of the line, hence this
-- function
whitespaces ∷ CharParsing η ⇒ η String
whitespaces = many $ oneOf " \t"

-- Parse a newline, optionally preceded by a carriage-return
-- (flucking windoze...)
nl ∷ (CharParsing η, Monad η) ⇒ η ()
nl = skipOptional (char '\r') ⋫ char '\n' ⋫ return () <?> "cr/nl"

------------------------------------------------------------

-- TODO
-- Add ADD/SUB/MULT/DIV CARRY; e.g., ADD to return carry bit
-- , Mult to return tuple
boundsCheck ∷ (Integral γ, Num γ) ⇒ γ → γ → γ → γ
boundsCheck lower upper n@(toInteger → n')
   | n' < toInteger lower = throw Underflow
   | n' > toInteger upper = throw Overflow
   | otherwise            = fromIntegral n

forceCatch ∷ NFData α ⇒ α → IO (Maybe α)
forceCatch x = let forceJust ∷ NFData α ⇒ α → IO (Maybe α)
                   forceJust = evaluate ∘ force ∘ Just
                in catch @SomeException (forceJust x) (const $ return Nothing)

checkBounds ∷ (Integral α, NFData α) ⇒ (α → α) → α → α → α → Property
checkBounds f x y i = ioProperty $ isWithinCheckY x y i ⊳ forceCatch (f i)

checkBounds' ∷ (Integral α, NFData α, Bounded α) ⇒ (α → α) → α → Property
checkBounds' f = checkBounds f minBound maxBound

boundsTests ∷ TestTree
boundsTests =
  let gen3Nats ∷ Gen (ℕ,ℕ,ℕ)
      gen3Nats = (,,) ⊳ arbitrarySizedNatural ⊵ arbitrarySizedNatural
                                              ⊵ arbitrarySizedNatural
   in testGroup "boundsCheck"
                [ testProperty "Word8"   (boundedProp @Word8)
                , testProperty "Word16"  (boundedProp @Word16)
                , testProperty "Word64"  (boundedProp @Word64)
                , testProperty "Int"     (boundedProp @Int)
                , testProperty "Integer" (boundedProp @ℤ)
                , testProperty "Natural" (forAll gen3Nats boundedProp')
                ]

between ∷ Ord α ⇒ α → (α,α) → 𝔹
between a (lower,upper) = a ≥ lower ∧ a ≤ upper

{- | Given two bounds, is a value within them? -}
isWithin ∷ Integral α ⇒ α → α → α → 𝔹
isWithin (toInteger → x) (toInteger → y) (toInteger → a) =
  a `between` ((min x y),(max x y))

{- | Given two bounds, if a value is within them, check for Just; else check
     check for Nothing. -}
isWithinCheckY ∷ Integral α ⇒ α → α → α → Maybe α → 𝔹
isWithinCheckY x y a = if isWithin x y a then isJust else isNothing

boundedProp ∷ (Integral α, NFData α) ⇒ α → α → α → Property
boundedProp x y = checkBounds (boundsCheck (min x y) (max x y)) x y

boundedProp' ∷ (Integral α, NFData α) ⇒ (α,α,α) → Property
boundedProp' (x,y,a) = boundedProp x y a

------------------------------------------------------------

newtype N60 = N_60 Word16
  deriving (Enum, Eq, Integral, NFData, Ord, Real, Show)

pattern N60 ∷ Word16 → N60
pattern N60 n ← N_60 n
        where N60 n = toN60 n

toN60 ∷ (Integral α, Num α) ⇒ α → N60
toN60 n@(toInteger → n') | n' < toInteger (minBound @N60) = throw Underflow
                         | n' > toInteger (maxBound @N60) = throw Overflow
                         | otherwise                     = N_60 (fromIntegral n)

-- We implement our own Num, rather than deriving it, so that we can implement
-- `fromInteger`; per https://www.haskell.org/tutorial/numbers.html,
-- `fromInteger` is used to implement numeric literals; so we use it, and
-- (+),(-),(*) to ensure overflow/underflow are caught.

-- DON'T EXPOSE THE CONSTRUCTOR as that bypasses the bounds check

instance Num N60 where
  (N_60 a) + (N_60 b) = fromInteger (toInteger (a + b))
  (N_60 a) - (N_60 b) = fromInteger (toInteger (a - b))
  (N_60 a) * (N_60 b) = fromInteger (toInteger (a * b))

  negate (N_60 0) = 0
  negate _         = throw Underflow

  fromInteger ∷ ℤ → N60
  fromInteger = toN60

  abs = id

  signum (N_60 0) = 0
  signum _ = 1

instance Bounded N60 where
  minBound = N_60 0
  maxBound = N_60 59


------------------------------------------------------------

newtype N24 = N_24 Word16
  deriving (Enum, Eq, Integral, NFData, Ord, Real, Show)

pattern N24 ∷ Word16 → N24
pattern N24 n ← N_24 n
        where N24 n = toN24 n

toN24 ∷ (Integral α, Num α) ⇒ α → N24
toN24 n@(toInteger → n') | n' < toInteger (minBound @N24) = throw Underflow
                         | n' > toInteger (maxBound @N24) = throw Overflow
                         | otherwise                     = N_24 (fromIntegral n)

-- We implement our own Num, rather than deriving it, so that we can implement
-- `fromInteger`; per https://www.haskell.org/tutorial/numbers.html,
-- `fromInteger` is used to implement numeric literals; so we use it, and
-- (+),(-),(*) to ensure overflow/underflow are caught.

-- DON'T EXPOSE THE CONSTRUCTOR as that bypasses the bounds check

instance Num N24 where
  (N_24 a) + (N_24 b) = fromInteger (toInteger (a + b))
  (N_24 a) - (N_24 b) = fromInteger (toInteger (a - b))
  (N_24 a) * (N_24 b) = fromInteger (toInteger (a * b))

  negate (N_24 0) = 0
  negate _         = throw Underflow

  fromInteger ∷ ℤ → N24
  fromInteger = toN24

  abs = id

  signum (N_24 0) = 0
  signum _ = 1

instance Bounded N24 where
  minBound = N_24 0
  maxBound = N_24 23

------------------------------------------------------------

{- | Bounded to 1Billion ([0-999,999,999]). -}
newtype NE9 = N_E9 Word32
  deriving (Enum, Eq, Integral, NFData, Ord, Real, Show)

pattern NE9 ∷ Word32 → NE9
pattern NE9 n ← N_E9 n
        where NE9 n = toNE9 n

toNE9 ∷ (Integral α, Num α) ⇒ α → NE9
toNE9 n@(toInteger → n') | n' < toInteger (minBound @NE9) = throw Underflow
                         | n' > toInteger (maxBound @NE9) = throw Overflow
                         | otherwise                     = N_E9 (fromIntegral n)

-- We implement our own Num, rather than deriving it, so that we can implement
-- `fromInteger`; per https://www.haskell.org/tutorial/numbers.html,
-- `fromInteger` is used to implement numeric literals; so we use it, and
-- (+),(-),(*) to ensure overflow/underflow are caught.

-- DON'T EXPOSE THE CONSTRUCTOR as that bypasses the bounds check

instance Num NE9 where
  (N_E9 a) + (N_E9 b) = fromInteger (toInteger (a + b))
  (N_E9 a) - (N_E9 b) = fromInteger (toInteger (a - b))
  (N_E9 a) * (N_E9 b) = fromInteger (toInteger (a * b))

  negate (N_E9 0) = 0
  negate _         = throw Underflow

  fromInteger ∷ ℤ → NE9
  fromInteger = toNE9

  abs = id

  signum (N_E9 0) = 0
  signum _ = 1

instance Bounded NE9 where
  minBound = N_E9 0
  maxBound = N_E9 999_999_999

                                   -- ≃ 5,124,095h
------------------------------------------------------------

{- | Bounded to max. number of hours in a `Duration` (5,124,095). -}
newtype N2562047 = N_2562047 Word32
  deriving (Enum, Eq, Integral, NFData, Ord, Real, Show)

pattern N2562047 ∷ Word32 → N2562047
pattern N2562047 n ← N_2562047 n
        where N2562047 n = toN2562047 n

toN2562047 ∷ (Integral α, Num α) ⇒ α → N2562047
toN2562047 n@(toInteger → n')
                         | n' < toInteger (minBound @N2562047) = throw Underflow
                         | n' > toInteger (maxBound @N2562047) = throw Overflow
                         | otherwise                = N_2562047 (fromIntegral n)

-- We implement our own Num, rather than deriving it, so that we can implement
-- `fromInteger`; per https://www.haskell.org/tutorial/numbers.html,
-- `fromInteger` is used to implement numeric literals; so we use it, and
-- (+),(-),(*) to ensure overflow/underflow are caught.

-- DON'T EXPOSE THE CONSTRUCTOR as that bypasses the bounds check

instance Num N2562047 where
  (N_2562047 a) + (N_2562047 b) = fromInteger (toInteger (a + b))
  (N_2562047 a) - (N_2562047 b) = fromInteger (toInteger (a - b))
  (N_2562047 a) * (N_2562047 b) = fromInteger (toInteger (a * b))

  negate (N_2562047 0) = 0
  negate _         = throw Underflow

  fromInteger ∷ ℤ → N2562047
  fromInteger = toN2562047

  abs = id

  signum (N_2562047 0) = 0
  signum _ = 1

instance Bounded N2562047 where
  minBound = N_2562047 0
  maxBound = N_2562047 5_124_095

------------------------------------------------------------

{- | Bounded to max. number of days in a `Duration` (213,503). -}
newtype N106751 = N_106751 Word32
  deriving (Enum, Eq, Integral, NFData, Ord, Real, Show)

pattern N106751 ∷ Word32 → N106751
pattern N106751 n ← N_106751 n
        where N106751 n = toN106751 n

toN106751 ∷ (Integral α, Num α) ⇒ α → N106751
toN106751 n@(toInteger → n')
                         | n' < toInteger (minBound @N106751) = throw Underflow
                         | n' > toInteger (maxBound @N106751) = throw Overflow
                         | otherwise                = N_106751 (fromIntegral n)

-- We implement our own Num, rather than deriving it, so that we can implement
-- `fromInteger`; per https://www.haskell.org/tutorial/numbers.html,
-- `fromInteger` is used to implement numeric literals; so we use it, and
-- (+),(-),(*) to ensure overflow/underflow are caught.

-- DON'T EXPOSE THE CONSTRUCTOR as that bypasses the bounds check

instance Num N106751 where
  (N_106751 a) + (N_106751 b) = fromInteger (toInteger (a + b))
  (N_106751 a) - (N_106751 b) = fromInteger (toInteger (a - b))
  (N_106751 a) * (N_106751 b) = fromInteger (toInteger (a * b))

  negate (N_106751 0) = 0
  negate _         = throw Underflow

  fromInteger ∷ ℤ → N106751
  fromInteger = toN106751

  abs = id

  signum (N_106751 0) = 0
  signum _ = 1

instance Bounded N106751 where
  minBound = N_106751 0
  maxBound = N_106751 5_124_095

------------------------------------------------------------

-- TODO
-- Create & use bounded Rationals for μs/ms/s/h/d ?
-- use units/unit-defs package?  Will that allow for bounded things?
-- Bounded Duration; use in SRTTimeStamp
-- Negative Durations
newtype Duration = Duration Int64 -- in nanoseconds, ≡ 106,751 days ≃ 292y
                                  -- ≃ 2,562,047h
  deriving (Arbitrary, Bounded, Enum, Eq, Ord, Show)


instance Printable Duration where
  print d =
    let HMS_NS g h m s ns = d
     in let suffix = if ns ≡ 0
                     then ""
                     else pack $ '.' : dropWhileEnd (≡ '0')([fmt|%09d|] ns)
            sgn = if g ≡ MINUS then "-" else ""
         in if h > 0
            then P.text $ [fmt|%s%dh%02dm%02d%ts|] sgn h m s suffix
            else if m > 0
                 then P.text $ [fmt|%s%dm%02d%ts|] sgn m s suffix
                 else P.text $ [fmt|%s%d%ts|] sgn s suffix

{- | `try` the first thing, then the next thing, until the last thing (which
     isn't surrounded by a `try`) -}
tries ∷ Parsing η ⇒ SeqNE (η α) → η α
tries (ts :⫸ t) = foldl1 (∤) (toList ((try ⊳ ts) ⋗ t))
tries _          = ePatSymExhaustive "tries"

instance Textual Duration where
  textual = let nnfraction ∷ (Monad η, CharParsing η, Fractional α) ⇒ η α
                nnfraction = fraction' (pure NonNegative) Decimal optSlash

                nnfractional ∷ (Monad η, CharParsing η, Fractional α) ⇒ η α
                nnfractional = fractional' (pure NonNegative) Decimal Required
                                           (char '.' ⋫ pure ()) decExpSign

                frac ∷ (Monad η, CharParsing η) ⇒
                       (ℚ → Duration) → String → [η Duration]
                frac x y = [ x ⊳ nnfraction ⋪ string y
                           , x ⊳ nnfractional ⋪ string y ]

                parseNS ∷ (Monad η, CharParsing η) ⇒ η Duration
                parseNS = Duration ⊳ bounded' optSign Decimal ⋪ string "ns"
                -- parse 0h0m0s0ms0us0ns, or any combination of those, summing
                -- up the pieces

                optmin ∷ (CharParsing η, Num α) ⇒ η α
                optmin = Text.Parser.Combinators.option 1 (char '-' ⋫ pure (-1))
  
                parsehms ∷ (Monad η, CharParsing η) ⇒ η Duration
                parsehms = (*) ⊳ optmin
                               ⊵ (sum ⊳ some (tries $ ю [ frac US    "us"
                                                        , frac MS    "ms"
                                                        , frac SECS  "s"
                                                        , frac MINS  "m"
                                                        , frac HOURS "h"
                                                        ]
                                                      ⋗ parseNS
                                             )
                           )
                -- parse "00:00","00:00,123","00:00:00.234987",etc.

                -- parse n denary digits and multiply by m
                parseDenary n m = ((*m) ∘ read) ⊳ (count n digit)
                -- parse up to n denary digits and multiply by 10 for each
                -- digit missing
                parseDenaries n =
                  tries $ [ parseDenary i (10^(n-i)) | i ← reverse [2..n] ]
                        ⋗ parseDenary 1 (10^(n-1))

                -- parse seconds with up to 3 ms digits after a ',' (srt-style)
                parseMS ∷ (CharParsing η, Monad η) ⇒ η Duration
                parseMS = (\ s ms → (SECS (s%1) + MS (ms%1))) ⊳
                          nnUpTo Decimal 2 ⊵ (char ',' ⋫ parseDenaries 3)

                -- parse a seconds value, which may either be regular decimal,
                -- or up-to-3-digits-after-a-comma style (srt-style).
                parseSecs ∷ (CharParsing η, Monad η) ⇒ η Duration
                parseSecs = try parseMS ∤ SECS ⊳ fractional

                -- parse h:m:s format, allowing for decimal or comma subseconds
                parseHMSColons ∷ (Monad η, CharParsing η) ⇒ η Duration
                parseHMSColons = (\ g h m s → g* (HOURS (h%1) + MINS (m%1) + s))
                               ⊳ optmin
                               ⊵ nonNegative Decimal ⋪ char ':'
                               ⊵ nnUpTo Decimal 2 ⋪ char ':' ⊵ parseSecs

                -- parse m:s format, allowing for decimal or comma subseconds
                parseMSColons ∷ (Monad η, CharParsing η) ⇒ η Duration
                parseMSColons = (\ g m s → g * (MINS (m%1) + s))
                              ⊳ optmin
                              ⊵ (nonNegative Decimal ⋪ char ':') ⊵ parseSecs

             in tries $ [parseHMSColons, parseMSColons] ⋗ parsehms

textualTests ∷ TestTree
textualTests =
  let a ≣ b = testCase b $ Just a ≟ fromString b
   in testGroup "Textual"
                [ testCase "print 100ms"    $ "0.1s"     ≟ toText (MS 100)
                , testCase "print 1s"       $ "1s"       ≟ toText (SECS 1)
                , testCase "print 1m07s"    $ "1m07s"    ≟ toText (SECS 67)
                , testCase "print 1h00m05s" $ "1h00m05s" ≟ toText (SECS 3605)

                , NS               1_234  ≣ "1234ns"
                , Duration     1_234_000  ≣ "1234us"
                , MS               1_234  ≣ "1234ms"
                , SECS             1_234  ≣ "1234s"
                , MS              12_340  ≣ "12.34s"
                , Duration   352_941_176  ≣ "12/34s"
                , MS              12_034  ≣ "12s34ms"
                , MS              61_001  ≣ "1m1s1ms"

                , NS               (-1_234)  ≣ "-1234ns"
                , Duration     (-1_234_000)  ≣ "-1234us"
                , MS               (-1_234)  ≣ "-1234ms"
                , SECS             (-1_234)  ≣ "-1234s"
                , MS              (-12_340)  ≣ "-12.34s"
                , Duration   (-352_941_176)  ≣ "-12/34s"
                , MS              (-12_034)  ≣ "-12s34ms"
                , MS              (-61_001)  ≣ "-1m1s1ms"

                , SECS             1_234  ≣ "20:34"
                , MS           1_234_500  ≣ "20:34,5"
                , MS           1_234_560  ≣ "20:34,56"
                , MS           1_234_567  ≣ "20:34,567"
                , MS           1_234_560  ≣ "20:34.56"
                , US       1_234_567_800  ≣ "20:34.5678"
                , SECS             4_834  ≣ "1:20:34"
                , MS           4_834_560  ≣ "1:20:34,56"
                , US       4_834_567_900  ≣ "1:20:34.5679"

                , SECS             (-1_234)  ≣ "-20:34"
                , MS           (-1_234_500)  ≣ "-20:34,5"
                , MS           (-1_234_560)  ≣ "-20:34,56"
                , MS           (-1_234_567)  ≣ "-20:34,567"
                , MS           (-1_234_560)  ≣ "-20:34.56"
                , US       (-1_234_567_800)  ≣ "-20:34.5678"
                , SECS             (-4_834)  ≣ "-1:20:34"
                , MS           (-4_834_560)  ≣ "-1:20:34,56"
                , US       (-4_834_567_900)  ≣ "-1:20:34.5679"

                , testProperty "invertibleText" (propInvertibleText @Duration)
                ]

{- | Create a duration from Nanoseconds (with bounds checking). -}
fromNanos ∷ Integral α ⇒ α → Duration
fromNanos n@(toInteger → n')
               | n' < toInteger (minBound @Duration) = throw Underflow
               | n' > toInteger (maxBound @Duration) = throw Overflow
               | otherwise                           = Duration (fromIntegral n)

{- | View a duration as nanoseconds. -}
asNanoseconds ∷ Integral α ⇒ Iso' Duration α
asNanoseconds = iso (\ (Duration n) → fromIntegral n) fromNanos

pattern NS ∷ Int64 → Duration
pattern NS n ← Duration n
        where NS n = Duration n

nsTests ∷ TestTree
nsTests =
  let ns3 = Duration 3
   in testGroup "ns"
                [ testCase "3½ms" $
                    (3_499_999∷ℤ) ≟ Duration 3_499_999 ⊣ asNanoseconds
                , testCase "⅔s" $
                    Duration 666_667 ≟ ((666_667∷ℤ) ⫣ asNanoseconds)
                , testCase "1.9...s" $
                      Duration 1_999_999_999
                    ≟ (1_999_999_999∷ℤ) ⫣ asNanoseconds
                , testCase "3ns" $ 3 ≟ (\ (NS n) → n) ns3
                , testCase "2ns" $ ns3 ≟ NS 3
                ]

--------------------

{- | View a duration as microseconds. -}
asMicroseconds ∷ Iso' Duration ℚ
asMicroseconds = iso ((% 1_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 1_000))

{- | (De)Construct a Duration from a number of microseconds. -}
pattern US ∷ ℚ → Duration
pattern US n ← (view asMicroseconds → n)
        where US n = n ⫣ asMicroseconds

{- | View/Set the microseconds 'part' of a Duration; getting will get the whole
     (rounded towards zero) number of microseconds: setting will update the
     number of microseconds, leaving milliseconds and nanoseconds alone.
 -}
microseconds ∷ Lens' Duration Word16
microseconds = _μs

{- | Alias for `microseconds`. -}
_μs ∷ Lens' Duration Word16
_μs = _us

{- | Alias for `microseconds`. -}
_us ∷ Lens' Duration Word16
_us = lens (\ (Duration n) → (fromIntegral $ (n `div` 1_000) `mod` 1_000 ))
           (\ (Duration n) u → let n' = n `mod` 1_000
                                   u' = fromIntegral u
                                   m' = n `div` 1_000_000
                                in if u >= 1_000
                                   then throw Overflow
                                   else Duration $ m'*1_000_000 + u'*1_000 + n')

μsTests ∷ TestTree
μsTests =
  let us3 = Duration 3_000
      f3  = 3 ∷ ℚ
      dur = Duration 456_789_123_456_789
   in testGroup "μs"
                [ testCase "3½ms" $
                      (3499.999 ∷ Float)
                    ≟ realToFrac
                        ((Duration 3_499_999 ⊣ asMicroseconds) ∷ ℚ)
                , testCase "⅔μs" $
                    Duration 667 ≟ ((two%three) ⫣ asMicroseconds)
                , testCase "2ms" $
                      Duration 2_000
                    ≟ ((realToFrac (1.999999999 ∷ Double) ∷ ℚ)
                         ⫣ asMicroseconds)
                , testCase "3μs" $ f3 ≟ (\ (US n) → n) us3
                , testCase "2μs" $ us3 ≟ US f3
                , testCase "_us (get)" $ 456 ≟ dur ⊣ _us
                , testCase "_us (set)" $   Duration 456_789_123_654_789
                                         ≟ dur ⅋ _us ⊢ 654
                ]

--------------------

{- | View a duration as milliseconds. -}
asMilliseconds ∷ Iso' Duration ℚ
asMilliseconds = iso ((% 1_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 1_000_000))

{- | (De)Construct a Duration from a number of milliseconds. -}
pattern MS ∷ ℚ → Duration
pattern MS n ← (view asMilliseconds → n)
        where MS n = n ⫣ asMilliseconds

{- | View/Set the milliseconds 'part' of a Duration; getting will get the whole
     (rounded towards zero) number of milliseconds: setting will update the
     number of milliseconds, leaving seconds and microseconds alone.
 -}
milliseconds ∷ Lens' Duration Word16
milliseconds = _ms

{- | Alias for `milliseconds`. -}
_ms ∷ Lens' Duration Word16
_ms = lens (\ (Duration n) → (fromIntegral $ (n `div` 1_000_000) `mod` 1_000 ))
           (\ (Duration n) m → let u' = n `mod` 1_000_000
                                   m' = fromIntegral m
                                   s' = n `div` 1_000_000_000
                                in if m >= 1_000
                                   then throw Overflow
                                   else Duration $ sum [ s'*1_000_000_000
                                                       , m'*1_000_000, u' ]
           )

msTests ∷ TestTree
msTests =
  let ms3 = Duration 3_000_000
      f3  = 3 ∷ ℚ
      dur = Duration 456_789_123_456_789
   in testGroup "ms"
                [ testCase "3½ms" $
                      (3.499999 ∷ Float)
                    ≟ realToFrac
                        ((Duration 3_499_999 ⊣ asMilliseconds) ∷ ℚ)
                , testCase "⅔ms" $
                    Duration 666667 ≟ ((two%three) ⫣ asMilliseconds)
                , testCase "2ms" $
                        Duration 2_000_000
                      ≟ ((realToFrac (1.999999999 ∷ Double) ∷ ℚ)
                           ⫣ asMilliseconds)
                , testCase "3ms" $ f3 ≟ (\ (MS n) → n) ms3
                , testCase "3ms" $ ms3 ≟ MS f3
                , testCase "_ms (get)" $ 123 ≟ dur ⊣ _ms
                , testCase "_ms (set)" $   Duration 456_789_321_456_789
                                         ≟ dur ⅋ _ms ⊢ 321
                ]

--------------------

{- | (De)Construct a Duration from Hours, Minutes, Seconds & Nanoseconds. -}

hms_ns ∷ Duration → (NumSign,N2562047,N60,N60,NE9)
hms_ns (Duration n) = let fromI ∷ (Integral ι, Integral κ, Num α, Num β) ⇒
                                  (ι,κ) → (α,β)
                          fromI (x,y) = (fromIntegral x, fromIntegral y)
                          (s∷Word64,ns)  = fromI $ abs n `divMod` 1_000_000_000
                          (m∷Word32,ss)  = fromI $ s `divMod` 60
                          (hh,mm)        = fromI $ m `divMod` 60
                       in (toNumSign n,hh,mm,ss,ns)

hms_ns' ∷ NumSign → N2562047 → N60 → N60 → NE9 → Duration
hms_ns' sgn hh mm ss ns = let hh' ∷ ℕ
                              hh' = if hh >= 5_124_095
                                    then throw Overflow
                                    else fromIntegral hh
                              mm' ∷ ℕ
                              mm' = fromIntegral mm
                              ss' ∷ ℕ
                              ss' = fromIntegral ss
                              billℕ ∷ ℕ
                              billℕ = 1_000_000_000
                              ns' = fromIntegral ns
                              n ∷ ℕ
                              n = fromIntegral $
                                    ns' + billℕ * (ss'+ 60*(mm'+60*hh'))
                           in if n > fromIntegral (maxBound @Word64)
                              then throw Overflow
                              else Duration $ fromNumSign sgn * fromIntegral n

pattern HMS_NS ∷ NumSign → N2562047 → N60 → N60 → NE9 → Duration
pattern HMS_NS sgn hh mm ss ns ← (hms_ns → (sgn,hh,mm,ss,ns))
        where HMS_NS = hms_ns'


hms_nsTests ∷ TestTree
hms_nsTests =
  let dur = Duration (-3_723_000_000_004)
      HMS_NS g hh mm ss ns = dur
   in testGroup "HMS_NS"
                [ testCase "→ HMS_NS" $ dur ≟ HMS_NS MINUS 1 2 3 4
                , testCase "g"  $ MINUS ≟ g
                , testCase "hh" $ 1     ≟ hh
                , testCase "mm" $ 2     ≟ mm
                , testCase "ss" $ 3     ≟ ss
                , testCase "ns" $ 4     ≟ ns
                ]

--------------------

{- | (De)Construct a Duration from Days, Hours, Minutes, Seconds &
     Nanoseconds. -}

dhms_ns ∷ Duration → (N106751,N24,N60,N60,NE9)
dhms_ns (Duration n) = let fromI ∷ (Integral ι, Integral κ, Num α, Num β) ⇒
                                   (ι,κ) → (α,β)
                           fromI (x,y) = (fromIntegral x, fromIntegral y)
                           (s∷Word64,ns)  = fromI $ n `divMod` 1_000_000_000
                           (m∷Word32,ss)  = fromI $ s `divMod` 60
                           (h∷Word32,mm)  = fromI $ m `divMod` 60
                           (dd,hh)        = fromI $ h `divMod` 24
                        in (dd,hh,mm,ss,ns)

pattern DHMS_NS ∷ N106751 → N24 → N60 → N60 → NE9 → Duration
pattern DHMS_NS dd hh mm ss ns ← (dhms_ns → (dd,hh,mm,ss,ns))
        where DHMS_NS dd hh mm ss ns =
                let dd' ∷ ℕ
                    dd' = if dd >= 213_503
                          then throw Overflow
                          else fromIntegral dd
                    hh' ∷ ℕ
                    hh' = fromIntegral hh
                    mm' ∷ ℕ
                    mm' = fromIntegral mm
                    ss' ∷ ℕ
                    ss' = fromIntegral ss
                    billℕ ∷ ℕ
                    billℕ = 1_000_000_000
                    ns' = fromIntegral ns
                    n ∷ ℕ
                    n = fromIntegral $
                          ns' + billℕ * (ss'+ 60*(mm'+60*(hh'+24*dd')))
                 in if n > fromIntegral (maxBound @Word64)
                    then throw Overflow
                    else Duration $ fromIntegral n

dhms_nsTests ∷ TestTree
dhms_nsTests =
  let dur = Duration 93_784_000_000_005
      DHMS_NS dd hh mm ss ns = dur
   in testGroup "DHMS_NS"
                [ testCase "→ DHMS_NS" $ dur ≟ DHMS_NS 1 2 3 4 5
                , testCase "dd" $  1 ≟ dd
                , testCase "hh" $  2 ≟ hh
                , testCase "mm" $  3 ≟ mm
                , testCase "ss" $  4 ≟ ss
                , testCase "ns" $  5 ≟ ns
                ]

--------------------

{- | (De)Construct a Duration from Hours, Minutes, Seconds & Milliseconds.
     Deconstruction will round sub-milliseconds to the nearest millisecond
     value.
-}

hms_ms ∷ Duration → (NumSign,N2562047,N60,N60,𝕎 1000)
hms_ms d = let HMS_NS g hh mm ss ns = d
            in (g,hh,mm,ss,𝕎 (round $ toInteger ns % 1_000_000))

pattern HMS_MS ∷ NumSign → N2562047 → N60 → N60 → 𝕎 1000 → Duration
pattern HMS_MS g hh mm ss ms ← (hms_ms → (g,hh,mm,ss,ms))
        where HMS_MS g hh mm ss ms = HMS_NS g hh mm ss (toNum ms * 1_000_000)

hms_msTests ∷ TestTree
hms_msTests =
  let dur  = Duration 4_834_567_567_123
      dur' = Duration (-4_834_568_000_000)
      HMS_MS g hh mm ss ms = dur
   in testGroup "HMS_MS"
                [ testCase "hms_ms"   $  (PLUS,1,20,34,𝕎 568) ≟ hms_ms dur
                , testCase "→ HMS_MS" $  dur' ≟ HMS_MS MINUS 1 20 34 (𝕎 568)
                , testCase "g"        $ PLUS  ≟ g
                , testCase "hh"       $     1 ≟ hh
                , testCase "mm"       $    20 ≟ mm
                , testCase "ss"       $    34 ≟ ss
                , testCase "ms"       $ 𝕎 568 ≟ ms
                ]

----------------------------------------

{- | View a duration as seconds. -}
asSeconds ∷ Iso' Duration ℚ
asSeconds = iso ((% 1_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                (Duration ∘ round ∘ (*1_000_000_000))

{- | (De)Construct a Duration from a number of seconds. -}
pattern SECS ∷ ℚ → Duration
pattern SECS n ← (view asSeconds → n)
        where SECS n = n ⫣ asSeconds

{- | A lens onto the seconds 'part' of the duration. -}
seconds ∷ Lens' Duration N60
seconds = lens (\ d   → let HMS_NS _ _ _ s _  = d in s)
               (\ d s → let HMS_NS g h m _ ns = d in HMS_NS g h m s ns)

secsTests ∷ TestTree
secsTests =
  let s3 = Duration 3_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration 3_723_123_456_789
      dur' = Duration 3_729_123_456_789
   in testGroup "seconds"
                [ testCase "3s" $ 3 ≟ dur ⊣ seconds
                , testCase "s → 9" $ dur' ≟ dur ⅋ seconds ⊢ 9
                , testCase "3½s" $
                      (3_499_999_999%1_000_000_000)
                    ≟ Duration 3_499_999_999 ⊣ asSeconds
                , testCase "⅔s" $
                    Duration 666_666_667 ≟ ((two%three) ⫣ asSeconds)
                , testCase "2s" $
                    Duration 2_000_000_000 ≟ (2 ⫣ asSeconds)
                , testCase "3s" $ f3 ≟ (\ (SECS n) → n) s3
                , testCase "3s" $ s3 ≟ SECS f3
                ]

--------------------

{- | View a duration as minutes. -}
asMinutes ∷ Iso' Duration ℚ
asMinutes = iso ((% 60_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 60_000_000_000))

{- | (De)Construct a Duration from a number of minutes. -}
pattern MINS ∷ ℚ → Duration
pattern MINS n ← (view asMinutes → n)
        where MINS n = n ⫣ asMinutes

{- | A lens onto the minutes 'part' of the duration. -}
minutes ∷ Lens' Duration N60
minutes = lens (\ d   → let HMS_NS _ _ m _ _  = d in m)
               (\ d m → let HMS_NS g h _ s ns = d in HMS_NS g h m s ns)

minsTests ∷ TestTree
minsTests =
  let s3 = Duration 180_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration 3_723_123_456_789
      dur' = Duration 3_783_123_456_789
   in testGroup "minutes"
                [ testCase "2mins"    $ 2 ≟ dur ⊣ minutes
                , testCase "mins → 3" $ dur' ≟ dur ⅋ minutes ⊢ 3
                , testCase "3½mins" $
                      (3_499_999_999%60_000_000_000)
                    ≟ Duration 3_499_999_999 ⊣ asMinutes
                , testCase "⅔us" $
                    Duration 40_000_000_000 ≟ ((two%three) ⫣ asMinutes)
                , testCase "2mins" $
                    Duration 120_000_000_000 ≟ (2 ⫣ asMinutes)
                , testCase "3mins" $ f3 ≟ (\ (MINS n) → n) s3
                , testCase "3mins" $ s3 ≟ MINS f3
                ]

----------------------------------------

{- | View a duration as hours. -}
asHours ∷ Iso' Duration ℚ
asHours = iso ((% 3_600_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 3_600_000_000_000))

{- | (De)Construct a Duration from a number of hours. -}
pattern HOURS ∷ ℚ → Duration
pattern HOURS n ← (view asHours → n)
        where HOURS n = n ⫣ asHours

{- | A lens onto the hours 'part' of the duration. -}
hours ∷ Lens' Duration N2562047
hours = lens (\ d   → let HMS_NS _ h _ _ _  = d in h)
             (\ d h → let HMS_NS g _ m s ns = d in HMS_NS g h m s ns)

hoursTests ∷ TestTree
hoursTests =
  let s3 = Duration 10_800_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration  3_723_123_456_789
      dur' = Duration 10_923_123_456_789
   in testGroup "hours"
                [ testCase "1hour"     $ 1 ≟ dur ⊣ hours
                , testCase "hours → 3" $ dur' ≟ dur ⅋ hours ⊢ 3
                , testCase "3½hours" $
                      (3_499_999_999%3_600_000_000_000)
                    ≟ Duration 3_499_999_999 ⊣ asHours
                , testCase "⅔us" $
                    Duration 2_400_000_000_000 ≟ ((two%three) ⫣ asHours)
                , testCase "2hours" $
                    Duration 7_200_000_000_000 ≟ (2 ⫣ asHours)
                , testCase "3hours" $ f3 ≟ (\ (HOURS n) → n) s3
                , testCase "3hours" $ s3 ≟ HOURS f3
                ]

----------------------------------------

{- | View a duration as days. -}
asDays ∷ Iso' Duration ℚ
asDays = iso ((% 86_400_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 86_400_000_000_000))

{- | (De)Construct a Duration from a number of days. -}
pattern DAYS ∷ ℚ → Duration
pattern DAYS n ← (view asDays → n)
        where DAYS n = n ⫣ asDays

{- | A lens onto the days 'part' of the duration. -}
days ∷ Lens' Duration N106751
days = lens (\ du → let DHMS_NS da _ _ _ _ = du in da)
             (\ du da → let DHMS_NS _ h m s ns = du in DHMS_NS da h m s ns)

daysTests ∷ TestTree
daysTests =
  let s3 = Duration 259_200_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration 89_532_723_123_456_789
      dur' = Duration 281_523_123_456_789
   in testGroup "days"
                [ testCase "1,036days" $ 1_036 ≟ dur ⊣ days
                , testCase "days → 3" $ dur' ≟ dur ⅋ days ⊢ 3
                , testCase "3½days" $
                      (7%2) ≟ Duration 302_400_000_000_000 ⊣ asDays
                , testCase "⅔us" $
                    Duration 57_600_000_000_000 ≟ ((two%three) ⫣ asDays)
                , testCase "2days" $
                    Duration 172_800_000_000_000 ≟ (2 ⫣ asDays)
                , testCase "3days" $ f3 ≟ (\ (DAYS n) → n) s3
                , testCase "3days" $ s3 ≟ DAYS f3
                ]

--------------------

durationTests ∷ TestTree
durationTests =
  testGroup "Duration" [ textualTests, nsTests, μsTests, dhms_nsTests
                       , hms_nsTests, hms_msTests, msTests, secsTests
                       , minsTests, hoursTests, daysTests
                       ]

instance Num Duration where
  (Duration a) + (Duration b) = fromInteger (toInteger (a + b))
  (Duration a) - (Duration b) = fromInteger (toInteger (a - b))
  (Duration a) * (Duration b) = fromInteger (toInteger (a * b))

  negate (Duration 0) = 0
  negate (Duration n) = Duration (negate n)

  fromInteger ∷ ℤ → Duration
  fromInteger = (⫣ asNanoseconds)

  abs = id

  signum (Duration ns) = Duration (signum ns)

instance Real Duration where
  toRational ∷ Duration → ℚ
  toRational (Duration n) = toRational n

instance Integral Duration where
  quotRem (Duration a) (Duration b) = let (q,r) = a `quotRem` b
                                 in (Duration q,Duration r)
  toInteger ∷ Duration → ℤ
  toInteger (Duration n) = toInteger n

------------------------------------------------------------


{- | Speed factor for timestamps as a multiplicative ratio. -}
newtype Skew = Skew ℚ
  deriving (Eq, Show)

to_ms_s ∷ Skew → ℚ
to_ms_s (Skew s) = (s-1) * 1_000

{- | (De)Construct a speed factor from milliseconds-per-second gain or loss.
     Thus, 100 ⇒ 100ms/s ⇒ 1.1; -100 ⇒ -100ms/s ⇒ 0.9 -}
pattern MS_S ∷ ℚ → Skew
pattern MS_S s ← (to_ms_s → s)
        where MS_S s = Skew $ 1+(s÷1_000)

class Shifty α where
  shift ∷ Duration → Skew → α → α

------------------------------------------------------------

newtype SRTTimeStamp = SRTTimeStamp { unSRTTimeStamp ∷ Duration }
  deriving (Enum, Eq, Ord, Real, Show)

type instance Element SRTTimeStamp = Duration

instance MonoFunctor SRTTimeStamp where
  omap ∷ (Duration → Duration) → SRTTimeStamp → SRTTimeStamp
  omap f (SRTTimeStamp d) = SRTTimeStamp (f d)

instance Shifty SRTTimeStamp where
  shift ∷ Duration → Skew → SRTTimeStamp → SRTTimeStamp
  shift offst (Skew mult) (SRTTimeStamp ts) =
    let (MS ms) = ts+offst in fromInteger (round $ ms*mult)

{- | We provide our own `Num` instance so we can convert to/from milliseconds.
 -}
instance Integral SRTTimeStamp where
  quotRem (SRTTimeStamp (MS ms)) (SRTTimeStamp (MS ms')) =
    let (q,r) = (round ms ∷ ℤ) `quotRem` (round ms' ∷ ℤ)
     in (SRTTimeStamp $ MS (q%1), SRTTimeStamp $ MS (r%1))
  quotRem _ _ = ePatSymExhaustive "SRTTimeStamp quotRem"

  toInteger (SRTTimeStamp (MS ms)) = round ms
  toInteger (SRTTimeStamp _) = ePatSymExhaustive "SRTTimeStamp toInteger"

instance Num SRTTimeStamp where
  a + b = fromInteger (toInteger a + toInteger b)
  a - b = fromInteger (toInteger a - toInteger b)
  a * b = fromInteger (toInteger a * toInteger b)
--    error "Multiplication of TimeStamps makes no sense"

  negate (SRTTimeStamp 0) = 0
  negate _         = throw Underflow

  fromInteger ∷ ℤ → SRTTimeStamp
  fromInteger = SRTTimeStamp ∘ MS ∘ (% 1)

  abs = id

  signum (SRTTimeStamp 0) = 0
  signum _ = 1

instance Fractional SRTTimeStamp where
  a / b = SRTTimeStamp $ (fromIntegral a % fromIntegral b) ⫥ asMilliseconds
  fromRational = SRTTimeStamp ∘ MS

instance Printable SRTTimeStamp where
  print (SRTTimeStamp d) =
    let HMS_MS g h m s ms = d
     in P.text $ [fmt|%s%02d:%02d:%02d,%03d|] (if g ≡ MINUS then "-" else "") h m s (toNumI ms)

instance Textual SRTTimeStamp where
  textual = SRTTimeStamp ⊳ textual

instance Parsecable SRTTimeStamp where
  parser = textual

instance Arbitrary SRTTimeStamp where
  arbitrary = SRTTimeStamp ∘ Duration ∘ (* 1_000_000) ∘ (`mod` 359_999_999) ⊳
                  arbitraryBoundedIntegral
--------------------

srtTimeStampTests ∷ TestTree
srtTimeStampTests =
  let s1 = 5_025_678 ∷ SRTTimeStamp -- 1h23m45s678
      s2 = 9_296_789 ∷ SRTTimeStamp -- 2h34m56s789
   in testGroup "SRTTimeStamp"
                [ testCase "toText s1" $   "01:23:45,678" ≟ toText s1
                , testCase "toText s2" $   "02:34:56,789" ≟ toText s2
                , testCase "s1+s2"     $   "03:58:42,467" ≟ toText (s1 + s2)
                , testCase "s2-s1"     $   "01:11:11,111" ≟ toText (s2 - s1)
                , testCase "s1*2"      $   "03:58:42,467" ≟ toText (s1 + s2)
                , testCase "quotRem" $ (4,3) ≟ (19 ∷ SRTTimeStamp) `quotRem` 4
                , testCase "fromText"  $   Just srtTimestampRef
                                         ≟ fromText srtTimestamp
                , testCase "toText"    $ srtTimestamp ≟ toText srtTimestampRef
                , testCase "toText"    $ srtTimestamp ≟ toText srtTimestampRef
                , testCase "parsec"    $
                        Right (SRTTimeStamp 4834_567_000_000)
                      ≟ parsec @SRTTimeStamp @ParseError @(Either ParseError)
                               @Text @String "srtTimestamp" srtTimestamp
                , testProperty "invertibleText"
                               (propInvertibleText @SRTTimeStamp)
                , testCase "shift" $
                      -- 100 ms/s
                      "01:32:09,346" ≟ toText (shift (MS 1_000) (MS_S 100) s1)
                ]

------------------------------------------------------------

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

--------------------

srtTimingTests ∷ TestTree
srtTimingTests =
  testGroup "SRTTiming"
            [ testCase "fromText" $ Just srtTimingRef ≟ fromText srtTiming
            , testCase "toText"   $ srtTiming ≟ toText srtTimingRef
            , testCase "parsec"   $
                    Right (SRTTiming 1_000 4_074)
                  ≟ parsec @SRTTiming @ParseError @(Either ParseError)
                           @Text @String "srtTimestamp" srtTiming
            , testProperty "invertibleText" (propInvertibleText @SRTTiming)
            , testCase "shift" $
                  SRTTiming 1800 4_567 ≟ shift (MS 1000) (MS_S (-100)) srtTimingRef
            ]

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

--------------------

srtSubtitleTextTests ∷ TestTree
srtSubtitleTextTests =
  testGroup "SRTSubtitleText"
            [ testCase "fromText" $
                    Just srtSubtitleTextRef ≟ fromText srtSubtitleText
            , testCase "toText"   $ srtSubtitleText ≟ toText srtSubtitleTextRef
            , testCase "parsec"   $
                    Right srtSubtitleTextRef
                  ≟ parsec @SRTSubtitleText @ParseError @(Either ParseError)
                           @Text @String "srtTimestamp" srtSubtitleText
            , testProperty "invertibleText"
                           (propInvertibleText @SRTSubtitleText)
            ]

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
                     option readS (long "marker" ⊕ short 'm'
                                                 ⊕ metavar "TIMESTAMP=TEXT")

                in AdjMarkers ⊳ parseMarker ⊵ optional parseMarker

parseDelOff ∷ Parser AdjustmentOpts
parseDelOff = let parseOffset ∷ Parser Duration
                  parseOffset = optS (short 'f' ⊕ long "offset"
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

class PrintOut σ where
  toP ∷ Printable ρ ⇒ ρ → σ

{- | Parse a printable value, give user-friendly error messages. -}
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

parseFile ∷ Mod ArgumentFields File → Parser File
parseFile ms = argS (action "file" ⊕ metavar "FILE" ⊕ ms)

------------------------------------------------------------

-- factor out run, etc. (to ProcLib?)
-- make ProcLib Errors to be Exceptions

say ∷ (MonadIO μ, Printable τ) ⇒ τ → μ ()
say = liftIO ∘ TextIO.putStrLn ∘ toText

pf ∷ File → IO (Either IOParseError SRTSequence)
pf f = ѥ (parsecFileUTF8 f)

pf' ∷ ∀ μ η . (MonadIO μ, MonadError IOParseError η) ⇒ File → μ (η SRTSequence)
pf' f = ѥ (parsecFileUTF8 f)

pf'' ∷ ∀ α μ ε η . (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε η,
                  Parsecable α) ⇒
     File → μ (η α)
pf'' f = ѥ (parsecFileUTF8 f)

pf''' ∷ ∀ α μ ε . (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε μ,
                  Parsecable α) ⇒
     File → μ α
pf''' f = parsecFileUTF8 f

pf_ ∷ ∀ μ ε . (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε μ) ⇒
        File → μ SRTSequence
pf_ f = parsecFileUTF8 f

pf__ ∷ ∀ μ ε . (MonadIO μ, AsParseError ε, AsIOError ε, MonadError ε μ) ⇒
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

srtTimestamp ∷ Text
srtTimestamp = "01:20:34,567"

srtTimestampRef ∷ SRTTimeStamp
srtTimestampRef = SRTTimeStamp (MS 4834_567)

--------------------

srtTiming ∷ Text
srtTiming = "00:00:01,000 --> 00:00:04,074"

srtTimingRef ∷ SRTTiming
srtTimingRef = SRTTiming 1_000 4_074

--------------------

srtSubtitleText ∷ Text
srtSubtitleText = unlines
  [ "Subtitles downloaded from www.OpenSubtitles.org"
  , "Deklan, that's enough."
  ]

srtSubtitleTextRef ∷ SRTSubtitleText
srtSubtitleTextRef =
  SRTSubtitleText $ unlines [ "Subtitles downloaded from www.OpenSubtitles.org"
                            , "Deklan, that's enough." ]
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
tests = testGroup "srt-adjust" [ boundsTests, durationTests
                               , srtTimeStampTests, srtTimingTests
                               , srtSubtitleTextTests, srtSubtitleTests
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

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UnicodeSyntax              #-}
{-# LANGUAGE ViewPatterns               #-}

module Duration
  ( Duration( NS, MS, US, SECS, MINS, HOURS, DAYS, DHMS_NS, HMS_MS )
  , asNanoseconds, fromNanos
  , asMicroseconds, microseconds, _us
  , asMilliseconds, milliseconds, _ms
  , asSeconds, seconds
  , asMinutes, minutes
  , asHours, hours
  , asDays, days

  , tests
  )
where

import Prelude  ( Bounded( maxBound, minBound ), Double, Enum, Float, Fractional
                , Integral( quotRem, toInteger )
                , Num( (+), (-), (*), abs, fromInteger, negate, signum )
                , Real( toRational )
                , (^), fromIntegral, realToFrac, round
                )

-- base --------------------------------

import Control.Applicative  ( pure, some )
import Control.Exception    ( ArithException( Overflow, Underflow ), throw )
import Control.Monad        ( Monad )
import Data.Bifunctor       ( first, second )
import Data.Bool            ( otherwise )
import Data.Eq              ( Eq )
import Data.Foldable        ( sum )
import Data.Function        ( ($), id )
import Data.Int             ( Int64 )
import Data.List            ( dropWhileEnd, reverse )
import Data.Maybe           ( Maybe( Just ) )
import Data.Ord             ( Ord, (<), (>) )
import Data.Proxy           ( Proxy( Proxy ) )
import Data.Ratio           ( Rational, (%) )
import Data.String          ( String )
import Data.Tuple           ( fst, snd )
import System.Exit          ( ExitCode )
import System.IO            ( IO )
import Text.Read            ( read )
import Text.Show            ( Show )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≡) )
import Data.Function.Unicode  ( (∘) )
import Prelude.Unicode        ( ℚ, ℤ )

-- boundedn ----------------------------

import BoundedN  ( 𝕎, pattern 𝕎, (⨹), (⨴), (⨵), (⫽), divModulo )

-- data-textual ------------------------

import Data.Textual             ( Printable( print ), Textual( textual )
                                , fromString, toText )
import Data.Textual.Fractional  ( Optional( Required )
                                , Sign( NonNegative )
                                , decExpSign, fraction', fractional, fractional'
                                , optSign, optSlash
                                )
import Data.Textual.Integral    ( Decimal( Decimal )
                                , bounded', nnUpTo, nonNegative )

-- lens --------------------------------

import Control.Lens.Getter  ( view )
import Control.Lens.Iso     ( Iso', iso )
import Control.Lens.Lens    ( Lens', lens )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋪), (⋫), (∤) )
import Data.MoreUnicode.Function     ( (⅋) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Lens         ( (⊣), (⫣), (⊢) )
import Data.MoreUnicode.Monoid       ( ю )
import Data.MoreUnicode.Natural      ( ℕ )
import Data.MoreUnicode.Tasty        ( (≟) )

-- non-empty-containers ----------------

import NonEmptyContainers.SeqNE  ( (⋗) )

-- number ------------------------------

import Number  ( NumSign( MINUS, PLUS )
               , absT, __fromI, fromNumSign, toNum, toNumI )

-- parser-plus -------------------------

import ParserPlus  ( tries )

-- parsers -----------------------------

import qualified Text.Parser.Combinators

import Text.Parser.Char         ( CharParsing, char, digit, string )
import Text.Parser.Combinators  ( count, try )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary  ( Arbitrary )

-- tasty -------------------------------

import Test.Tasty  ( TestTree, testGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( testCase )

-- tasty-plus --------------------------

import TastyPlus  ( propInvertibleText, runTestsP, runTestsReplay, runTestTree )

-- tasty-quickcheck --------------------

import Test.Tasty.QuickCheck  ( testProperty )

-- text --------------------------------

import Data.Text  ( pack )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

(÷) ∷ ℤ → ℤ → Rational
(÷) = (%)

--------------------------------------------------------------------------------

-- TODO
-- Create & use bounded Rationals for μs/ms/s/h/d ?
-- use units/unit-defs package?  Will that allow for bounded things?
-- Bounded Duration; use in SRTTimeStamp
-- Negative Durations

-- maxBound @Int64 = 9223372036854775807ns
--                 = (9223372036s,854775807ns)
--                 = (153722867m,16s,854775807ns)
--                 = (2562047h,47m,16s,854775807ns)
--                 = (106751d,23h,47m,16s,854775807ns)
--                 ≃ 292y
newtype Duration = Duration { unDuration ∷ Int64 }
  deriving (Arbitrary, Bounded, Enum, Eq, Ord, Show)

-- | as a bounded type, with sign
durBounded ∷ Duration → (NumSign,𝕎 9223372036854775807)
durBounded = second __fromI ∘ absT ∘ unDuration

instance Printable Duration where
  print d =
    let HMS_NS g h m s ns = d
     in let sgn = if g ≡ MINUS then "-" else ""
            suffix = if ns ≡ 𝕎 0
                     then ""
                     else let drop0s = dropWhileEnd (≡ '0')
                           in pack $ '.' : drop0s ([fmt|%09n|] $ ns)
         in if toNumI h > 0
            then P.text $ [fmt|%s%nh%02nm%02n%ts|] sgn h m s suffix
            else if m > 𝕎 0
                 then P.text $ [fmt|%s%nm%02n%ts|] sgn m s suffix
                 else P.text $ [fmt|%s%n%ts|] sgn s suffix

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

                optmin ∷ (CharParsing η, Num α) ⇒ η α
                optmin = Text.Parser.Combinators.option 1 (char '-' ⋫ pure (-1))

                -- parse 0h0m0s0ms0us0ns, or any combination of those, summing
                -- up the pieces
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
                parseMS = (\ s ms → (SECS (s÷1) + MS (ms÷1))) ⊳
                          nnUpTo Decimal 2 ⊵ (char ',' ⋫ parseDenaries 3)

                -- parse a seconds value, which may either be regular decimal,
                -- or up-to-3-digits-after-a-comma style (srt-style).
                parseSecs ∷ (CharParsing η, Monad η) ⇒ η Duration
                parseSecs = try parseMS ∤ SECS ⊳ fractional

                -- parse h:m:s format, allowing for decimal or comma subseconds
                parseHMSColons ∷ (Monad η, CharParsing η) ⇒ η Duration
                parseHMSColons = (\ g h m s → g* (HOURS (h÷1) + MINS (m÷1) + s))
                               ⊳ optmin
                               ⊵ nonNegative Decimal ⋪ char ':'
                               ⊵ nnUpTo Decimal 2 ⋪ char ':' ⊵ parseSecs

                -- parse m:s format, allowing for decimal or comma subseconds
                parseMSColons ∷ (Monad η, CharParsing η) ⇒ η Duration
                parseMSColons = (\ g m s → g * (MINS (m÷1) + s))
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
{-# COMPLETE NS #-}

nsTests ∷ TestTree
nsTests =
  let ns3 = Duration 3
   in testGroup "ns"
                [ testCase "3½ms" $
                    (3_499_999∷ℤ) ≟ Duration 3_499_999 ⊣ asNanoseconds
                , testCase "-⅔s" $
                    Duration (-666_667) ≟ ((-666_667∷ℤ) ⫣ asNanoseconds)
                , testCase "1.9...s" $
                      Duration 1_999_999_999
                    ≟ (1_999_999_999∷ℤ) ⫣ asNanoseconds
                , testCase "3ns" $ 3 ≟ (\ (NS n) → n) ns3
                , testCase "2ns" $ ns3 ≟ NS 3
                ]

--------------------

{- | View a duration as microseconds. -}
asMicroseconds ∷ Iso' Duration ℚ
asMicroseconds = iso ((÷ 1_000) ∘ fromInteger ∘ view asNanoseconds)
                     (Duration ∘ round ∘ (* 1_000))

{- | (De)Construct a Duration from a number of microseconds. -}
pattern US ∷ ℚ → Duration
pattern US n ← (view asMicroseconds → n)
        where US n = n ⫣ asMicroseconds
{-# COMPLETE US #-}

{- | View/Set the microseconds 'part' of a Duration; getting will get the number
     of whole microseconds (rounded towards zero) ignoring milliseconds and
     sub-microseconds: setting will update the number of microseconds, leaving
     milliseconds and nanoseconds alone.
 -}
microseconds ∷ Lens' Duration (𝕎 1000)
microseconds = _μs

{- | Alias for `microseconds`. -}
_μs ∷ Lens' Duration (𝕎 1000)
_μs = _us

{- | Split a duration into milliseconds, microseconds, & nanoseconds. -}
msμsns ∷ Duration → (NumSign,𝕎 9_223_372_036_855,𝕎 1000, 𝕎 1000)
msμsns d = let (g ,n)  = durBounded d
               (μ ,ns) = n ⫽ Proxy @1000
               (ms,μs) = μ ⫽ Proxy @1000
            in (g,ms,μs,ns)

{- | Form a duration from milliseconds, microseconds, & nanoseconds. -}
msμsns' ∷ NumSign → 𝕎 9_223_372_036_855 → 𝕎 1000 →  𝕎 1000 → Duration
msμsns' g ms μs ns =
  Duration $ fromNumSign g * toNum(ns ⨹ Proxy @1000 ⨴ (μs ⨹ (Proxy @1000 ⨴ ms)))

{- | Alias for `microseconds`. -}
_us ∷ Lens' Duration (𝕎 1000)
_us = lens (\ d → let (_,ns) = durBounded d
                      (μs,_) = ns ⫽ Proxy @1_000
                   in snd $ μs ⫽ Proxy @1_000
           )
           (\ d μs → let (g,ms,_,ns) = msμsns d
                     in msμsns' g ms μs ns)

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
                    Duration 667 ≟ ((two÷three) ⫣ asMicroseconds)
                , testCase "2ms" $
                      Duration 2_000
                    ≟ ((realToFrac (1.999999999 ∷ Double) ∷ ℚ)
                         ⫣ asMicroseconds)
                , testCase "3μs" $ f3 ≟ (\ (US n) → n) us3
                , testCase "2μs" $ us3 ≟ US f3
                , testCase "_us (get)" $ 𝕎 456 ≟ dur ⊣ _us
                , testCase "_us (set)" $   Duration 456_789_123_654_789
                                         ≟ dur ⅋ _us ⊢ 𝕎 654
                ]

--------------------

{- | View a duration as milliseconds. -}
asMilliseconds ∷ Iso' Duration ℚ
asMilliseconds = iso ((÷ 1_000_000) ∘ fromInteger ∘ view asNanoseconds)
                     (Duration ∘ round ∘ (* 1_000_000))

{- | (De)Construct a Duration from a number of milliseconds. -}
pattern MS ∷ ℚ → Duration
pattern MS n ← (view asMilliseconds → n)
        where MS n = n ⫣ asMilliseconds
{-# COMPLETE MS #-}

{- | View/Set the milliseconds 'part' of a Duration; getting will get the number
     of whole milliseconds (rounded towards zero) ignoring seconds and
     sub-milliseconds: setting will update the number of milliseconds, leaving
     seconds and microseconds alone.
 -}
milliseconds ∷ Lens' Duration (𝕎 1000)
milliseconds = _ms

{- | Split a duration into milliseconds, microseconds, & nanoseconds. -}
smsμs ∷ Duration → (NumSign,𝕎 9_223_372_037,𝕎 1000, 𝕎 1_000_000)
smsμs d = let (g,n)  = durBounded d
              (m,μs) = n ⫽ Proxy @1_000_000
              (s,ms) = m ⫽ Proxy @1000
           in (g,s,ms,μs)

{- | Form a duration from seconds, milliseconds, & microseconds. -}
smsμs' ∷ NumSign → 𝕎 9_223_372_037 → 𝕎 1000 →  𝕎 1_000_000 → Duration
smsμs' g s ms μs =
  Duration $ fromNumSign g * toNum (μs ⨹ Proxy @1_000_000
                                       ⨴ (ms ⨹ (Proxy @1000 ⨴ s)))

{- | Alias for `milliseconds`. -}
_ms ∷ Lens' Duration (𝕎 1000)
_ms = lens (\ d → let (_,ns) = durBounded d
                      (ms,_) = ns ⫽ Proxy @1_000_000
                   in snd $ ms ⫽ Proxy @1_000
           )
           (\ d ms → let (g,s,_,μs) = smsμs d
                      in smsμs' g s ms μs)

msTests ∷ TestTree
msTests =
  let ms3 = Duration 3_000_000
      f3  = 3 ∷ ℚ
      dur = Duration (-456_789_123_456_789)
   in testGroup "ms"
                [ testCase "3½ms" $
                      (3.499999 ∷ Float)
                    ≟ realToFrac
                        ((Duration 3_499_999 ⊣ asMilliseconds) ∷ ℚ)
                , testCase "⅔ms" $
                    Duration 666667 ≟ ((two÷three) ⫣ asMilliseconds)
                , testCase "2ms" $
                        Duration 2_000_000
                      ≟ ((realToFrac (1.999999999 ∷ Double) ∷ ℚ)
                           ⫣ asMilliseconds)
                , testCase "3ms" $ f3 ≟ (\ (MS n) → n) ms3
                , testCase "3ms" $ ms3 ≟ MS f3
                , testCase "_ms (get)" $ 𝕎 123 ≟ dur ⊣ _ms
                , testCase "_ms (set)" $   Duration (-456_789_321_456_789)
                                         ≟ dur ⅋ _ms ⊢ 𝕎 321
                ]

--------------------

{- | (De)Construct a Duration from Hours, Minutes, Seconds & Nanoseconds. -}

hms_ns ∷ Duration → (NumSign,𝕎 2562048,𝕎 60,𝕎 60,𝕎 1_000_000_000)
hms_ns (Duration n) = let (g,n')  = absT n
                          (s,ns)  = divModulo n'
                          (m,ss)  = divModulo s
                          (hh,mm) = first __fromI (divModulo m)
                       in (g,hh,mm,ss,ns)

----------

hms_ns' ∷ NumSign → 𝕎 2562048 → 𝕎 60 → 𝕎 60 → 𝕎 1_000_000_000 → Duration
hms_ns' sgn hh mm ss ns =
  let billion = Proxy @1_000_000_000
      n ∷ ℕ
      n = toNum $ ns ⨹ billion ⨴ (ss ⨹ (Proxy @60 ⨴ (mm ⨹ (Proxy @60 ⨴ hh))))
   in if n > fromIntegral (maxBound @Int64)
      then throw Overflow
      else Duration $ fromNumSign sgn * fromIntegral n

----------

pattern HMS_NS ∷ NumSign → 𝕎 2562048 → 𝕎 60 → 𝕎 60 → 𝕎 1_000_000_000
                         → Duration
pattern HMS_NS sgn hh mm ss ns ← (hms_ns → (sgn,hh,mm,ss,ns))
        where HMS_NS = hms_ns'
{-# COMPLETE HMS_NS #-}

----------

hms_nsTests ∷ TestTree
hms_nsTests =
  let dur = Duration (-3_723_000_000_004)
      HMS_NS g hh mm ss ns = dur
   in testGroup "HMS_NS"
                [ testCase "→ HMS_NS" $ dur ≟ HMS_NS MINUS (𝕎 1)(𝕎 2)(𝕎 3)(𝕎 4)
                , testCase "g"  $ MINUS ≟ g
                , testCase "hh" $ 𝕎 1   ≟ hh
                , testCase "mm" $ 𝕎 2   ≟ mm
                , testCase "ss" $ 𝕎 3   ≟ ss
                , testCase "ns" $ 𝕎 4   ≟ ns
                ]

--------------------

{- | (De)Construct a Duration from Days, Hours, Minutes, Seconds &
     Nanoseconds. -}

dhms_ns ∷ Duration → (NumSign,𝕎 106752,𝕎 24,𝕎 60,𝕎 60,𝕎 1_000_000_000)
dhms_ns u = let (g,ns) = durBounded u
                (s,nn) = ns ⫽ Proxy @1_000_000_000
                (m,ss) = s  ⫽ Proxy @60
                (h,mm) = m  ⫽ Proxy @60
                (d,hh) = h  ⫽ Proxy @24
             in (g,d,hh,mm,ss,nn)

----------

dhms_ns' ∷ NumSign → 𝕎 106752 → 𝕎 24 → 𝕎 60 → 𝕎 60 → 𝕎 1_000_000_000 → Duration
dhms_ns' sgn dd hh mm ss ns =
  let billion = Proxy @1_000_000_000
      s ∷ 𝕎 9223462860
      s = ss ⨹ (Proxy @60 ⨴ (mm ⨹ (Proxy @60 ⨴ (hh ⨹ (Proxy @24 ⨴ dd)))))
      n ∷ ℕ
      n = toNum $ ns ⨹ billion ⨴ s
   in if n > fromIntegral (maxBound @Int64)
      then throw Overflow
      else Duration $ fromNumSign sgn * fromIntegral n

----------

pattern DHMS_NS ∷ NumSign → 𝕎 106752 → 𝕎 24 → 𝕎 60 → 𝕎 60 → 𝕎 1_000_000_000
                → Duration
pattern DHMS_NS g dd hh mm ss ns ← (dhms_ns → (g,dd,hh,mm,ss,ns))
        where DHMS_NS = dhms_ns'
{-# COMPLETE DHMS_NS #-}

----------

dhms_nsTests ∷ TestTree
dhms_nsTests =
  let dur = Duration 93_784_000_000_005
      DHMS_NS g dd hh mm ss ns = dur
   in testGroup "DHMS_NS"
                [ testCase "→ DHMS_NS" $ dur ≟ DHMS_NS PLUS (𝕎 1) (𝕎 2) (𝕎 3)
                                                                   (𝕎 4) (𝕎 5)
                , testCase "g"  $ PLUS ≟ g
                , testCase "dd" $ 𝕎 1 ≟ dd
                , testCase "hh" $ 𝕎 2 ≟ hh
                , testCase "mm" $ 𝕎 3 ≟ mm
                , testCase "ss" $ 𝕎 4 ≟ ss
                , testCase "ns" $ 𝕎 5 ≟ ns
                ]

--------------------

{- | (De)Construct a Duration from Hours, Minutes, Seconds & Milliseconds.
     Deconstruction will round sub-milliseconds to the nearest millisecond
     value.
-}

hms_ms ∷ Duration → (NumSign,𝕎 2562048,𝕎 60,𝕎 60,𝕎 1000)
hms_ms d = let HMS_NS g hh mm ss ns = d
            in (g,hh,mm,ss, (fst ∘ (⫽ Proxy @1_000_000)) ns)

----------

pattern HMS_MS ∷ NumSign → 𝕎 2562048 → 𝕎 60 → 𝕎 60 → 𝕎 1000 → Duration
pattern HMS_MS g hh mm ss ms ← (hms_ms → (g,hh,mm,ss,ms))
        where HMS_MS g hh mm ss ms = HMS_NS g hh mm ss (ms ⨵ Proxy @1_000_000)
{-# COMPLETE HMS_NS #-}

hms_msTests ∷ TestTree
hms_msTests =
  let dur  = Duration 4_834_567_567_123
      dur' = Duration (-4_834_568_000_000)
      HMS_MS g hh mm ss ms = dur
   in testGroup "HMS_MS"
                [ testCase "hms_ms"   $  (PLUS,𝕎 1,𝕎 20,𝕎 34,𝕎 567) ≟ hms_ms dur
                , testCase "→ HMS_MS" $  dur' ≟ HMS_MS MINUS (𝕎 1) (𝕎 20) (𝕎 34)
                                                             (𝕎 568)
                , testCase "g"        $ PLUS  ≟ g
                , testCase "hh"       $ 𝕎   1 ≟ hh
                , testCase "mm"       $ 𝕎  20 ≟ mm
                , testCase "ss"       $ 𝕎  34 ≟ ss
                , testCase "ms"       $ 𝕎 567 ≟ ms
                ]

----------------------------------------

{- | View a duration as seconds. -}
asSeconds ∷ Iso' Duration ℚ
asSeconds = iso ((÷ 1_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                (Duration ∘ round ∘ (*1_000_000_000))

{- | (De)Construct a Duration from a number of seconds. -}
pattern SECS ∷ ℚ → Duration
pattern SECS n ← (view asSeconds → n)
        where SECS n = n ⫣ asSeconds
{-# COMPLETE SECS #-}

{- | A lens onto the seconds 'part' of the duration. -}
seconds ∷ Lens' Duration (𝕎 60)
seconds = lens (\ d   → let HMS_NS _ _ _ s _  = d in s)
               (\ d s → let HMS_NS g h m _ ns = d in HMS_NS g h m s ns)

secsTests ∷ TestTree
secsTests =
  let s3 = Duration 3_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration 3_723_123_456_789
      dur' = Duration 3_729_123_456_789
   in testGroup "seconds"
                [ testCase "3s" $ 𝕎 3 ≟ dur ⊣ seconds
                , testCase "s → 9" $ dur' ≟ dur ⅋ seconds ⊢ 𝕎 9
                , testCase "3½s" $
                      (3_499_999_999÷1_000_000_000)
                    ≟ Duration 3_499_999_999 ⊣ asSeconds
                , testCase "⅔s" $
                    Duration 666_666_667 ≟ ((two÷three) ⫣ asSeconds)
                , testCase "2s" $
                    Duration 2_000_000_000 ≟ (2 ⫣ asSeconds)
                , testCase "3s" $ f3 ≟ (\ (SECS n) → n) s3
                , testCase "3s" $ s3 ≟ SECS f3
                ]

--------------------

{- | View a duration as minutes. -}
asMinutes ∷ Iso' Duration ℚ
asMinutes = iso ((÷ 60_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 60_000_000_000))

{- | (De)Construct a Duration from a number of minutes. -}
pattern MINS ∷ ℚ → Duration
pattern MINS n ← (view asMinutes → n)
        where MINS n = n ⫣ asMinutes
{-# COMPLETE MINS #-}

{- | A lens onto the minutes 'part' of the duration. -}
minutes ∷ Lens' Duration (𝕎 60)
minutes = lens (\ d   → let HMS_NS _ _ m _ _  = d in m)
               (\ d m → let HMS_NS g h _ s ns = d in HMS_NS g h m s ns)

minsTests ∷ TestTree
minsTests =
  let s3 = Duration 180_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration 3_723_123_456_789
      dur' = Duration 3_783_123_456_789
   in testGroup "minutes"
                [ testCase "2mins"    $ 𝕎 2 ≟ dur ⊣ minutes
                , testCase "mins → 3" $ dur' ≟ dur ⅋ minutes ⊢ 𝕎 3
                , testCase "3½mins" $
                      (3_499_999_999÷60_000_000_000)
                    ≟ Duration 3_499_999_999 ⊣ asMinutes
                , testCase "⅔us" $
                    Duration 40_000_000_000 ≟ ((two÷three) ⫣ asMinutes)
                , testCase "2mins" $
                    Duration 120_000_000_000 ≟ (2 ⫣ asMinutes)
                , testCase "3mins" $ f3 ≟ (\ (MINS n) → n) s3
                , testCase "3mins" $ s3 ≟ MINS f3
                ]

----------------------------------------

{- | View a duration as hours. -}
asHours ∷ Iso' Duration ℚ
asHours = iso ((÷ 3_600_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 3_600_000_000_000))

{- | (De)Construct a Duration from a number of hours. -}
pattern HOURS ∷ ℚ → Duration
pattern HOURS n ← (view asHours → n)
        where HOURS n = n ⫣ asHours
{-# COMPLETE HOURS #-}

{- | A lens onto the hours 'part' of the duration. -}
hours ∷ Lens' Duration (𝕎 2562048)
hours = lens (\ d   → let HMS_NS _ h _ _ _  = d in h)
             (\ d h → let HMS_NS g _ m s ns = d in HMS_NS g h m s ns)

hoursTests ∷ TestTree
hoursTests =
  let s3 = Duration 10_800_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration  3_723_123_456_789
      dur' = Duration 10_923_123_456_789
   in testGroup "hours"
                [ testCase "1hour"     $ 𝕎 1 ≟ dur ⊣ hours
                , testCase "hours → 3" $ dur' ≟ dur ⅋ hours ⊢ 𝕎 3
                , testCase "3½hours" $
                      (3_499_999_999÷3_600_000_000_000)
                    ≟ Duration 3_499_999_999 ⊣ asHours
                , testCase "⅔us" $
                    Duration 2_400_000_000_000 ≟ ((two÷three) ⫣ asHours)
                , testCase "2hours" $
                    Duration 7_200_000_000_000 ≟ (2 ⫣ asHours)
                , testCase "3hours" $ f3 ≟ (\ (HOURS n) → n) s3
                , testCase "3hours" $ s3 ≟ HOURS f3
                ]

----------------------------------------

{- | View a duration as days. -}
asDays ∷ Iso' Duration ℚ
asDays = iso ((÷ 86_400_000_000_000) ∘ fromInteger ∘ view asNanoseconds)
                  (Duration ∘ round ∘ (* 86_400_000_000_000))

{- | (De)Construct a Duration from a number of days. -}
pattern DAYS ∷ ℚ → Duration
pattern DAYS n ← (view asDays → n)
        where DAYS n = n ⫣ asDays
{-# COMPLETE DAYS #-}

{- | A lens onto the days 'part' of the duration. -}
days ∷ Lens' Duration (𝕎 106752)
days = lens (\ du → let DHMS_NS _ da _ _ _ _ = du in da)
             (\ du da → let DHMS_NS g _ h m s ns = du in DHMS_NS g da h m s ns)

daysTests ∷ TestTree
daysTests =
  let s3 = Duration 259_200_000_000_000
      f3 = 3 ∷ ℚ
      dur  = Duration 89_532_723_123_456_789
      dur' = Duration 281_523_123_456_789
   in testGroup "days"
                [ testCase "1,036days" $ 𝕎 1_036 ≟ dur ⊣ days
                , testCase "days → 3" $ dur' ≟ dur ⅋ days ⊢ 𝕎 3
                , testCase "3½days" $
                      (7÷2) ≟ Duration 302_400_000_000_000 ⊣ asDays
                , testCase "⅔us" $
                    Duration 57_600_000_000_000 ≟ ((two÷three) ⫣ asDays)
                , testCase "2days" $
                    Duration 172_800_000_000_000 ≟ (2 ⫣ asDays)
                , testCase "3days" $ f3 ≟ (\ (DAYS n) → n) s3
                , testCase "3days" $ s3 ≟ DAYS f3
                ]

--------------------

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

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- testdata ------------------------------------------------

two ∷ ℤ
two = 2

three ∷ ℤ
three = 3

------------------------------------------------------------

tests ∷ TestTree
tests =
  testGroup "Duration" [ textualTests, nsTests, μsTests, dhms_nsTests
                       , hms_nsTests, hms_msTests, msTests, secsTests
                       , minsTests, hoursTests, daysTests
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

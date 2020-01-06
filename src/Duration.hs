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
  ( Duration( HMS_MS, MS ), NumSign(..)
  , asMilliseconds, milliseconds, microseconds

  , tests
  )
where

import Prelude  ( Bounded( maxBound, minBound ), Double, Enum, Float, Fractional
                , Integral( quotRem, toInteger )
                , Num( (+), (-), (*), abs, fromInteger, negate, signum )
                , Real( toRational )
                , (^), div, divMod, fromIntegral, mod, realToFrac, round
                )

-- base --------------------------------

import Control.Applicative  ( pure, some )
import Control.Exception    ( ArithException( Overflow, Underflow ), throw )
import Control.Monad        ( Monad )
import Data.Bifunctor       ( bimap, second )
import Data.Bool            ( otherwise )
import Data.Eq              ( Eq )
import Data.Foldable        ( sum )
import Data.Function        ( ($), id )
import Data.Int             ( Int64 )
import Data.List            ( dropWhileEnd, reverse )
import Data.Maybe           ( Maybe( Just ) )
import Data.Ord             ( Ord, (<), (>) )
import Data.Ratio           ( Rational, (%) )
import Data.String          ( String )
import Data.Word            ( Word16, Word32, Word64 )
import System.Exit          ( ExitCode )
import System.IO            ( IO )
import Text.Read            ( read )
import Text.Show            ( Show )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≡) )
import Data.Function.Unicode  ( (∘) )
import Data.Ord.Unicode       ( (≥) )
import Prelude.Unicode        ( ℚ, ℤ )

-- boundedn ----------------------------

import BoundedN  ( 𝕎, pattern 𝕎 )
import FromI     ( __fromI' )
import ToNum     ( toNum, toNumI )

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

------------------------------------------------------------

type N60 = 𝕎 60

------------------------------------------------------------

type N24 = 𝕎 24

------------------------------------------------------------

type NE9 = 𝕎 1_000_000_000

------------------------------------------------------------

{- | Bounded to max. number of hours in a `Duration` (2,562,047). -}
type N2562047 = 𝕎 2562047

------------------------------------------------------------

{- | Bounded to max. number of days in a `Duration` (106,751). -}
type N106751 = 𝕎 106751

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
     in let suffix = if ns ≡ 𝕎 0
                     then ""
                     else pack $ '.' : dropWhileEnd (≡ '0')([fmt|%09d|] $ toNumI ns)
            sgn = if g ≡ MINUS then "-" else ""
         in if toNumI h > 0
            then P.text $ [fmt|%s%dh%02dm%02d%ts|] sgn (toNumI h) (toNumI m) (toNumI s) suffix
            else if m > 𝕎 0
                 then P.text $ [fmt|%s%dm%02d%ts|] sgn (toNumI m) (toNumI s) suffix
                 else P.text $ [fmt|%s%d%ts|] sgn (toNumI s) suffix

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
asMicroseconds = iso ((÷ 1_000) ∘ fromInteger ∘ view asNanoseconds)
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
                                in if u ≥ 1_000
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
                    Duration 667 ≟ ((two÷three) ⫣ asMicroseconds)
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
asMilliseconds = iso ((÷ 1_000_000) ∘ fromInteger ∘ view asNanoseconds)
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
                                in if m ≥ 1_000
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
                    Duration 666667 ≟ ((two÷three) ⫣ asMilliseconds)
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
hms_ns (Duration n) = let fromi ∷ (Integral ι, Integral κ, Num α, Num β) ⇒
                                  (ι,κ) → (α,β)
                          fromi (x,y) = (fromIntegral x, fromIntegral y)
                          (s∷Word64,ns)  = second __fromI' $ fromi $ abs n `divMod` 1_000_000_000
                          (m∷Word32,ss)  = second __fromI' $ fromi $ s `divMod` 60
                          (hh,mm)        = bimap __fromI' __fromI' $ fromi $ m `divMod` 60
                       in (toNumSign n,hh,mm,ss,ns)

hms_ns' ∷ NumSign → N2562047 → N60 → N60 → NE9 → Duration
hms_ns' sgn hh mm ss ns = let mm' ∷ ℕ
                              mm' = toNum mm
                              ss' ∷ ℕ
                              ss' = toNum ss
                              billℕ ∷ ℕ
                              billℕ = 1_000_000_000
                              ns' = toNum ns
                              n ∷ ℕ
                              n = fromIntegral $
                                    ns' + billℕ * (ss'+ 60*(mm'+60*(toNum hh)))
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
                [ testCase "→ HMS_NS" $ dur ≟ HMS_NS MINUS (𝕎 1) (𝕎 2) (𝕎 3) (𝕎 4)
                , testCase "g"  $ MINUS ≟ g
                , testCase "hh" $ 𝕎 1   ≟ hh
                , testCase "mm" $ 𝕎 2   ≟ mm
                , testCase "ss" $ 𝕎 3   ≟ ss
                , testCase "ns" $ 𝕎 4   ≟ ns
                ]

--------------------

{- | (De)Construct a Duration from Days, Hours, Minutes, Seconds &
     Nanoseconds. -}

dhms_ns ∷ Duration → (N106751,N24,N60,N60,NE9)
dhms_ns (Duration n) = let fromi ∷ (Integral ι, Integral κ, Num α, Num β) ⇒
                                   (ι,κ) → (α,β)
                           fromi (x,y) = (fromIntegral x, fromIntegral y)
                           (s∷Word64,ns)  = second __fromI' $ fromi $ n `divMod` 1_000_000_000
                           (m∷Word32,ss)  = second __fromI' $ fromi $ s `divMod` 60
                           (h∷Word32,mm)  = second __fromI' $ fromi $ m `divMod` 60
                           (dd,hh)        = bimap __fromI' __fromI' $ fromi $ h `divMod` 24
                        in (dd,hh,mm,ss,ns)

pattern DHMS_NS ∷ N106751 → N24 → N60 → N60 → NE9 → Duration
pattern DHMS_NS dd hh mm ss ns ← (dhms_ns → (dd,hh,mm,ss,ns))
        where DHMS_NS dd hh mm ss ns =
                let hh' ∷ ℕ
                    hh' = toNum hh
                    mm' ∷ ℕ
                    mm' = toNum mm
                    ss' ∷ ℕ
                    ss' = toNum ss
                    billℕ ∷ ℕ
                    billℕ = 1_000_000_000
                    ns' = toNum ns
                    n ∷ ℕ
                    n = fromIntegral $
                          ns' + billℕ * (ss'+ 60*(mm'+60*(hh'+24*toNum dd)))
                 in if n > fromIntegral (maxBound @Word64)
                    then throw Overflow
                    else Duration $ fromIntegral n

dhms_nsTests ∷ TestTree
dhms_nsTests =
  let dur = Duration 93_784_000_000_005
      DHMS_NS dd hh mm ss ns = dur
   in testGroup "DHMS_NS"
                [ testCase "→ DHMS_NS" $ dur ≟ DHMS_NS (𝕎 1) (𝕎 2) (𝕎 3) (𝕎 4) (𝕎 5)
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

hms_ms ∷ Duration → (NumSign,N2562047,N60,N60,𝕎 1000)
hms_ms d = let HMS_NS g hh mm ss ns = d
            in (g,hh,mm,ss,𝕎 (round $ toNumI ns ÷ 1_000_000))

pattern HMS_MS ∷ NumSign → N2562047 → N60 → N60 → 𝕎 1000 → Duration
pattern HMS_MS g hh mm ss ms ← (hms_ms → (g,hh,mm,ss,ms))
        where HMS_MS g hh mm ss ms = HMS_NS g hh mm ss (__fromI' $ toNum ms * 1_000_000)

hms_msTests ∷ TestTree
hms_msTests =
  let dur  = Duration 4_834_567_567_123
      dur' = Duration (-4_834_568_000_000)
      HMS_MS g hh mm ss ms = dur
   in testGroup "HMS_MS"
                [ testCase "hms_ms"   $  (PLUS,𝕎 1,𝕎 20,𝕎 34,𝕎 568) ≟ hms_ms dur
                , testCase "→ HMS_MS" $  dur' ≟ HMS_MS MINUS (𝕎 1) (𝕎 20) (𝕎 34) (𝕎 568)
                , testCase "g"        $ PLUS  ≟ g
                , testCase "hh"       $ 𝕎   1 ≟ hh
                , testCase "mm"       $ 𝕎  20 ≟ mm
                , testCase "ss"       $ 𝕎  34 ≟ ss
                , testCase "ms"       $ 𝕎 568 ≟ ms
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

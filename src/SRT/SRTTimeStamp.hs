{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UnicodeSyntax              #-}

module SRT.SRTTimeStamp
  ( SRTTimeStamp( unSRTTimeStamp ), tests )
where

import Prelude  ( Enum, Fractional( (/), fromRational )
                , Integral( quotRem, toInteger )
                , Num( (+), (-), (*), abs, signum , fromInteger, negate )
                , Real
                , (/), fromIntegral, round
                )

-- base --------------------------------

import Control.Exception  ( ArithException( Underflow ), throw )
import Data.Either        ( Either( Right ) )
import Data.Eq            ( Eq )
import Data.Function      ( ($), id )
import Data.Maybe         ( Maybe( Just ) )
import Data.Ord           ( Ord )
import Data.Ratio         ( (%) )
import Data.String        ( String )
import System.Exit        ( ExitCode )
import System.IO          ( IO )
import Text.Show          ( Show )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode        ( (≡) )
import Data.Function.Unicode  ( (∘) )
import Prelude.Unicode        ( ℤ )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ), Textual( textual ), fromText,toText )

-- duration ----------------------------

import Duration  ( Duration( HMS_MS, MS ), asMilliseconds )

-- finite-typelits ---------------------

import Data.Finite  ( Finite, getFinite )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFunctor( omap ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Functor  ( (⊳) )
import Data.MoreUnicode.Lens     ( (⫣), (⫥) )
import Data.MoreUnicode.Natural  ( ℕ )

-- number ------------------------------

import Number  ( NumSign( MINUS ) )

-- parsec-plus -------------------------

import ParsecPlus  ( Parsecable( parsec, parser ), ParseError )

-- QuickCheck --------------------------

import Test.QuickCheck.Arbitrary  ( Arbitrary( arbitrary )
                                  , arbitraryBoundedIntegral )

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

import Data.Text  ( Text )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Shifty  ( Shifty( shift ) )
import SRT.Skew    ( Skew( MS_S, unSkew ) )

--------------------------------------------------------------------------------

newtype SRTTimeStamp = SRTTimeStamp { unSRTTimeStamp ∷ Duration }
  deriving (Enum, Eq, Ord, Real, Show)

type instance Element SRTTimeStamp = Duration

instance MonoFunctor SRTTimeStamp where
  omap ∷ (Duration → Duration) → SRTTimeStamp → SRTTimeStamp
  omap f (SRTTimeStamp d) = SRTTimeStamp (f d)

instance Shifty SRTTimeStamp where
  shift ∷ Duration → Skew → SRTTimeStamp → SRTTimeStamp
  shift offst mult (SRTTimeStamp ts) =
    let (MS ms) = ts+offst in fromInteger (round $ ms*(unSkew mult))

{- | We provide our own `Num` instance so we can convert to/from milliseconds.
 -}
instance Integral SRTTimeStamp where
  quotRem (SRTTimeStamp (MS ms)) (SRTTimeStamp (MS ms')) =
    let (q,r) = (round ms ∷ ℤ) `quotRem` (round ms' ∷ ℤ)
     in (SRTTimeStamp $ MS (q%1), SRTTimeStamp $ MS (r%1))
--  quotRem _ _ = ePatSymExhaustive "SRTTimeStamp quotRem"

  toInteger (SRTTimeStamp (MS ms)) = round ms
--  toInteger (SRTTimeStamp _) = ePatSymExhaustive "SRTTimeStamp toInteger"

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
     in P.text $ [fmt|%s%02n:%02n:%02n,%03n|]
                 (if g ≡ MINUS then "-" else "") h m s ms

instance Textual SRTTimeStamp where
  textual = SRTTimeStamp ⊳ textual

instance Parsecable SRTTimeStamp where
  parser = textual

instance Arbitrary SRTTimeStamp where
  arbitrary = SRTTimeStamp ∘ (⫣ asMilliseconds) ∘ (%1) ∘ getFinite ⊳
                arbitraryBoundedIntegral @(Finite 360_000_000)

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test data -----------------------------------------------

srtTimestamp ∷ Text
srtTimestamp = "01:20:34,567"

srtTimestampRef ∷ SRTTimeStamp
srtTimestampRef = SRTTimeStamp (MS 4834_567)

------------------------------------------------------------

tests ∷ TestTree
tests =
  let s1 = 5_025_678 ∷ SRTTimeStamp -- 1h23m45s678
      s2 = 9_296_789 ∷ SRTTimeStamp -- 2h34m56s789
   in testGroup "SRTTimeStamp"
                [ testCase "toText s1" $   "01:23:45,678" ≟ toText s1
                , testCase "toText s2" $   "02:34:56,789" ≟ toText s2
                , testCase "s1+s2"     $   "03:58:42,467" ≟ toText (s1 + s2)
                , testCase "s2-s1"     $   "01:11:11,111" ≟ toText (s2 - s1)
                , testCase "s1*2"      $   "03:58:42,467" ≟ toText (s1 + s2)
                , testCase "quotRem" $ (4,3) @=? (19 ∷ SRTTimeStamp) `quotRem` 4
                , testCase "fromText"  $     Just srtTimestampRef
                                         @=? fromText srtTimestamp
                , testCase "toText"    $ srtTimestamp ≟ toText srtTimestampRef
                , testCase "toText"    $ srtTimestamp ≟ toText srtTimestampRef
                , testCase "parsec"    $
                        Right (SRTTimeStamp 4834_567_000_000)
                    @=? parsec @SRTTimeStamp @ParseError @(Either ParseError)
                               @Text @String "srtTimestamp" srtTimestamp
                , testProperty "invertibleText"
                               (propInvertibleText @SRTTimeStamp)
                , testCase "shift" $
                      -- 100 ms/s
                      "01:32:09,346" ≟ toText (shift (MS 1_000) (MS_S 100) s1)
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

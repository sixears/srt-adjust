{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE UnicodeSyntax      #-}
{-# LANGUAGE ViewPatterns       #-}

module SRT.Skew
  ( Skew( MS_S, Skew, unSkew ), to_ms_s )
where

import Prelude  ( Fractional( (/) ), Num( (+), (-), (*) ), (/) )

-- base --------------------------------

import Data.Eq        ( Eq )
import Data.Function  ( ($) )
import Text.Show      ( Show )

-- base-unicode-symbols ----------------

import Prelude.Unicode  ( ℚ )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

{- | Speed factor for timestamps as a multiplicative ratio. -}
newtype Skew = Skew { unSkew ∷ ℚ }
  deriving (Eq, Show)

to_ms_s ∷ Skew → ℚ
to_ms_s (Skew s) = (s-1) * 1_000

{- | (De)Construct a speed factor from milliseconds-per-second gain or loss.
     Thus, 100 ⇒ 100ms/s ⇒ 1.1; -100 ⇒ -100ms/s ⇒ 0.9 -}
pattern MS_S ∷ ℚ → Skew
pattern MS_S s ← (to_ms_s → s)
        where MS_S s = Skew $ 1+(s/1_000)

-- that's all, folks! ----------------------------------------------------------


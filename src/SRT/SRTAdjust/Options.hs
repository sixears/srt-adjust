{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}

module SRT.SRTAdjust.Options
  ( adj, infns, parseOptions )
where

-- base --------------------------------

import Control.Applicative  ( many )
import Data.Bifunctor       ( bimap )
import Data.Char            ( Char )
import Data.Function        ( ($) )
import Text.Show            ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Monoid.Unicode  ( (⊕) )
import Prelude.Unicode      ( ℚ )

-- data-textual ------------------------

import Data.Textual.Fractional  ( Optional( Optional ), decExpSign, fractional'
                                , optSign )
import Data.Textual.Integral    ( Decimal( Decimal ) )

-- duration ----------------------------

import Duration  ( Duration )

-- fpath -------------------------------

import FPath.File  ( File )

-- lens --------------------------------

import Control.Lens.Lens    ( Lens', lens )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋫), (∤) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Monoid       ( ф, ю )

-- options-applicative -----------------

import Options.Applicative  ( ArgumentFields, Mod, Parser, ReadM
                            , action, eitherReader, long, metavar, option
                            , optional, pure, short, value
                            )

-- optparse-plus -----------------------

import OptParsePlus  ( argT, optT )

-- parsec ------------------------------

import Text.Parsec.Prim  ( ParsecT, Stream, parse )

-- parsers -----------------------------

import Text.Parser.Char  ( char )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Skew             ( Skew( MS_S ) )
import SRT.SRTAdjust.Types  ( AdjustmentOpts( AdjDelOff, AdjMarkers ), Marker )

--------------------------------------------------------------------------------

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

parseFile ∷ Mod ArgumentFields File → Parser File
parseFile ms = argT (action "file" ⊕ metavar "FILE" ⊕ ms)

-- that's all, folks! ----------------------------------------------------------

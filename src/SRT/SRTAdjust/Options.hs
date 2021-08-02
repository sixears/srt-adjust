{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE UnicodeSyntax     #-}

module SRT.SRTAdjust.Options
  ( adj, infns, optsParse )
where

-- base --------------------------------

import Control.Applicative  ( many )
import Control.Monad        ( return, sequence )
import Data.Bifunctor       ( bimap )
import Data.Char            ( Char )
import Data.Function        ( ($) )
import Text.Show            ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Monoid.Unicode  ( (⊕) )
import Prelude.Unicode      ( ℚ )

-- data-textual ------------------------

import Data.Textual             ( toString )
import Data.Textual.Fractional  ( Optional( Optional ), decExpSign, fractional'
                                , optSign )
import Data.Textual.Integral    ( Decimal( Decimal ) )

-- duration ----------------------------

import Duration  ( Duration )

-- fpath -------------------------------

import FPath.AbsFile           ( AbsFile )
import FPath.Error.FPathError  ( AsFPathError )

-- lens --------------------------------

import Control.Lens.Lens    ( Lens', lens )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( AsIOError )

-- monadio-plus ------------------------

import MonadIO        ( MonadIO )
import MonadIO.FPath  ( pResolve )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋫), (∤) )
import Data.MoreUnicode.Functor      ( (⊳) )
import Data.MoreUnicode.Monad        ( (≫) )
import Data.MoreUnicode.Monoid       ( ф, ю )

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError )

-- optparse-applicative ----------------

import Options.Applicative  ( ArgumentFields, Mod, Parser, ReadM
                            , action, eitherReader, long, metavar, option
                            , optional, progDesc, pure, short, strArgument
                            , value
                            )

-- optparse-plus -----------------------

import OptParsePlus  ( optT, parseOpts )

-- parsec ------------------------------

import Text.Parsec.Prim  ( ParsecT, Stream, parse )

-- parsers -----------------------------

import Text.Parser.Char  ( char )

-- text --------------------------------

import Data.Text  ( Text )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Skew             ( Skew( MS_S ) )
import SRT.SRTAdjust.Types  ( AdjustmentOpts( AdjDelOff, AdjMarkers ), Marker )

--------------------------------------------------------------------------------

type family ResolvesTo α
class Resolvable α where
  resolve ∷ (MonadIO μ, AsFPathError ε, AsIOError ε, MonadError ε μ) ⇒
            α → μ (ResolvesTo α)

type instance ResolvesTo Text = AbsFile
instance Resolvable Text where
  resolve ∷ (MonadIO μ, AsFPathError ε, AsIOError ε, MonadError ε μ) ⇒
            Text → μ AbsFile
  resolve = pResolve

------------------------------------------------------------

class HasAdjustmentOpts α where
  adj ∷ Lens' α AdjustmentOpts

data Options' = Options' { _infns' ∷ [Text]
                         , _adj'   ∷ AdjustmentOpts
                         }

instance HasAdjustmentOpts Options' where
  adj = lens _adj' (\ o a → o { _adj' = a })

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


parseOptions' ∷ Parser Options'
parseOptions' = Options' ⊳ many (parseFile ф) ⊵ (parseMarkers ∤ parseDelOff)

parseFile ∷ Mod ArgumentFields Text → Parser Text
parseFile ms = strArgument (action "file" ⊕ metavar "FILE" ⊕ ms)

------------------------------------------------------------

data Options = Options { _infns ∷ [AbsFile]
                       , _adj   ∷ AdjustmentOpts
                       }

infns ∷ Lens' Options [AbsFile]
infns = lens _infns (\ o is → o { _infns = is })

instance HasAdjustmentOpts Options where
  adj = lens _adj (\ o a → o { _adj = a })

type instance ResolvesTo Options' = Options
instance Resolvable Options' where
  resolve (Options' is' a) = do is ← sequence $ resolve ⊳ is'
                                return $ Options is a

optsParse ∷ (MonadIO μ, AsFPathError ε, AsIOError ε, MonadError ε μ) ⇒
            Text → μ Options
optsParse descn = parseOpts (progDesc $ toString descn) parseOptions' ≫ resolve

-- that's all, folks! ----------------------------------------------------------

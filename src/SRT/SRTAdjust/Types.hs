{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE UnicodeSyntax     #-}

module SRT.SRTAdjust.Types
  ( AdjustmentOpts(..), Marker, mtext, position )
where

-- base --------------------------------

import Control.Applicative  ( many )
import Data.Eq              ( Eq )
import Data.Function        ( ($) )
import Data.Maybe           ( Maybe( Just, Nothing ) )
import Text.Show            ( Show )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ) , Textual( textual ) )

-- duration ----------------------------

import Duration  ( Duration )

-- lens --------------------------------

import Control.Lens.Lens    ( Lens', lens )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⊵), (⋫) )
import Data.MoreUnicode.Functor      ( (⊳) )

-- parsers -----------------------------

import Text.Parser.Char  ( anyChar, char )

-- text --------------------------------

import Data.Text     ( Text, pack )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Skew          ( Skew )
import SRT.SRTTimeStamp  ( SRTTimeStamp )

--------------------------------------------------------------------------------

------------------------------------------------------------
--                        Options                         --
------------------------------------------------------------

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

------------------------------------------------------------

data AdjustmentOpts = AdjDelOff  { _d ∷ Skew  , _o ∷ Duration }
                    | AdjMarkers { _m1 ∷ Marker, _m2 ∷ Maybe Marker }

-- that's all, folks! ----------------------------------------------------------

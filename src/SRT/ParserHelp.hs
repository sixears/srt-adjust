{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}

module SRT.ParserHelp
  ( nl, whitespaces )
where

-- base --------------------------------

import Control.Applicative  ( many )
import Control.Monad        ( Monad, return )
import Data.Function        ( ($) )
import Data.String          ( String )

-- parsers -----------------------------

import Text.Parser.Char         ( CharParsing, char, oneOf )
import Text.Parser.Combinators  ( (<?>), skipOptional )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⋫) )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

-- `Text.Parser.Char.spaces` parses *all* spaces, including newline.  That's not
-- what we need for parsing/skipping spaces at the end of the line, hence this
-- function
whitespaces ∷ CharParsing η ⇒ η String
whitespaces = many $ oneOf " \t"

-- Parse a newline, optionally preceded by a carriage-return
-- (flucking windoze...)
nl ∷ (CharParsing η, Monad η) ⇒ η ()
nl = skipOptional (char '\r') ⋫ char '\n' ⋫ return () <?> "cr/nl"

-- that's all, folks! ----------------------------------------------------------

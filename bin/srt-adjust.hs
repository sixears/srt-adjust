{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UnicodeSyntax         #-}

-- TODO:
-- add completion for duration/timestamp?
-- add completion for marker texts?

import Prelude  ( Int, floor )

-- base --------------------------------

import Control.Monad  ( forM_, return )
import Data.Function  ( ($) )
import Data.Maybe     ( Maybe( Just, Nothing ) )
import System.Exit    ( ExitCode( ExitSuccess ) )
import System.IO      ( IO )

-- base-unicode-symbols ----------------

import Data.Function.Unicode  ( (∘) )

-- duration ----------------------------

import Duration  ( Duration( MS ) )

-- exited ------------------------------

import Exited  ( doMain )

-- fpath -------------------------------

import FPath.File  ( File( FileA ) )

-- monadio-plus ------------------------

import MonadIO  ( say, warn )

-- more-unicode ------------------------

import Data.MoreUnicode.Functor  ( (⊳) )
import Data.MoreUnicode.Lens     ( (⊣) )

-- parsec-plus -------------------------

import Parsec.FPathParseError  ( FPathIOParseError )
import ParsecPlus              ( parsecFUTF8L  )

-- tfmt --------------------------------

import Text.Fmt  ( fmtT )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.SRTAdjust          ( optionsAdjust )
import SRT.SRTAdjust.Options  ( adj, infns, optsParse )
import SRT.Shifty             ( Shifty( shift ) )
import SRT.Skew               ( to_ms_s )

--------------------------------------------------------------------------------

main ∷ IO ()
main = doMain @FPathIOParseError $ do
  opts ← optsParse Nothing "greet thee all"

  let fns = case opts ⊣ infns of
              [] → [Nothing] -- read stdin
              xs → (Just ∘ FileA) ⊳ xs

  forM_ fns $ \ fn → do
    seq ← parsecFUTF8L fn

    (del,off) ← optionsAdjust seq fn $ opts ⊣ adj
    let MS off_ms = off
    warn $ [fmtT|Using offset %dms, delay %fms/s|] (floor @_ @Int off_ms)
                                                   (to_ms_s del)

    say $ shift off del seq


  return ExitSuccess

-- that's all, folks! ----------------------------------------------------------

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
import System.Exit    ( ExitCode( ExitSuccess ) )
import System.IO      ( IO )

-- duration ----------------------------

import Duration  ( Duration( MS ) )

-- exited ------------------------------

import Exited  ( doMain )

-- fpath -------------------------------

import FPath.AbsFile  ( absfile )
import FPath.File     ( File( FileA ) )

-- monadio-plus ------------------------

import MonadIO  ( say, warn )

-- more-unicode ------------------------

import Data.MoreUnicode.Functor  ( (⊳) )
import Data.MoreUnicode.Lens     ( (⊣) )

-- parsec-plus -------------------------

import Parsec.FPathParseError  ( FPathIOParseError )
import ParsecPlus              ( parsecFileUTF8L  )

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
  opts ← optsParse "greet thee all"

  let fns = case opts ⊣ infns of
              [] → [FileA [absfile|/dev/stdin|]] -- read stdin
              xs → FileA ⊳ xs

  forM_ fns $ \ fn → do
    seq ← parsecFileUTF8L fn

    (del,off) ← optionsAdjust seq fn $ opts ⊣ adj
    let MS off_ms = off
    warn $ [fmtT|Using offset %dms, delay %fms/s|] (floor @_ @Int off_ms)
                                                   (to_ms_s del)

    say $ shift off del seq


  return ExitSuccess

-- that's all, folks! ----------------------------------------------------------

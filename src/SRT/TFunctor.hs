{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnicodeSyntax     #-}

module SRT.TFunctor
  (  TFunctor( tmap ) )
where

-- text --------------------------------

import Data.Text  ( Text )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

{- | A `MonoFunctor` over Text; defined explicitly to allow types to be an
     instance of this as well as a regular MonoFunctor -}
class TFunctor α where
  tmap ∷ (Text → Text) → α → α

-- that's all, folks! ----------------------------------------------------------

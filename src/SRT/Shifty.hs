{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE UnicodeSyntax      #-}

module SRT.Shifty
  ( Shifty( shift ) )
where

-- duration ----------------------------

import Duration  ( Duration )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import SRT.Skew( Skew )

--------------------------------------------------------------------------------

class Shifty α where
  shift ∷ Duration → Skew → α → α

-- that's all, folks! ----------------------------------------------------------


{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module X86 where

import qualified Prelude
import qualified Control
import qualified IO

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Types
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

x86Main :: IO.IO ()
x86Main =
  Control.pure (unsafeCoerce IO.coq_IO_Applicative) ()


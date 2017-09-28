{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module IO where

import qualified Prelude
import qualified Control
import qualified WEq

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

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Types.Any
#else
-- HUGS
type Any = ()
#endif

type IO a = Prelude.IO a

coq_IO_WEq :: (WEq.WEq a1) -> WEq.WEq (IO a1)
coq_IO_WEq =
  Prelude.error "AXIOM TO BE REALIZED"

io_map :: (a1 -> a2) -> (IO a1) -> IO a2
io_map = Prelude.fmap

io_pure :: a1 -> IO a1
io_pure = Prelude.pure

io_apply :: (IO (a1 -> a2)) -> (IO a1) -> IO a2
io_apply = (Prelude.<*>)

coq_IO_Functor :: Control.Functor (IO Any)
coq_IO_Functor =
  Control.Build_Functor (\_ -> coq_IO_WEq) (\_ _ -> io_map)

coq_IO_Applicative :: Control.Applicative (IO Any)
coq_IO_Applicative =
  Control.Build_Applicative coq_IO_Functor (\_ -> io_pure)
    (unsafeCoerce (\_ _ -> io_apply))


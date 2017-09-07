module Lib
    ( libMain
    ) where

import CoqMain (coq_coq_main)

libMain :: IO ()
libMain = coq_coq_main

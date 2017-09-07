Require Import FreeSpec.Control.IO.

Extract Constant IO "a" => "Prelude.IO a".
Extract Constant io_map => "Prelude.fmap".
Extract Constant io_pure => "Prelude.pure".
Extract Constant io_apply => "(Prelude.<*>)".
Extract Constant io_bind => "(Prelude.>>=)".
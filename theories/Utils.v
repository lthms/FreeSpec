Require Import Sumbool.

Notation "'true_dec'" := (left _ _).
Notation "'false_dec'" := (right _ _).
Notation "'and_dec' x y" := (sumbool_and _ _ _ _ x y)
                              (at level 43).
Notation "'or_dec' x y" := (sumbool_or _ _ _ _ x y)
                             (at level 43).
Notation "'decide_dec' x" := (if x then
    true_dec
  else
    false_dec) (at level 42).

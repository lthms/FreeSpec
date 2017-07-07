Require Import FreeSpec.TemporalLogic.

(** We define several notation to make a formula more readable. These
    notations are obviously optional, but they can help to have a
    cleaner code. The risk, however, is that you code will not be
    readable if the unicode characters are not supported by the font
    used to render them.

 *)

Notation "⬜ p" := (globally p) (at level 70): formula_scope.
Notation "◊ p" := (eventually p) (at level 70): formula_scope.
Notation "⃝ p" := (next p) (at level 70): formula_scope.
Notation "⟙" := (ltrue) (at level 70): formula_scope.
Notation "⟘" := (lfalse) (at level 70): formula_scope.
Notation "f1 ⊢ p ⟶ f2" := (switch f1 p f2) (at level 70): formula_scope.
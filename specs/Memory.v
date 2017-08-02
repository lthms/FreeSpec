Require Import FreeSpec.Libs.Vector.Vector.
Require Import FreeSpec.Specs.Hexa.
Require Import Omega.
Require Import Coq.Program.Program.

Definition mem := vector bit.
Definition carry := bit.

Definition byte  := mem 8.
Definition word  := mem 16.
Definition lword := mem 32.
Definition qword := mem 64.

Program Definition split_word
        (w: word)
  : { o: (byte * byte) | forall i, i < 16 -> nth w i = nth (append (fst o) (snd o)) i }:=
  (extract w 8 0, extract w 16 8).
Next Obligation.
  omega.
Defined.
Next Obligation.
  omega.
Defined.
Next Obligation.
  omega.
Defined.
Next Obligation.
  destruct append.
  cbn.
  destruct take.
  destruct drop.
  destruct take.
  cbn in *.
  destruct drop.
  cbn in *.
  assert (
      (i < 8 -> nth x i = nth x0 i) /\ (8 <= i -> nth x i = nth x2 (i - 8))
    ) as H0 by apply a.
  destruct H0.
  destruct (lt_dec i 8).
  + rewrite H0; [| exact l].
    rewrite e; [| exact l].
    rewrite e0; [| omega].
    reflexivity.
  + apply not_lt in n.
    rewrite H1; [| omega].
    remember (i - 8) as i'.
    assert (i = S (S (S (S (S (S (S (S i')))))))) by omega.
    rewrite H2.
    rewrite <- e2; [| omega].
    rewrite e1; [| omega].
    reflexivity.
Defined.
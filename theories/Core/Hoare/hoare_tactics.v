(** Reasoning with the [hoare] type has proven to be cumbersome to say the
    least. However, one can use the automation features of Coq to ease the
    verification process.

    More precisely, we implement several “angry”, ad-hoc tactics. *)

Lemma iff_p_p (p : Prop) : (p <-> p) <-> True.

Proof.
  now split.
Qed.

Lemma prop_and_neutral (p : Prop) : (True /\ p) <-> p.

Proof.
  now repeat split.
Qed.

Lemma imply_true_true (p : Type) : (p -> True) <-> True.

Proof.
  now repeat split.
Qed.

Lemma and_imply_equ (p q r : Prop) : (p /\ q -> r) <-> (p -> q -> r).

Proof.
  split.
  + intros H hp hq.
    apply H.
    now split.
  + intros H [hp hq].
    now apply H.
Qed.

Lemma alias_equ {a} (x : a) (p : a -> Prop)
  : (forall (y : a), y = x -> p y) <-> p x.

Proof.
  split.
  + intros H.
    now apply (H x).
  + intros hx y equ.
    now rewrite equ.
Qed.

Lemma forall_equ_2 {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (forall (x' : a) (y' : b), x = x' -> y = y' -> p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now apply H.
  + intros hxy x' y' equ1 equ2.
    now subst.
Qed.

Lemma forall_equ_2' {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (forall (x' : a) (y' : b), x' = x -> y' = y -> p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now apply H.
  + intros hxy x' y' equ1 equ2.
    now subst.
Qed.

Lemma exists_equ_2 {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (exists (x' : a) (y' : b), (x = x' /\ y = y') /\ p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now destruct H as [x' [y' [[equ1 equ2] H]]]; subst.
  + intros hxy.
    exists x.
    exists y.
    now split.
Qed.

Lemma exists_equ_2' {a b} (x : a) (y : b) (p : a -> b -> Prop)
  : (exists (x' : a) (y' : b), (x' = x /\ y' = y) /\ p x' y') <-> p x y.

Proof.
  split.
  + intros H.
    now destruct H as [x' [y' [[equ1 equ2] H]]]; subst.
  + intros hxy.
    exists x.
    exists y.
    now split.
Qed.

Lemma eq_sym_equ {a} (x y : a) : x = y <-> y = x.

Proof.
  now repeat split.
Qed.

Ltac angry_rewrite :=
  repeat (
      setoid_rewrite prop_and_neutral
      || setoid_rewrite imply_true_true
      || setoid_rewrite (and_comm _ True)
      || setoid_rewrite (and_comm _ (_ /\ _))
      || setoid_rewrite and_imply_equ
      || setoid_rewrite forall_equ_2
      || setoid_rewrite exists_equ_2
      || setoid_rewrite exists_equ_2'
      || setoid_rewrite iff_p_p
    ).

Ltac angry_destruct H :=
  match type of H with
  | _ /\ _ => let H' := fresh "H" in
              let H'' := fresh "H" in
              destruct H as [H' H''];
              angry_destruct H';
              angry_destruct H''
  | exists _, _ => let x := fresh "x" in
                   let H' := fresh "H" in
                   destruct H as [x H']; angry_destruct H'
  | _ => idtac
  end.

Ltac angry_intros :=
  let H := fresh "H" in
  intros H; angry_destruct H.

Ltac angry_exists :=
  repeat (eexists; eauto).

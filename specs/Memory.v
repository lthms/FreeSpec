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

Fixpoint vec_to_nat
         {n: nat}
         (v: mem n)
  : nat :=
  match v with
  | vnil => 0
  | vcons true rest => 1 + 2 * (vec_to_nat rest)
  | vcons false rest => 2 * (vec_to_nat rest)
  end.

Program Definition vec_to_nat'
        {n: nat}
        (v: mem n)
  : { m: nat | m < 2 ^ n } :=
  vec_to_nat v.
Next Obligation.
  induction v.
  + destruct a; cbn.
    ++ repeat rewrite OpenNat.add_0_r.
       apply OpenNat.lt_power_2.
       exact IHv.
    ++ repeat rewrite OpenNat.add_0_r.
       assert (S ((vec_to_nat v) + (vec_to_nat v)) < 2 ^ n+ 2 ^ n)
         by (apply (OpenNat.lt_power_2 (vec_to_nat v) n IHv)).
       apply Nat.lt_succ_l in H.
       exact H.
  + cbn.
    constructor.
Defined.

(** Right now, the [vec_to_nat] function is not efficient. It
    overflows with a big number, such as [Ox _FF_ _FF_]. The function
    [vec_to_nat'] can be used, but in addition to the flaw of
    [vec_to_nat], it is _very_ slow _very_ quickly.

 *)

Program Definition test_to_nat
  : nat
  := vec_to_nat (Ox _FF_).

Lemma test_to_nat_eq
  : test_to_nat = 255.
Proof.
  cbn.
  reflexivity.
Qed.

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

(** We add a test to check that split_works can indeed be evaluate by
    Coq.  If Coq hangs on that lemmas, it means we have introduced an
    opaque lemmas in a key proof obligation.

 *)

Program Definition test
  : byte * byte :=
  split_word (Ox _FA_ _AB_).

Program Lemma test_split
  : test = (Ox _AB_, Ox _FA_).
Proof.
  vm_compute. (* vm_compute works, not cbn *)
  reflexivity.
Qed.

(** * Addition

    Define an addition which can actually be evaluated by Coq.

 *)

Program Definition add_bit
        {a: Type}
        (b b': bit)
        (c: bool)
        (f: bit -> bool -> a)
  : a :=
  match b, b', c with
  | false, false, false => f false false
  | false, true, false => f true false
  | true, false, false => f true false
  | true, true, false => f false true
  | false, false, true => f false true
  | false, true, true => f false true
  | true, false, true => f false true
  | true, true, true => f true true
  end.

Program Fixpoint add_rec
        {A: Type}
        {n: nat}
        (o o': mem n)
        (f: mem (S n) -> bool -> A)
        (b: bit)
        (c: bool)
        {measure n}
  : A :=
  match n with
  | 0 => f (vcons b vnil) c
  | S m => add_bit (@head bit m o) (@head bit m o') c (@add_rec A m (drop o 1) (drop o' 1) (fun v c' => f (vcons b v) c')) _
  end.
Next Obligation.
  apply le_n_S.
  apply Peano.le_0_n.
Defined.
Next Obligation.
  cbn.
  apply OpenNat.sub_0_r.
Defined.
Next Obligation.
  apply le_n_S.
  apply Peano.le_0_n.
Defined.
Next Obligation.
  cbn.
  apply OpenNat.sub_0_r.
Defined.

Program Definition add
        {n: nat}
        (o o': mem n)
  : mem n * bool :=
  match n with
  | 0 => (vnil, false)
  | S m => add_bit (@head bit m o) (@head bit m o') false (add_rec (drop o 1) (drop o' 1) (fun v c' => (v, c')))
  end.
Next Obligation.
  apply le_n_S.
  apply Peano.le_0_n.
Defined.
Next Obligation.
  cbn.
  rewrite OpenNat.sub_0_r.
  reflexivity.
Defined.

(** We add this test lemma to check that the addition can actually be
    evaluated properly.

 *)

Definition test_ff
  : (mem 8 * bool) :=
  add (Ox _FE_) (Ox _01_).

Fact test_ff_eq
  : fst test_ff = Ox _FF_.
Proof.
  vm_compute.
  reflexivity.
Qed.
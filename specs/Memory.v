Require Import FreeSpec.Libs.OpenNat.OpenNat.
Require Import FreeSpec.PropBool.
Require Import Coq.Program.Program.
Require Import Coq.Arith.Arith.

(** * Definitions

 *)

Program Record mem
        (n: nat)
  : Type :=
  mkMem { mem_val: nat
        ; mem_bound: mem_val < 2 ^ n
        }.

Arguments mem_val [n] (_).
Arguments mem_bound [n] (_).

Definition byte := mem 8.
Definition word := mem 16.
Definition lword := mem 32.
Definition qword := mem 64.

Notation "x 'Byte'" := (x * 8) (at level 30, no associativity).
Notation "x 'Bytes'" := (x * 8) (at level 30, no associativity).

(** * Manipulation

    ** Boxing

 *)

Program Definition box
        (n x: nat)
  : mem n :=
  {| mem_val := x mod (2 ^ n)
   ; mem_bound := _
   |}.
Next Obligation.
  apply Nat.mod_bound_pos.
  + apply OpenNat.le_0_n.
  + assert (G: forall z, 0 < 2 ^ z). {
      clear x.
      induction z.
      + constructor.
      + cbn.
        rewrite OpenNat.add_0_r.
        rewrite <- OpenNat.add_0_r at 1.
        unfold lt.
        rewrite <- OpenNat.add_succ_l.
        apply OpenNat.add_le_mono.
        ++ apply OpenNat.le_0_n.
        ++ exact IHz.
    }
    exact (G n).
Defined.

Definition zero
           (n: nat)
  : mem n :=
  box n 0.

(** ** Unboxing

 *)

Definition unbox
        {n: nat}
        (x: mem n)
  : nat :=
  mem_val x.

Definition cast
           {n: nat}
           (m: nat)
           (x: mem n)
  : mem m :=
  box m (unbox x).

(** ** Arithmetic

 *)

Definition add
           {n: nat}
           (x y: mem n)
  : mem n :=
  box n (unbox x + unbox y).

Definition shiftl
           {n: nat}
           (x: mem n)
           (b: nat)
  : mem n :=
    box n (Nat.shiftl (unbox x) b).

Definition shiftr
           {n: nat}
           (x: mem n)
           (b: nat)
  : mem n :=
    box n (Nat.shiftr (unbox x) b).

Definition mle
           {n: nat}
           (x y: mem n)
  : Prop :=
  unbox x <= unbox y.

Definition mleb
           {n: nat}
           (x y: mem n)
  : bool :=
  unbox x <=? unbox y.

Definition mltb
           {n: nat}
           (x y: mem n)
  : bool :=
  unbox x <? unbox y.

(** * Memory

 *)

Inductive Endianness : Type := BE | LE.

Local Open Scope list_scope.

Fixpoint split
         (n: nat)
         (x: mem (8 * n))
         {struct n}
  : list byte :=
  match n with
  | 0 => []
  | S m => (cast 8 x)::(split m (cast (8 * m) (shiftr x 8)))
  end.

Program Definition split_word
        (x: word)
  : byte * byte :=
  match split 2 x with
  | b1 :: b2 :: nil => (b1, b2)
  | _ => !
  end.
Next Obligation.
  assert ([cast 8 x; cast 8 (cast 8 (shiftr x 8))] <> [cast 8 x; cast 8 (cast 8 (shiftr x 8))])
    by apply H.
  destruct H0.
  reflexivity.
Defined.

Program Definition split_lword
        (x: lword)
  : byte * byte * byte * byte :=
  match split 4 x with
  | b1 :: b2 :: b3 :: b4 :: nil => (b1, b2, b3, b4)
  | _ => !
  end.
Next Obligation.
  assert (
      [cast 8 x; cast 8 (cast 24 (shiftr x 8));
      cast 8 (cast 16 (shiftr (cast 24 (shiftr x 8)) 8));
      cast 8 (cast 8 (shiftr (cast 16 (shiftr (cast 24 (shiftr x 8)) 8)) 8))]
        <>
      [cast 8 x; cast 8 (cast 24 (shiftr x 8));
      cast 8 (cast 16 (shiftr (cast 24 (shiftr x 8)) 8));
      cast 8 (cast 8 (shiftr (cast 16 (shiftr (cast 24 (shiftr x 8)) 8)) 8))]
    )
    by apply H.
  destruct H0.
  reflexivity.
Defined.

(** * Manipulation

  *)

Definition append
           {n m:  nat}
           (v:    mem n)
           (v':   mem m)
  : mem (n + m) :=
  add (shiftl (cast (n + m) v') n)
      (cast (n + m) v).

Program Definition extract
        {n:           nat}
        (m:           mem n)
        (offset:      nat | offset <= n)
        (size:        nat | offset + size <= n)
  : mem size :=
  cast size (shiftr m offset).
Require Import Coq.Arith.Arith.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Function.
Require Import FreeSpec.MonadInterp.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.
Require Import Omega.

Local Open Scope free_weq_scope.
Local Open Scope free_control_scope.

Inductive MSi
          (n:  nat)
  : Interface :=
| read_byte (addr:  mem n)
  : MSi n byte
| read_word (addr:  mem n)
  : MSi n word
| read_lword (addr:  mem n)
  : MSi n lword
| write_byte (addr:  mem n)
             (val:   byte)
  : MSi n unit
| write_word (addr:  mem n)
             (val:   word)
  : MSi n unit
| write_lword (addr:  mem n)
              (val:   lword)
  : MSi n unit.

Arguments read_byte  {n} (addr).
Arguments read_word  {n} (addr).
Arguments read_lword {n} (addr).
Arguments write_byte  {n} (addr val).
Arguments write_word  {n} (addr val).
Arguments write_lword {n} (addr val).

Definition MSs
           (n:  nat)
  := mem n
     -> byte.

Definition MSs_weq
           {n:             nat}
           (store store':  MSs n)
  : Prop :=
  forall (addr: mem n),
    store addr == store' addr.

Instance MSs_WEq
         (n:  nat)
  : WEq (MSs n) :=
  { weq := @MSs_weq n
  }.

Definition MSs_init
           (n:  nat)
  : MSs n :=
  pure (0: byte).

Definition nxt
           {n:  nat}
           (x:  mem n)
  : mem n :=
  add x (box n 1).

Lemma nxt_neq
      {n:  nat}
      (x:  mem n)
      (H:  1 < n)
  : ~ weq x (nxt x).
Proof.
  unfold nxt.
  unfold add.
  unfold box, unbox.
  intros [Heq].
  destruct x as [x Hx].
  unfold mem_val in Heq.
  rewrite Nat.mod_1_l in Heq.
  + destruct (Nat.eq_dec (x + 1) (2 ^ n)).
    ++ rewrite e in Heq.
       rewrite Nat.mod_same in Heq.
       subst.
       rewrite Nat.add_0_l in e.
       assert (Hn:  n = 0). {
         rewrite <- (Nat.pow_0_r 2) in e at 1.
         apply Nat.pow_inj_r in e.
         symmetry; exact e.
         omega.
       }
       subst.
       inversion H.
       apply Nat.neq_sym.
       apply lt_0_neq.
       apply pow_pos.
       omega.
    ++ assert (Hn:  x + 1 < 2 ^ n) by omega.
       rewrite Nat.mod_small in Heq; [| exact Hn ].
       omega.
  + apply Nat.pow_gt_1; omega.
Qed.

Definition MS_interp
           {n:  nat}
           {A:  Type}
           (i:  MSi n A)
  : State (MSs n) A :=
  match i with
  | read_byte addr
    => gets (fun store
             => store addr)
  | read_word addr
    => gets (fun store
             => join_bytes_to_word (store (nxt addr))
                                   (store addr))
  | read_lword addr
    => gets (fun store
             => join_bytes_to_lword (store (nxt (nxt (nxt addr))))
                                    (store (nxt (nxt addr)))
                                    (store (nxt addr))
                                    (store addr))
  | write_byte addr val
    => modify (fun store
               => fun addr'
                  => if addr' ?= addr
                     then val
                     else store addr')
  | write_word addr val
    => modify (fun store
               => fun addr'
                  => if addr' ?= addr
                     then lower_word_half val
                     else if addr' ?= nxt addr
                          then upper_word_half val
                          else store addr')
  | write_lword addr val
    => modify (fun store
               => fun addr'
                  => if addr' ?= addr
                     then lword_quarter_1 val
                     else if addr' ?= nxt addr
                          then lword_quarter_2 val
                          else if addr' ?= nxt (nxt addr)
                               then lword_quarter_3 val
                               else if addr' ?= nxt (nxt (nxt addr))
                                    then lword_quarter_4 val
                                    else store addr')
  end.

Instance memstorage_MonadInterp
         (n:  nat)
  : MonadInterp (MSi n) (State (MSs n)) :=
  { interpret := @MS_interp n
  }.

Definition MSInterp
           {n:  nat}
           (x:  MSs n)
  : Interp (MSi n) :=
  monad_state_interp (MSs_init n).

Require Import FreeSpec.Program.
Local Open Scope free_prog_scope.

Fact write_then_read
     {n:  nat}
     (H:  1 < n)
     (x:  MSs n)
     (a:  mem n)
     (v:  word)
  : evalProgram (MSInterp x) ([write_word a v] ;; [read_word a]) == v.
Proof.
  Opaque weq_bool.
  cbn.
  repeat rewrite weq_bool_refl.
  rewrite (weq_bool_false_rewrite (nxt a) a).
  rewrite <- join_bytes_upper_lower_eq.
  reflexivity.
  apply not_weq_sym.
  apply (nxt_neq a).
  exact H.
Qed.
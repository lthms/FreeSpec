Require Import Coq.NArith.NArith.

Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Function.
Require Import FreeSpec.MonadSemantics.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.Identity.
Require Import FreeSpec.WEq.

Require Import FreeSpec.Libs.NOmega.NOmega.

Local Close Scope nat_scope.
Local Open Scope N_scope.

Local Open Scope free_weq_scope.
Local Open Scope free_control_scope.

Inductive MSi
          (n:  N)
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
           (n:  N)
  := mem n
     -> byte.

Definition MSs_weq
           {n:             N}
           (store store':  MSs n)
  : Prop :=
  forall (addr: mem n),
    store addr == store' addr.

Instance MSs_WEq
         (n:  N)
  : WEq (MSs n) :=
  { weq := @MSs_weq n
  }.

Definition MSs_init
           (n:  N)
  : MSs n :=
  pure (0: byte).

Definition nxt
           {n:  N}
           (x:  mem n)
  : mem n :=
  add x (box n 1).

Lemma nxt_neq
      {n:  N}
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
  rewrite N.mod_1_l in Heq.
  + destruct (N.eq_dec (x + 1) (2 ^ n)).
    ++ rewrite e in Heq.
       rewrite N.mod_same in Heq.
       subst.
       rewrite N.add_0_l in e.
       assert (Hn:  n = 0). {
         rewrite <- (N.pow_0_r 2) in e at 1.
         apply N.pow_inj_r in e.
         symmetry; exact e.
         exact N.lt_1_2.
       }
       subst.
       inversion H.
       apply N.neq_0_lt_0.
       apply pow_pos.
       apply N.lt_0_2.
    ++ assert (Hn:  x + 1 < 2 ^ n) by nomega.
       apply (N.neq_succ_diag_r x).
       rewrite <- N.add_1_r.
       rewrite N.mod_small in Heq.
       exact Heq.
       exact Hn.
  + apply N.pow_gt_1.
    apply N.lt_1_2.
    nomega.
Qed.

Definition MS_handle
           {n:  N}
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

Instance memstorage_MonadSemantics
         (n:  N)
  : MonadSemantics (MSi n) (State (MSs n)) :=
  { handle := @MS_handle n
  }.

Definition MSSemantics
           {n:  N}
           (x:  MSs n)
  : Semantics (MSi n) :=
  monad_state_semantics (MSs_init n).

Require Import FreeSpec.Program.
Local Open Scope free_prog_scope.

Fact write_then_read
     {n:  N}
     (H:  1 < n)
     (x:  MSs n)
     (a:  mem n)
     (v:  word)
  : evalProgram (MSSemantics x) ([write_word a v] ;; [read_word a]) == v.
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
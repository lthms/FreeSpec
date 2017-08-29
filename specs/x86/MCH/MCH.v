Require Import FreeSpec.Specs.x86.MCH.SMRAMC.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.Specs.Address.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Undefined.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Specs.Bitfield.
Require Import FreeSpec.Specs.x86.MCH.SMRAMC.
Require Import FreeSpec.PropBool.

Local Open Scope free_scope.
Local Open Scope free_control_scope.

(** * Interface

 *)

Inductive MCHi
  : Interface :=
| PIO_in32 (port: word)
  : MCHi lword
| PIO_out32 (port: word)
            (val:  lword)
  : MCHi unit
| IO_read (addr: address_64B_aligned)
  : MCHi (mem (64 Bytes))
| IO_write (addr: address_64B_aligned)
           (val:  mem (64 Bytes))
  : MCHi unit.

(** * Hardware Specification

 *)

Inductive ConfAddr
  : Type :=
| confaddr (bus:        nat)
           (device:     nat)
           (function:   nat)
           (register:   nat)
           (pci_enable: bool)
  : ConfAddr.

Definition confaddr_eqb
           (c c': ConfAddr)
  : bool :=
  match c, c' with
  | confaddr b d f r p, confaddr b' d' f' r' p'
    =>  Nat.eqb b b'
     && Nat.eqb d d'
     && Nat.eqb f f'
     && Nat.eqb r r'
     && Bool.eqb p p'
  end.

Fact confaddr_eqb_refl
     (c: ConfAddr)
  : confaddr_eqb c c = true.
Proof.
  destruct c.
  unfold confaddr_eqb.
  repeat rewrite <- EqNat.beq_nat_refl.
  rewrite Bool.eqb_reflx.
  reflexivity.
Qed.

Instance confaddr_PropBoolP
  : PropBool2 (@eq ConfAddr) (confaddr_eqb) :=
  {
  }.
  intros c c'; split.
  + intros H.
    destruct c; destruct c'.
    unfold confaddr_eqb in H.
    apply Bool.andb_true_iff in H; destruct H as [H H'].
    apply Bool.andb_true_iff in H; destruct H as [H H''].
    apply Bool.andb_true_iff in H; destruct H as [H H'''].
    apply Bool.andb_true_iff in H; destruct H as [H H''''].
    apply EqNat.beq_nat_true in H.
    apply EqNat.beq_nat_true in H''.
    apply EqNat.beq_nat_true in H'''.
    apply EqNat.beq_nat_true in H''''.
    apply Bool.eqb_prop in H'.
    subst.
    reflexivity.
  + intros Heq.
    rewrite Heq.
    rewrite confaddr_eqb_refl.
    reflexivity.
Defined.

Definition SMRAMC_Addr
  : ConfAddr :=
  confaddr 0 16 0 22 true. (* 16h *)

Definition ConfAddr_bf
  : Bitfield 32 ConfAddr :=
  skip 1                 :;
  register :<- field 7    ;
  function :<- field 3    ;
  device   :<- field 5    ;
  bus      :<- field 8    ;
  skip 7                 :;
  pci      :<- bit        ;
  bf_pure (confaddr bus device function register pci).

Definition parse_confaddr
           (w: lword)
  : ConfAddr :=
  parse ConfAddr_bf w.

Inductive io_write32_target
  : Type :=
| ConfAddr_target
| ConfData_target
| Invalid_target.

Axiom word_to_target
  : word -> option io_write32_target.

Record MCHs :=
  { confAddr: ConfAddr
  ; smramc: SMRAMC
  }.

Instance mchs_WEq
  : WEq MCHs :=
  { weq := eq
  }.

(** We need a notation here. If you use a plain ~Definition~, Coq
    cannot find the typeclass instance any longer.

 *)
Notation "'MCHm' A":= (StateT MCHs (Program (MCHi <+> Undefined)) A)
                        (at level 30).

(* We have to help a little Coq here. See #16 for more information on
   this matter *)
Definition mch_undefined
           {A: Type}
  : MCHm A :=
  undef (UndefMonad:=undefmonad_Trans _ _).

Definition update_confaddr
           (ca: ConfAddr)
  : MCHm unit :=
  modify (fun s
          => {| confAddr := ca
              ; smramc := smramc s
              |}).

Definition get_confaddr
  : MCHm ConfAddr :=
  gets confAddr.

Definition update_smramc
           (reg: SMRAMC)
  : MCHm unit :=
  modify (fun s
          => {| confAddr := confAddr s
              ; smramc := reg
              |}).

Definition get_smramc
  : MCHm SMRAMC :=
  gets smramc.

Definition pio_out32
           (x: word)
           (val: lword)
  : MCHm unit :=
  match word_to_target x with
  | Some ConfAddr_target
    => update_confaddr (parse_confaddr val)
  | Some ConfData
    => confaddr <- get_confaddr                                      ;
       match confaddr with
       | confaddr 0 16 0 97 (* 61h *) true (* SMRAMC *)
         => (* update_smramc (parse_smramc val) *)
             mch_undefined
       | _
         => mch_undefined
       end
  | Nothing (* An invalid IO out access is just ignore by the MCH   *)
    => pure tt
  end.

Definition mch_specs
  : StatefulRefinement MCHi (MCHi <+> Undefined) MCHs :=
  fun (A: Type)
      (i: MCHi A)
  => match i with
     | PIO_out32 x val
       => pio_out32 x val
     | _
       => mch_undefined
     end.
(* begin hide *)
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
(* end hide *)

Require Import FreeSpec.Interp.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Program.
Require Import FreeSpec.Contract.
Require Import FreeSpec.PropBool.
Require Import FreeSpec.Control.

Require Import FreeSpec.Examples.Map.

Local Open Scope free_scope.
Local Open Scope free_prog_scope.
Local Open Scope free_control_scope.

(** This Example is here to show how to create a Component which
    relies on two separated interfaces.

 *)

(* begin hide *)
Section SMRAM_EXAMPLE.
(* end hide *)

  (** * Hypotheses

      This is an example, not a real proof of concept. Therefore, we
      do not really care about code extraction and could easily work
      with axioms.

      We don’t really care which addresses and values we
      consider. However, we really want to know when one address falls
      into the SMRAM.
    *)
  Variables (Addr:             Type)
            (addr_eq_bool:     Addr -> Addr -> bool)
            (addr_eq_PropBool: PropBool2 (@eq Addr) addr_eq_bool)
            (Value:            Type)
            (Smram:            Addr -> Prop)
            (Smram_bool:       Addr -> bool)
            (smram_PropBool:   PropBool1 Smram Smram_bool).

  (** * Memory Controller

      In this example, we consider one very simple Memory Controller
      with a unique mechanism to protect the so-called SMRAM. Our goal
      is to ensure that, if correctly configured, the Memory
      Controller will enforce that privileged memory read accesses
      will always return something that has been previously written in
      a privileged way.

      ** Interface

      We consider two primitives: read and write accesses. These
      primitives can be done in a privileged or unprivileged manner.

   *)

  Inductive IMCH
    : Interface :=
  | ReadMem (a:   Addr)
            (smm: bool)
    : IMCH Value
  | WriteMem (a:   Addr)
             (v:   Value)
             (smm: bool)
    : IMCH unit.

  (** ** Concrete State

      The Memory Controller has got one register called [smram_lock]
      which can be high or low. We do not provide a way to modify it
      yet, so it will set in the initial state and never change after
      that.

   *)

  Record MCH
    : Type :=
    { smram_lock: bool
    }.

  (** ** Required Interfaces

      Our Memory Controller is used as a memory proxy. It receives
      privileged and unprivileged memory requests and forwards them to
      either a DRAM controller or a VGA controller.

      We use the [IMap] interface defined in the
      [FreeSpec.Examples.Map] Library.

   *)

  Definition IDRAM := IMap Addr Value.
  Definition IVGA := IMap Addr Value.

  (** ** Specification

      We know specify the functionning of the Memory Controller. To do
      so, we first define several helper programs.

   *)

  Definition read_dram
             (a: Addr)
    : Program (IDRAM <+> IVGA) Value :=
    [ileft (Read a)].

  Definition read_vga
             (a: Addr)
    : Program (IDRAM <+> IVGA) Value :=
    [iright (Read a)].

  Definition write_dram
             (a: Addr)
             (v: Value)
    : Program (IDRAM <+> IVGA) unit :=
    [ileft (Write a v)].

  Definition write_vga
             (a: Addr)
             (v: Value)
    : Program (IDRAM <+> IVGA) unit :=
    [iright (Write a v)].

  (** Then, we define a [StatefulRefinement] from [IMCH] to [IDRAM <+>
      IVGA].

   *)

  Program Definition mch_refine
    : StatefulRefinement IMCH (IDRAM <+> IVGA) MCH :=
    fun (A: Type)
        (i: IMCH A)
        (s: MCH)
    =>  match i with
        | ReadMem a true (* ---- Privileged Read Access ----------- *)
          => x <- read_dram a                                        ;
             ret (x, s)
        (* -------------------------------------------------------- *)
        | ReadMem a false (* --- Unprivileged Read Access---------- *)
          => x <- if andb (Smram_bool a)
                          (smram_lock s)
                  then read_vga a
                  else read_dram a                                   ;
             ret (x, s)
        (* -------------------------------------------------------- *)
        | WriteMem a v true (* - Privileged Write Access ---------- *)
          => write_dram a v                                         ;;
             ret (tt, s)
        (* -------------------------------------------------------- *)
        | WriteMem a v false (*  Unprivileged Write Access -------- *)
          => (if andb (Smram_bool a)
                      (smram_lock s)
              then write_vga a v
              else write_dram a v                                  );;
              ret (tt, s)
        (* -------------------------------------------------------- *)
        end.

  (** * Contract

      Now here comes the section where FreeSpec is supposed to shine.
      We want to define a Contract which basically says: “Privileged
      read accesses only fetch value written by privileged write
      accesses.”

      ** Abstract State

      To express that, we first define a very simple abstract state
      which is basically a map from SMRAM addresses to value written
      by privileged write accesses.

      To do that, we will keep a map from SMRAM addresses to value
      which will be updated only with privileged memory accesses.

   *)

  Definition SmramState
    := Addr -> Value.

  Definition update
             (a: Addr)
             (v: Value)
             (s: SmramState)
    : SmramState :=
    fun (a': Addr)
    => if addr_eq_bool a a'
       then v
       else s a'.

  Definition Smram_step
             (A: Type)
             (i: IMCH A)
             (_: A)
             (s: SmramState)
    : SmramState :=
    match i with
    | WriteMem a v true (* Privileged Write Access within the SMRAM *)
      => if Smram_bool a
         then update a v s
         else s
    | _ (* Any other primitives should not trigger a SMRAM change --*)
      => s
    end.

  (** ** Requirements

      Because we do not allow anyone to modify the [smram_lock]
      register, we do not have any requirement the Memory Controller
      user (typically the CPU) needs to enforce.

   *)

  Definition Smram_requirements
             (A: Type)
             (i: IMCH A)
             (S: SmramState)
    : Prop :=
    True.

  (** ** Promises

      An Enforcer Component needs to stay syncronize with the abstract
      state of the Smram, that is deliver the value written by a
      privileged memory access.

   *)

  Notation "H :- a == b" :=
    (eq_rect _ id a _ H = b)
      (at level 40, no associativity).

  Definition Smram_promises
             (A:   Type)
             (i:   IMCH A)
             (ret: A)
             (s:   SmramState)
    : Prop :=
    match i
          in IMCH A'
          return A = A' -> Prop
    with
    | ReadMem a true (* Privileged Reads match the shadow Smram *)
      => fun (H: A = Value)
         => Smram a -> H :- ret == s a
    | _ (* No Guarantee otherwise *)
      => fun _ => True
    end (eq_refl A).

  (** ** Definition

   *)

  Definition smram_contract
    : Contract SmramState IMCH :=
    {| abstract_step := Smram_step
     ; requirements  := Smram_requirements
     ; promises      := Smram_promises
     |}.

  (** * Contract Enforcement

      ** Sub-Contracts

      We acknowledge that, in order for our Memory Controler to
      enforce the [smram_contract], the DRAM controller needs to work
      in a correct manner. To specify this correct manner, we need a
      sub-contract, which will basically describe who it is supposed
      to work.

   *)

  Definition DRAMState
    := Addr -> Value.

  Definition DRAM_step
             (A: Type)
             (i: IDRAM A)
             (_: A)
             (s: DRAMState)
    : DRAMState :=
    match i with
    | Write a v (* Write Access *)
      => fun (a': Addr)
         => if addr_eq_bool a a'
            then v
            else s a'
    | _ (* Nothing to do with Read Access *)
      => s
    end.

  (** We do not need any requirements on the DRAM Interface...

   *)

  Definition DRAM_requirements
             (A: Type)
             (i: IDRAM A)
             (s: DRAMState)
    : Prop :=
    True.

  (** But we need the result of the Read primitive to stay
  synchronized with the abstract step.

   *)

  Definition DRAM_promises
             (A:   Type)
             (i:   IDRAM A)
             (ret: A)
             (s:   DRAMState)
    : Prop :=
    match i
          in IMap _ _ A' (* we cannot use the alias IDRAM here *)
          return A = A' -> Prop
    with
    | Read a (* Read Access *)
      => fun (H: A = Value)
         => H :- ret == s a
    | _
      => fun _ => True
    end (eq_refl A).

  Definition dram_contract
    : Contract DRAMState IDRAM :=
    {| abstract_step := DRAM_step
     ; requirements  := DRAM_requirements
     ; promises      := DRAM_promises
     |}.

  Definition smram_subcontract
    : Contract DRAMState (IDRAM <+> IVGA) :=
    expand_contract_left (dram_contract) IVGA.

  (** ** Predicate of Synchronization

 *)

  Definition mch_dram_sync
    : sync_pred SmramState DRAMState MCH :=
    fun (mch:   SmramState)
        (state: MCH)
        (dram:  DRAMState)
    => smram_lock state = true /\
       forall (a: Addr),
         Smram a
         -> mch a = dram a.

  Fact mch_dram_sync_smram_lock_is_true
       (si:    SmramState)
       (state: MCH)
       (so:    DRAMState)
    : mch_dram_sync si state so
      -> smram_lock state = true.
  Proof.
    intros [H _H].
    exact H.
  Qed.

  Lemma mch_specs_compliant_refinement
    : compliant_refinement mch_refine
                           smram_contract
                           smram_subcontract
                           mch_dram_sync.
  Proof.
    unfold compliant_refinement.
    intros si s so A i Hsync Hreq.
    induction i.
    + induction smm.
      ++ constructor.
         +++ constructor.
             trivial. (* no requirement for the subcontract *)
         +++ constructor. (* program is only a ret, so it is trivial *)
      ++ constructor.
         +++ rewrite (mch_dram_sync_smram_lock_is_true _ _ _ Hsync).
             rewrite andb_true_r.
             destruct (Smram_bool a); cbn.
             ++++ constructor.
                  trivial. (* read vga, no contract on vga *)
             ++++ constructor.
                  trivial. (* read dram, no requirement on vga *)
         +++ constructor. (* program is only a ret *)
    + induction smm.
      ++ constructor.
         +++ constructor.
             trivial. (* no requirement for the subcontract *)
         +++ constructor. (* program is only a ret, so it is trivial *)
      ++ constructor.
         +++ rewrite (mch_dram_sync_smram_lock_is_true _ _ _ Hsync).
             rewrite andb_true_r.
             destruct (Smram_bool a); cbn.
             ++++ constructor.
                  trivial. (* read vga, no contract on vga *)
             ++++ constructor.
                  trivial. (* read dram, no requirement on vga *)
         +++ constructor. (* program is only a ret *)
  Qed.

  Lemma mch_specs_sync_preservation
    : sync_preservation mch_refine
                        smram_contract
                        smram_subcontract
                        mch_dram_sync.
  Proof.
    unfold sync_preservation.
    intros si s so int Henf A i Hsync Hreq.
    induction i; induction smm.
    + (* privileged read *)
      exact Hsync.
    + (* unprivileged read *)
      cbn.
      rewrite (mch_dram_sync_smram_lock_is_true _ _ _ Hsync).
      rewrite andb_true_r.
      destruct (Smram_bool a); cbn; exact Hsync.
    + (* privileged write *)
      cbn.
      split.
      ++ apply (mch_dram_sync_smram_lock_is_true si _ so Hsync).
      ++ intros a' Hsmram.
         unfold update.
         case_eq (Smram_bool a); intro Hsmram'.
         +++ destruct (addr_eq_bool a a').
             ++++ reflexivity.
             ++++ destruct Hsync as [_H H].
                  rewrite (H a' Hsmram).
                  reflexivity.
         +++ case_eq (addr_eq_bool a a'); intro Heq.
             ++++ apply pred_bool_pred_2 in Heq.
                  rewrite Heq in Hsmram'.
                  apply (pred_bool_false_1 Smram Smram_bool a') in Hsmram'.
                  apply Hsmram' in Hsmram.
                  destruct Hsmram.
             ++++ destruct Hsync as [_H H].
                  rewrite (H a' Hsmram).
                  reflexivity.
    + (* unprivileged write *)
      cbn.
      split.
      ++ apply (mch_dram_sync_smram_lock_is_true si _ so Hsync).
      ++ intros a' Hsmram.
         rewrite (mch_dram_sync_smram_lock_is_true _ _ _ Hsync).
         rewrite andb_true_r.
         case_eq (Smram_bool a); intro Hsmram'; cbn.
         +++ destruct Hsync as [_H H].
             rewrite (H a' Hsmram).
             reflexivity.
         +++ case_eq (addr_eq_bool a a'); intro Heq.
             ++++ apply pred_bool_pred_2 in Heq.
                  rewrite Heq in Hsmram'.
                  apply (pred_bool_false_1 Smram Smram_bool a') in Hsmram'.
                  apply Hsmram' in Hsmram.
                  destruct Hsmram.
             ++++ destruct Hsync as [_H H].
                  rewrite (H a' Hsmram).
                  reflexivity.
  Qed.


  Lemma mch_specs_sync_promises
    : sync_promises mch_refine
                    smram_contract
                    smram_subcontract
                    mch_dram_sync.
  Proof.
    unfold sync_promises.
    intros si s so int Henf A i Hsync Hreq.
    assert (Hcp: compliant_refinement mch_refine
                                      smram_contract
                                      smram_subcontract
                                      mch_dram_sync). {
      apply mch_specs_compliant_refinement.
    }
    unfold compliant_refinement in Hcp.
    assert (H: compliant_program smram_subcontract so (mch_refine A i s))
      by apply (Hcp si _ _ _ _ Hsync Hreq).
    induction i; induction smm; try trivial.
    (* privileged read *)
    cbn; cbn in H.
    intros Hsmram.
    inversion H;
      repeat simpl_existT;
      subst.
    inversion Hcp0;
      repeat simpl_existT;
      subst.
    assert (Hprom: promises smram_subcontract
                            (ileft (Read a))
                            (fst (interpret int (ileft (Read a))))
                            so). {
      apply (enforcer_enforces_promises _ _ _ _ Henf Hreq0).
    }
    cbn in Hprom.
    rewrite Hprom.
    assert (Hproof: so a = si a). {
      destruct Hsync as [_H Hx].
      rewrite (Hx a Hsmram).
      reflexivity.
    }
    rewrite Hproof.
    constructor.
  Qed.

  Lemma mch_refine_enforcer
        {dram:     Interp IDRAM}
        {dram_ref: DRAMState}
        (Henf:     dram :> dram_contract[dram_ref])
    : forall (vga:       Interp IVGA)
             (smram_ref: SmramState),
      mch_dram_sync smram_ref {| smram_lock := true |} dram_ref
      -> (StatefulInterpret mch_refine
                            {| smram_lock := true |}
                            (dram |+| vga))
           :> smram_contract [smram_ref].
  Proof.
    intros vga smram_ref Hsync.
    assert (dram |+| vga :> smram_subcontract[dram_ref])
      as Henf' by apply (expand_enforcer_left Henf).
    apply (enforcer_refinement mch_refine
                               smram_contract
                               smram_subcontract
                               mch_dram_sync
                               mch_specs_sync_preservation
                               mch_specs_sync_promises
                               mch_specs_compliant_refinement
                               smram_ref
                               {| smram_lock := true |}
                               dram_ref
                               (dram |+| vga)
                               Henf'
                               Hsync).
  Qed.

(* begin hide *)
End SMRAM_EXAMPLE.
(* end hide *)
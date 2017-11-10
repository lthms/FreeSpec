(* begin hide *)
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Import FreeSpec.Compose.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.PropBool.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Tactics.
Require Import FreeSpec.WEq.

Require Import FreeSpec.Examples.Map.

Local Open Scope free_scope.
Local Open Scope free_weq_scope.
Local Open Scope free_prog_scope.
Local Open Scope free_control_scope.

(** This Example is here to show how to create a Component which
    relies on two separated interfaces. To do that, we take the
    example of the SMRAM protection by the Memory Controller. The
    current example simplifies *a lot* both the Memory Controller and
    how it works. Keep in mind it is just a showcase to get a quick
    understanding on how FreeSpec works and what you can do with it.

    If you want to see a more in-depth example, you can have a look at
    [FreeSpec.Specs.x86.MCH] and related.

 *)

(* begin hide *)
Section SMRAM_EXAMPLE.
(* end hide *)

  (** * Hypotheses

      This is an example, not a real proof of concept. Therefore, we
      do not really care about code extraction and could easily work
      with axioms.  We don’t really care which addresses and values we
      consider. However, we really want to know when one address falls
      into the SMRAM.
    *)
  Variables (Addr:             Type)
            (AddrWEq:          WEq Addr)
            (AddrWEqBool:      WEqBool Addr)
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

  Instance mch_WEq
    : WEq (MCH) :=
    { weq := eq
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
    : StateT MCH (Program (IDRAM <+> IVGA)) Value :=
    '[ileft (Read a)].

  Definition read_vga
             (a: Addr)
    : StateT MCH (Program (IDRAM <+> IVGA)) Value :=
    '[iright (Read a)].

  Definition write_dram
             (a: Addr)
             (v: Value)
    : StateT MCH (Program (IDRAM <+> IVGA)) unit :=
    '[ileft (Write a v)].

  Definition write_vga
             (a: Addr)
             (v: Value)
    : StateT MCH (Program (IDRAM <+> IVGA)) unit :=
    '[iright (Write a v)].

  (** Then, we define a [StatefulRefinement] from [IMCH] to [IDRAM <+>
      IVGA].

   *)

  (* this work *)
  Definition get_smram_lock
    : StateT MCH (Program (IDRAM <+> IVGA)) bool :=
    smram_lock <$> get.

  Definition mch_refine
    : StatefulRefinement IMCH (IDRAM <+> IVGA) MCH :=
    fun (A: Type)
        (i: IMCH A)
    =>  match i with
        | ReadMem a true (* ---- Privileged Read Access ----------- *)
          => read_dram a
        (* -------------------------------------------------------- *)
        | ReadMem a false (* --- Unprivileged Read Access---------- *)
          => s <- get_smram_lock                                     ;
             x <- if andb (Smram_bool a) s
                  then read_vga a
                  else read_dram a                                   ;
             pure x
        (* -------------------------------------------------------- *)
        | WriteMem a v true (* - Privileged Write Access ---------- *)
          => write_dram a v                                         ;;
             pure tt
        (* -------------------------------------------------------- *)
        | WriteMem a v false (*  Unprivileged Write Access -------- *)
          => s <- get_smram_lock                                     ;
             x <- if andb (Smram_bool a) s
                  then write_vga a v
                  else write_dram a v                                ;
             pure tt
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
    => if a ?= a'
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
         => Smram a -> eq_rect _ id ret _ H = s a
    | _ (* No Guarantee otherwise *)
      => fun _ => True
    end (eq_refl A).

  (** ** Definition

    We can now put all the different pieces together.

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

      The state is a simple map from addresses to values. This is a
      very straightforward and natural (but inefficient, but we really
      don't care about that for this example) way to model a key-value
      store.

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
         => if a ?= a'
            then v
            else s a'
    | _ (* Nothing to do with Read Access *)
      => s
    end.

  (** We do not need any requirements on the DRAM Interface. This is
      mostly because we only describe how it works.

   *)

  Definition DRAM_requirements
             (A: Type)
             (i: IDRAM A)
             (s: DRAMState)
    : Prop :=
    True.

  (** But we need the result of the Read primitive to stay
      synchronized with the abstract step. This is because we will use
      the primitives introduces in [FreeSpec.Refine] library. See, in
      particular, [sync_pred].

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
         => eq_rect _ id ret _ H = s a
    | _
      => fun _ => True
    end (eq_refl A).

  (** We then put all the pieces together to build a contract for the
      DRAM Controller.

   *)

  Definition dram_contract
    : Contract DRAMState IDRAM :=
    {| abstract_step := DRAM_step
     ; requirements  := DRAM_requirements
     ; promises      := DRAM_promises
     |}.

  (** But, remember, the MCH is a proxy and roots memory accesses to
      either the DRAM controller (we have taken care of this one) _or
      the VGA controller_.

      The thing is, we will later prove not matter how the VGA
      controller behaves, it does not interfere with the functionning
      of the MCH and the SMRAM protection. This works because:

        - We know exactly how the MCH is using both the DRAM
          Controller and the VGA Controller (the refinement)
        - We consider the VGA Controller and the DRAM Controller are
          totally independent (this is explicit because we have two
          interfaces).

      The [FreeSpec.Compose] library provides a convenient helper to
      expand a contract of a given contract to make it usable to check
      against more complex specifications that rely on other
      Interfaces as well: [expand_contact_left]. It also provides
      other helpers, see the module documentation for more
      informations about them.

   *)

  Definition smram_subcontract
    : Contract DRAMState (IDRAM <+> IVGA) :=
    expand_contract_left (dram_contract) IVGA.

  (** ** Predicate of Synchronization

      Before going any further, you need to have a clear idea of how
      the [FreeSpec.Refine] library works. In a few words, all the
      proofs logic relies on a so-called predicate of synchronization
      (see [sync_pred]). This predicate is specific to each refinement
      and it allows to reason by induction. Basically, you show that
      if all the considered states (the abstract state of your main
      contract, the concrete state of your specifications and the
      abstract states of the subcontracts) are “synchronized“, if you
      have to handle an instruction that is allowed by the main
      contract ([requirements]), then

        - The states stay synchronized after the instruction has been
          executed.
        - You only uses instructions that are allowed by the
          subcontracts when interacting with the subcomponents
        - The instuction result matches the contract [promises]


      Here, our predicate of synchronization is two-folded:

        - We need the MCH to be “locked” (that is, the protection of
          the SMRAM is enable and working)
        - We need the MCH abstract view of the SMRAM to match the
          current abstract view of the SMRAM inside the DRAM
          controller

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

  Ltac next := repeat (try constructor; cbn; trivial).

  (** Our goal is to be able to use the [enforcer_refinement] lemma,
      we therefore prove its premises, which are summarized in the
      introduction of this section.

      First, we only use the underlying interfaces in a way that
      respect the subcontracts. As a reminder, a refinement is
      basically a translation from one interface into a program of
      sub-interfaces. We therefore check these programs comply with
      the subcontract previously introduced.

   *)

  Lemma mch_specs_compliant_refinement
    : compliant_refinement mch_refine
                           smram_contract
                           smram_subcontract
                           mch_dram_sync.
  Proof.
    unfold compliant_refinement.
    intros si s so A i Hsync Hreq.
    induction i; induction smm; next; repeat destruct_if_when; next.
  Qed.

  (** Then, we prove the predicate of synchronization is effectively
      an invariant preserved by the [requirements] predicate of the
      main contract.

   *)

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
      repeat destruct_if_when; exact Hsync.
    + (* privileged write *)
      cbn.
      split.
      ++ apply (mch_dram_sync_smram_lock_is_true si _ so Hsync).
      ++ intros a' Hsmram.
         unfold update; repeat destruct_if_when.
         +++ reflexivity.
         +++ apply Hsync.
             exact Hsmram.
         +++ (* Smram a /\ Smram_bool a' = false /\ (a ?= a') = true
                is not possible, but we lack the fact that Smram and
                Smram_bool are “weq_morphism“. Admit for now. *)
             admit.
         +++ apply Hsync.
             exact Hsmram.
    + (* unprivileged write *)
      cbn.
      repeat destruct_if_when.
      split.
      ++ apply (mch_dram_sync_smram_lock_is_true si _ so Hsync).
      ++ intros a' Hsmram.
         apply Hsync.
         exact Hsmram.
  Admitted.

  (** Finally, we check all this work and constrains brings the
      expected result, that is the [promises] predicate. In other
      word, if the caller does its job, then the component (here, the
      MCH) does its job too. In this example, the promises is that an
      unprivileged write cannot tamper with the SMRAM content as seen
      by the privileged reads.

 *)

  Lemma mch_specs_sync_promises
    : sync_promises mch_refine
                    smram_contract
                    smram_subcontract
                    mch_dram_sync.
  Proof.
    unfold sync_promises.
    intros si s so int Henf A i Hsync Hreq.
    induction i; induction smm; cbn; try constructor.
    intros Hsmram.
    run_program int.
    + simplify_promise.
      rewrite Hprom_i.
      symmetry.
      apply Hsync.
      exact Hsmram.
    + rewrite Heqi.
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
(* FreeSpec
 * Copyright (C) 2018 ANSSI
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

(* begin hide *)
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Import FreeSpec.Compose.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Tactics.

Require Import Prelude.Control.
Require Import Prelude.Control.Classes.
Require Import Prelude.Control.State.
Require Import Prelude.PropBool.
Require Import Prelude.Equality.

Require Import FreeSpec.Examples.Map.

Local Open Scope free_scope.
Local Open Scope prelude_scope.

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
  Variables (Addr:                Type)
            (AddrEq:              Equality Addr)
            (AddrEqBool:          EqualityBool Addr)
            (Value:               Type)
            (Smram:               Addr -> Prop)
            (Smram_weq_morphism:  forall (a a': Addr),
                a == a' -> Smram a -> Smram a')
            (Smram_bool:          Addr -> bool)
            (smram_PropBool:      PropBool1 Smram Smram_bool).

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

  Instance mch_Eq
    : Equality (MCH) :=
    { equal := eq
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
    lift (Request (InL (Read a))).

  Definition read_vga
             (a: Addr)
    : StateT MCH (Program (IDRAM <+> IVGA)) Value :=
    lift (Request (InR (Read a))).

  Definition write_dram
             (a: Addr)
             (v: Value)
    : StateT MCH (Program (IDRAM <+> IVGA)) unit :=
    lift (Request (InL (Write a v))).

  Definition write_vga
             (a: Addr)
             (v: Value)
    : StateT MCH (Program (IDRAM <+> IVGA)) unit :=
    lift (Request (InR (Write a v))).

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

  (** * Specification

      Now here comes the section where FreeSpec is supposed to shine.
      We want to define a Specification which basically says: “Privileged
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

  (** ** Precondition

      Because we do not allow anyone to modify the [smram_lock]
      register, we do not have any requirement the Memory Controller
      user (typically the CPU) needs to enforce.

   *)

  Definition Smram_precondition
             (A: Type)
             (i: IMCH A)
             (S: SmramState)
    : Prop :=
    True.

  (** ** Postcondition

      An Enforcer Component needs to stay syncronize with the abstract
      state of the Smram, that is deliver the value written by a
      privileged memory access.

   *)

  Definition Smram_postcondition
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

  Definition smram_specification
    : Specification SmramState IMCH :=
    {| abstract_step  := Smram_step
     ; precondition   := Smram_precondition
     ; postcondition  := Smram_postcondition
     |}.

  (** * Specification Enforcement

      ** Sub-Specifications

      We acknowledge that, in order for our Memory Controler to
      enforce the [smram_specification], the DRAM controller needs to
      work in a correct manner. To specify this correct manner, we
      need a sub-specification, which will basically describe who it
      is supposed to work.

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

  (** We do not need any precondition on the DRAM Interface. This is
      mostly because we only describe how it works.

   *)

  Definition DRAM_precondition
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

  Definition DRAM_postcondition
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

  (** We then put all the pieces together to build a specification for the
      DRAM Controller.

   *)

  Definition dram_specification
    : Specification DRAMState IDRAM :=
    {| abstract_step  := DRAM_step
     ; precondition   := DRAM_precondition
     ; postcondition  := DRAM_postcondition
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
      expand a specification of a given specification to make it usable to check
      against more complex specifications that rely on other
      Interfaces as well: [expand_contact_left]. It also provides
      other helpers, see the module documentation for more
      informations about them.

   *)

  Definition smram_subspecification
    : Specification DRAMState (IDRAM <+> IVGA) :=
    expand_specification_left (dram_specification) IVGA.

  (** ** Predicate of Synchronization

      Before going any further, you need to have a clear idea of how
      the [FreeSpec.Refine] library works. In a few words, all the
      proofs logic relies on a so-called predicate of synchronization
      (see [sync_pred]). This predicate is specific to each refinement
      and it allows to reason by induction. Basically, you show that
      if all the considered states (the abstract state of your main
      specification, the concrete state of your specifications and the
      abstract states of the subspecifications) are “synchronized“, if you
      have to handle an instruction that is allowed by the main
      specification ([precondition]), then

        - The states stay synchronized after the instruction has been
          executed.
        - You only uses instructions that are allowed by the
          subspecifications when interacting with the subcomponents
        - The instuction result matches the specification [postcondition]


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
      respect the subspecifications. As a reminder, a refinement is
      basically a translation from one interface into a program of
      sub-interfaces. We therefore check these programs comply with
      the subspecification previously introduced.

   *)

  Lemma mch_specs_compliant_refinement
    : correct_refinement mch_refine
                         smram_specification
                         smram_subspecification
                         mch_dram_sync.
  Proof.
    unfold correct_refinement.
    intros si s so A i Hsync Hreq.
    induction i; induction smm; next; repeat destruct_if_when; next.
  Qed.

  (** Then, we prove the predicate of synchronization is effectively
      an invariant preserved by the [precondition] predicate of the
      main specification.

   *)

  Lemma mch_specs_sync_preservation
    : sync_preservation mch_refine
                        smram_specification
                        smram_subspecification
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
         +++ apply (pred_bool_false_1 _ Smram_bool) in Heq_cond.
             apply equalb_equal in Heq_cond0.
             apply (Smram_weq_morphism a' a) in Hsmram.
             apply Heq_cond in Hsmram.
             destruct Hsmram.
             symmetry.
             apply Heq_cond0.
         +++ apply Hsync.
             exact Hsmram.
    + (* unprivileged write *)
      cbn.
      repeat destruct_if_when.
      ++ split.
         +++ apply (mch_dram_sync_smram_lock_is_true si _ so Hsync).
         +++ intros a' Hsmram.
             apply Hsync.
             exact Hsmram.
      ++ assert (Heq: smram_lock s = true)
          by apply (mch_dram_sync_smram_lock_is_true si _ so Hsync).
         rewrite Heq in Heq_cond.
         assert (Handb: forall (b:  bool), b && true = false -> b = false). {
           intros b.
           induction b.
           + cbn.
             intros False; destruct False.
             reflexivity.
           + reflexivity.
         }
         apply Handb in Heq_cond.
         unfold mch_dram_sync.
         split; [exact Heq |].
         intros a'.
         intros Hsmram.
         assert (Hneq: a ?= a' = false). {
           apply <- equalb_false.
           intros Hfalse.
           apply (pred_bool_false_1 _ Smram_bool) in Heq_cond.
           apply (Smram_weq_morphism a' a) in Hsmram.
           + apply Heq_cond in Hsmram.
             exact Hsmram.
           + symmetry.
             exact Hfalse.
         }
         rewrite Hneq.
         apply Hsync.
         apply Hsmram.
  Qed.

  (** Finally, we check all this work and constrains brings the
      expected result, that is the [postcondition] predicate. In other
      word, if the caller does its job, then the component (here, the
      MCH) does its job too. In this example, the postcondition is that an
      unprivileged write cannot tamper with the SMRAM content as seen
      by the privileged reads.

 *)

  Lemma mch_specs_sync_postcondition
    : sync_postcondition mch_refine
                         smram_specification
                         smram_subspecification
                         mch_dram_sync.
  Proof.
    unfold sync_postcondition.
    intros si s so int Henf A i Hsync Hreq.
    induction i; induction smm; cbn; try constructor.
    intros Hsmram.
    run_program int.
    + simplify_postcondition.
      rewrite Hprom_i.
      symmetry.
      apply Hsync.
      exact Hsmram.
    + rewrite Heqi.
      constructor.
  Qed.

  Lemma mch_refine_enforcer
        {dram:      Semantics IDRAM}
        {dram_ref:  DRAMState}
        (Hcomp:     dram |= dram_specification[dram_ref])
    : forall (vga:        Semantics IVGA)
             (smram_ref:  SmramState),
      mch_dram_sync smram_ref {| smram_lock := true |} dram_ref
      -> (StatefulSemantics mch_refine
                            {| smram_lock := true |}
                            (dram <x> vga))
           |= smram_specification [smram_ref].
  Proof.
    intros vga smram_ref Hsync.
    assert (dram <x> vga |= smram_subspecification[dram_ref])
      as Hcomp' by apply (expand_compliant_left Hcomp).
    apply (compliant_refinement mch_refine
                                smram_specification
                                smram_subspecification
                                mch_dram_sync
                                mch_specs_sync_preservation
                                mch_specs_sync_postcondition
                                mch_specs_compliant_refinement
                                smram_ref
                                {| smram_lock := true |}
                                dram_ref
                                (dram <x> vga)
                                Hcomp'
                                Hsync).
  Qed.

(* begin hide *)
End SMRAM_EXAMPLE.
(* end hide *)
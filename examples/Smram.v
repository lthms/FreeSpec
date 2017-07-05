(* begin hide *)
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.

(* end hide *)

Require Import FreeSpec.Interp.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Program.
Require Import FreeSpec.Contract.

Require Import FreeSpec.Examples.Map.

Local Open Scope free_scope.
Local Open Scope prog_scope.

(** This Example is here to show how to create a Component which
    relies on two separated interfaces.

 *)

Section SMRAM_EXAMPLE.
  (** * Hypotheses

      This is an example, not a real proof of concept. Therefore, we
      do not really care about code extraction and could easily work
      with axioms.

      We don’t really care which addresses and values we
      consider. However, we really want to know when one address falls
      into the SMRAM.
    *)
  Variables (Addr: Type)
            (addr_eq: forall (a a': Addr), {a = a'}+{a <> a'})
            (Value: Type)
            (Smram: Addr -> Prop)
            (Smramdec: forall (a: Addr), {Smram a}+{~Smram a}).

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
  | ReadMem (a: Addr)
            (smm: bool)
    : IMCH Value
  | WriteMem (a: Addr)
             (v: Value)
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
    [ileft (Read _ _ a)].

  Definition read_vga
             (a: Addr)
    : Program (IDRAM <+> IVGA) Value :=
    [iright (Read _ _ a)].

  Definition write_dram
             (a: Addr)
             (v: Value)
    : Program (IDRAM <+> IVGA) unit :=
    [ileft (Write _ _ a v)].

  Definition write_vga
             (a: Addr)
             (v: Value)
    : Program (IDRAM <+> IVGA) unit :=
    [iright (Write _ _ a v)].

  (** Then, we define a [StatefulRefinement] from [IMCH] to [IDRAM <+>
      IVGA].

   *)

  Program Definition mch_refine
    : StatefulRefinement IMCH (IDRAM <+> IVGA) MCH :=
    fun (A: Type) (i: IMCH A) (s: MCH) =>
      match i with
      | ReadMem a true (* ------ Privileged Read Access ----------- *)
        => x <- read_dram a                                          ;
           ret (x, s)
      (* ---------------------------------------------------------- *)
      | ReadMem a false (* ----- Unprivileged Read Access---------- *)
        => x <- if andb (bool_of_sumbool (Smramdec a))
                        (smram_lock s)
                then read_vga a
                else read_dram a                                     ;
           ret (x, s)
      (* ---------------------------------------------------------- *)
      | WriteMem a v true (* --- Privileged Write Access ---------- *)
        => write_dram a v                                           ;;
           ret (tt, s)
      (* ---------------------------------------------------------- *)
      | WriteMem a v false (* -- Unprivileged Write Access -------- *)
        => (if andb (bool_of_sumbool (Smramdec a))
                    (smram_lock s)
            then write_vga a v
            else write_dram a v                                    );;
            ret (tt, s)
      (* ---------------------------------------------------------- *)
      end.

  (** ** Contract

      Now here comes the section where FreeSpec is supposed to shine.
      We want to define a Contract which basically says: “Privileged
      read accesses only fetch value written by privileged write
      accesses.”

      *** Abstract State

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
    => if addr_eq a a'
       then v
       else s a'.

  Definition Smram_step
             (A: Type)
             (i: IMCH A)
             (s: SmramState)
    : SmramState :=
    match i with
    | WriteMem a v true (* Privileged Write Access within the SMRAM *)
      => if Smramdec a
         then update a v s
         else s
    | _ (* Any other primitives should not trigger a SMRAM change --*)
      => s
    end.

  (** *** Requirements

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

  (** *** Promises

      An Enforcer Component needs to stay syncronize with the abstract
      state of the Smram, that is deliver the value written by a
      privileged memory access.

   *)

  Definition Smram_promises
             (A: Type)
             (i: IMCH A)
             (ret: A)
             (s: SmramState)
    : Prop :=
    match i with
    | ReadMem a true (* Privileged Reads match the shadow Smram *)
      => ret ~= (s a)
    | _ (* No Guarantee otherwise *)
      => True
    end.

  (** *** Definition

   *)

  Definition smram_contract
             (s: SmramState)
    : Contract SmramState IMCH :=
    {| abstract := s
     ; abstract_step := Smram_step
     ; requirements := Smram_requirements
     ; promises := Smram_promises
     |}.

End SMRAM_EXAMPLE.
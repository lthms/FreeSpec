(* begin hide *)
Require Import Coq.Bool.Sumbool.
(* end hide *)

Require Import FreeSpec.Interp.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Program.

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
End SMRAM_EXAMPLE.
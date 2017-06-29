Require Import Coq.Bool.Sumbool.

Require Import FreeSpec.Interp.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Program.

Require Import FreeSpec.Examples.Map.

Section SMRAM_EXAMPLE.
  Variables (Addr: Type)
            (Value: Type)
            (Smram: Addr -> Prop)
            (Smramdec: forall (a: Addr), {Smram a}+{~Smram a}).

  Inductive IMCH
    : Interface :=
  | ReadMem (a: Addr)
            (smm: bool)
    : IMCH Value
  | WriteMem (a: Addr)
             (v: Value)
             (smm: bool)
    : IMCH unit.

  Record MCH
    : Type :=
    { smram_lock: bool
    }.

  Definition IDRAM := IMap Addr Value.
  Definition IVGA := IMap Addr Value.

  Local Open Scope prog_scope.

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

  Program Definition mch_refine
    : StatefulRefinement IMCH (IDRAM <+> IVGA) MCH :=
    fun {A: Type} (i: IMCH A) (s: MCH) =>
      match i with
      | ReadMem a true => x <- read_dram a
                        ; ret (x, s)
      | ReadMem a false => x <- if andb (bool_of_sumbool (Smramdec a))
                                        (smram_lock s)
                                then read_vga a
                                else read_dram a
                         ; ret (x, s)

      | WriteMem a v true => write_dram a v
                          ;; ret (tt, s)
      | WriteMem a v false => (if andb (bool_of_sumbool (Smramdec a))
                                       (smram_lock s)
                              then write_vga a v
                              else write_dram a v)
                           ;; ret (tt, s)
      end.
End SMRAM_EXAMPLE.
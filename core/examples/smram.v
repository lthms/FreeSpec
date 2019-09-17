From FreeSpec Require Import Core.
From Prelude Require Import Integer State Tactics.
From Coq Require Import ZArith.

Generalizable All Variables.

(** This library introduces the starting point of the FreeSpec framework, that
    is the original the original example which motivates everything else. *)

(** * The Verification Problem *)

(** We model a small subset of a x86 architecture, where a Memory Controller
    (now integrated into the CPU die) received memory accesses from cores, and
    dispatches these accesses to differont controllers.  In our case, we only
    consider the DRAM and VGA controllers.

    From a FreeSpec perspective, we therefore consider three components and as
    many interfaces, whith the memory controller exposing its own interfaces and
    relying on the interfaces of the two other controllers.

    The DRAM contains a special-purpose memory region called the SMRAM,
    dedicated to the x86 System Management Mode (SMM).  It is expected that only
    a CPU in SMM can access the SMRAM. The CPU set a dedicated pin (SMIACT) when
    it is in SMM, for the Memory Controller to know. *)

(** * Specifying the Subsystem *)

(** The overview of the system we want to moder is the following:

<<
             |
             |
             v
      -----------------
     +-----------------+
     |Memory Controller|
     +-----------------+
       |            |
       |            |
       v            v
 ----------     ----------
+----------+   +----------+
|   DRAM   |   |   VGA    |
|Controller|   |Controller|
+----------+   +----------+
>>
    We will focus on the Memory Controller, and only model the interfaces of the
    DRAM and VGA controllers. *)

(** ** Addressing Memories *)

(** We leave how the memory is actually addressed (in terms of memory cell
    addresses and contents) as a parameter of the model. *)

Parameters (address cell : Type)
           (address_eq : address -> address -> Prop)
           (address_eq_refl : forall (addr addr' : address),
               address_eq addr addr' -> address_eq addr' addr)
           (address_eq_dec : forall (addr addr' : address),
               { address_eq addr addr' } + { ~ address_eq addr addr' })
           (in_smram : address -> bool)
           (in_smram_morphism : forall (addr addr' : address),
               address_eq addr addr' -> in_smram addr = in_smram addr').

(** ** VGA and DRAM Controllers *)

(** We consider that the DRAM and VGA controllers expose the same interface
    which allows for reading from and writing to memory cells. *)

Inductive MEMORY : interface :=
| ReadFrom (addr : address) : MEMORY cell
| WriteTo (addr : address) (value : cell) : MEMORY unit.

Definition DRAM := MEMORY.
Definition VGA := MEMORY.

Definition dram_read_from `{ix :| DRAM <+> VGA} (addr : address)
  : impure ix cell :=
  request (in_left (ReadFrom addr)).

Definition dram_write_to `{ix :| DRAM <+> VGA} (addr : address) (val : cell)
  : impure ix unit :=
  request (in_left (WriteTo addr val)).

Definition vga_read_from `{ix :| DRAM <+> VGA} (addr : address) : impure ix cell :=
  request (in_right (ReadFrom addr)).

Definition vga_write_to `{ix :| DRAM <+> VGA} (addr : address) (val : cell)
  : impure ix unit :=
  request (in_right (WriteTo addr val)).

(** ** Memory Controller *)

Inductive smiact := smiact_set | smiact_unset.

Inductive MEMORY_CONTROLLER : interface :=
| Read (pin : smiact) (addr : address) : MEMORY_CONTROLLER cell
| Write (pin : smiact) (addr : address) (value : cell) : MEMORY_CONTROLLER unit.

Definition unwrap_sumbool {A B} (x : { A } + { B }) : bool :=
  if x then true else false.

Coercion unwrap_sumbool : sumbool >-> bool.

Definition dispatch {a} (addr : address)
    (unpriv : address -> impure (DRAM <+> VGA) a)
    (priv : address -> impure (DRAM <+> VGA) a)
  : state_t bool (impure (DRAM <+> VGA)) a :=
  do var reg <- get in
     lift (if (andb reg (in_smram addr))
           then unpriv addr
           else priv addr)
  end.

Definition memory_controller : component MEMORY_CONTROLLER (DRAM <+> VGA) bool :=
  fun _ op =>
    match op with

(** When SMIACT is set, the CPU is in SMM.  According to its specification, the
    Memory Controller can simply forward the memory access to the DRAM *)

    | Read smiact_set addr => lift (dram_read_from addr)
    | Write smiact_set addr val => lift (dram_write_to addr val)

(** On the contrary, when the SMIACT is not set, the CPU is not in SMM.  As a
    consequence, the memory controller implements a dedicated access control
    mechanism.  If the requested address belongs to the SMRAM and if the SMRAM
    lock has been set, then the memory access is forwarded to the VGA.
    Otherwise, it is forwarded to the DRAM by default.  This is specified in the
    [dispatch] function. *)

    | Read smiact_unset addr => dispatch addr vga_read_from dram_read_from
    | Write smiact_unset addr val =>
      dispatch addr (fun x => vga_write_to x val) (fun x => dram_write_to x val)
    end.

(** * Verifying our Subsystem *)

(** ** Memory View *)

Definition memory_view : Type := address -> cell.

Definition update_memory_view_address (ω : memory_view) (addr : address) (content : cell)
  : memory_view :=
  fun (addr' : address) => if address_eq_dec addr addr' then content else ω addr'.

(** ** Specification *)

(** *** DRAM Controller Specification *)

Definition update_dram_view (ω : memory_view) (a : Type) (p : DRAM a) (_ : a) : memory_view :=
  match p with
  | WriteTo a v  => update_memory_view_address ω a v
  | _ => ω
  end.

Inductive dram_promises (ω : memory_view) : forall (a : Type), DRAM a -> a -> Prop :=

| read_in_smram
    (a : address) (v : cell) (prom : in_smram a = true -> v = ω a)
  : dram_promises ω cell (ReadFrom a) (ω a)

| write (a : address) (v : cell) (r : unit)
  : dram_promises ω unit (WriteTo a v) r.

Definition dram_specs : specs DRAM memory_view :=
  {| witness_update := update_dram_view
   ; requirements := no_req
   ; promises := dram_promises
   |}.

(** *** Memory Controller Specification *)

Definition update_memory_controller_view (ω : memory_view)
    (a : Type) (p : MEMORY_CONTROLLER a) (_ : a)
  : memory_view :=
  match p with
  | Write smiact_set a v  => update_memory_view_address ω a v
  | _ => ω
  end.

Inductive memory_controller_promises (ω : memory_view)
  : forall (a : Type) (p : MEMORY_CONTROLLER a) (x : a), Prop :=

| memory_controller_read_promises (pin : smiact) (addr : address) (content : cell)
    (prom : pin = smiact_set -> in_smram addr = true -> ω addr = content)
  : memory_controller_promises ω cell (Read pin addr) content

| memory_controller_write_promises (pin : smiact) (addr : address) (content : cell) (b : unit)
  : memory_controller_promises ω unit (Write pin addr content) b.

Definition mc_specs : specs MEMORY_CONTROLLER memory_view :=
  {| witness_update := update_memory_controller_view
   ; requirements := no_req
   ; promises := memory_controller_promises
   |}.

(** ** Main Theorem *)

Definition memories_specs : specs (DRAM <+> VGA) (memory_view * unit) :=
  dram_specs <.> no_specs VGA.

Definition smram_pred (ωmc : memory_view) (s : bool) (ωdram : memory_view * unit) : Prop :=
  s = true /\ forall (a : address), in_smram a = true -> ωmc a = fst ωdram a.

Lemma memory_controller_trustworthy (a : Type) (op : MEMORY_CONTROLLER a)
    (ω : memory_view) (r : unit)
  : trustworthy_impure memories_specs (ω, r) (memory_controller a op true).
  induction op; induction pin;
    prove_impure; constructor.
Qed.

Theorem memory_controller_correct (ω : memory_view)
    (dram : semantics DRAM) (comp : compliant_semantics dram_specs ω dram)
    (vga : semantics VGA)
  : compliant_semantics mc_specs ω (derive_semantics memory_controller true (dram ⊗ vga)).
Proof.
  apply correct_component_derives_compliant_semantics with (pred := smram_pred)
                                                           (specj := memories_specs)
                                                           (ωj := (ω, tt)).
  + intros ωmc st [ωdram b] [st_true pred] a e req.
    split.
    ++ rewrite st_true.
       apply memory_controller_trustworthy.
    ++ intros x st' [ωdram' b'] trustworthy.
       destruct e.
       +++ split; [| now unroll_impure_run trustworthy ].
           unroll_impure_run trustworthy; constructor; intros pin_equ is_in_smram;
             rewrite pred; auto;
               now inversion prom; ssubst.
       +++ split.
           ++++ constructor.
           ++++ unroll_impure_run trustworthy;
                  split; auto;
                    intros addr' is_in_smram';
                    cbn; unfold update_memory_view_address;
                      destruct address_eq_dec as [ equ | nequ ]; auto.
                cbn in equ0.
                rewrite (in_smram_morphism addr addr' equ) in equ0.
                now rewrite equ0 in is_in_smram'.
  + split; auto.
  + remember (semplus dram vga) as mems.
    assert (compliant_semantics (dram_specs <.> no_specs VGA) (ω, tt) mems)
      as memcomp. {
      rewrite Heqmems.
      now apply compliant_semantics_semplus_no_specs.
    }
    clear Heqmems comp dram vga.
    remember (ω, tt) as ωmem.
    clear Heqωmem ω.
    revert memcomp;
      revert mems ωmem;
      cofix memory_controller_compliant_cofix;
      intros ω mems comp.
    constructor.
    ++ intros a e req.
       induction e; [| auto].
       inversion comp.
       now apply prom.
    ++ intros a e req.
       apply memory_controller_compliant_cofix.
       now apply compliant_semantics_requirement_compliant.
Qed.

Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.Function.
Require Import FreeSpec.Control.Option.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.Specs.Abstract.Abstract.
Require Import FreeSpec.Specs.Abstract.MemoryController.
Require Import FreeSpec.Specs.Address.
Require Import FreeSpec.Specs.Memory.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.
Local Open Scope free_prog_scope.
Local Open Scope free_control_scope.
Local Open Scope bool_scope.

(** * Interface

 *)

Inductive Strategy
  : Type :=
| UC
  : Strategy
| WB
  : Strategy.

Inductive Cache_interface
  : Interface :=
| read_cache (addr:        address)
             (privileged:  bool)
             (strat:       Strategy)
  : Cache_interface byte
| write_cache (addr:        address)
              (privileged:  bool)
              (strat:       Strategy)
              (val:         byte)
  : Cache_interface unit.

(** * Contract

 *)

Record Cache_abstract
  : Type :=
  { map_view:  Abstract
  ; strats:    address -> option Strategy
  }.

Definition Cache_abstract_step
           (A:    Type)
           (i:    Cache_interface A)
           (_:    A)
           (abs:  Cache_abstract)
  : Cache_abstract :=
  match i with
  | write_cache a true st x
    => {| map_view := update a x (map_view abs)
        ; strats   := fun (a':  address)
                      => if a ?= a'
                         then Some st
                         else strats abs a'
        |}
  | _
    => abs
  end.

Definition Cache_requirements
           (A:    Type)
           (i:    Cache_interface A)
           (abs:  Cache_abstract)
  : Prop :=
  match i with
  | read_cache a true st
    => match strats abs a with
       | Some st'
         => st = st'
       | None
         => True
       end
  | _
    => True
  end.

Definition Cache_promises
           (A:    Type)
           (i:    Cache_interface A)
           (ret:  A)
           (abs:  Cache_abstract)
  : Prop :=
  match i
        in Cache_interface A'
        return A = A' -> Prop
  with
  | read_cache a true _
    => fun (H:  A = byte)
       => eq_rect _ id ret _ H = map_view abs a
  | _
    => fun _
       => True
  end (eq_refl A).

Definition Cache_contract
  : Contract Cache_abstract Cache_interface :=
  {| abstract_step := Cache_abstract_step
   ; requirements  := Cache_requirements
   ; promises      := Cache_promises
   |}.

(** * Refinement

    ** State

 *)

Definition index
  : Type :=
  byte.

Definition address_to_index
           (a:  address)
  : index :=
  cast 8 a.

Record cline
  : Type :=
  { tag:    address
  ; dirty:  bool
  ; used:   bool
  ; val:    byte
  ; dirty_means_used:  dirty = true -> used = true
  }.

Definition cline_weq
  : cline -> cline -> Prop :=
  fun (c c':  cline)
  => tag c == tag c'
     /\ dirty c == dirty c'
     /\ used c == used c'
     /\ val c == val c'.

Lemma cline_weq_refl
      (c:  cline)
  : cline_weq c c.
Proof.
  split; [| split; [| split]];
    reflexivity.
Qed.

Lemma cline_weq_sym
      (c c':  cline)
  : cline_weq c c'
    -> cline_weq c' c.
Proof.
  intros [A [B [C D]]].
  split; [| split; [| split]];
    symmetry;
    assumption.
Qed.

Lemma cline_weq_trans
      (c c' c'':  cline)
  : cline_weq c c'
    -> cline_weq c' c''
    -> cline_weq c c''.
Proof.
  intros [A [B [C D]]]
         [A' [B' [C' D']]].
  split; [| split; [| split]];
    [ transitivity (tag c')
    | transitivity (dirty c')
    | transitivity (used c')
    | transitivity (val c')
    ];
    assumption.
Qed.

Add Parametric Relation
  : cline cline_weq
    reflexivity proved by cline_weq_refl
    symmetry proved by cline_weq_sym
    transitivity proved by cline_weq_trans
      as cline_weq_rel.

Instance cline_WEq
  : WEq cline :=
  { weq := cline_weq
  }.

Definition Cache_state
  : Type :=
  index -> cline.

Program Definition empty_cache
  : Cache_state :=
  pure {| tag   := box 32 0
        ; used  := false
        ; dirty := false
        ; val   := box 8 0
        |}.

Definition _cache_hit
           (a:    address)
           (map:  Cache_state)
  : bool :=
  weq_bool a <<< tag <<< map $ address_to_index a.

Definition _get_cline
           (i:    index)
           (map:  Cache_state)
  : cline :=
  map i.

Definition Cache_monad
  : Type -> Type :=
  StateT Cache_state (Program MemoryController_interface).

Definition cache_hit
           (a:    address)
  : Cache_monad bool :=
  _cache_hit a <$> get.

Definition get_cline
           (i:  index)
  : Cache_monad cline :=
  _get_cline i <$> get.

Definition dirty_cline
           (i:  index)
  : Cache_monad bool :=
  dirty <$> get_cline i.

Program Definition _overwrite_cline
        (a:    address)
        (v:    byte)
        (abs:  Cache_state)
  : Cache_state :=
  fun (i':  index)
  => if i' ?= (address_to_index a)
     then {| tag := a
           ; val := v
           ; dirty := false
           ; used := true
           |}
     else abs i'.

Program Definition _update_cline
        (i:    index)
        (v:    byte)
        (abs:  Cache_state)
  : Cache_state :=
  fun (i':  index)
  => if i' ?= i
     then {| tag := tag (abs i)
           ; val := v
           ; dirty := true
           ; used := true
           |}
     else abs i'.

Definition overwrite_cline
           (a:  address)
           (v:  byte)
  : Cache_monad unit :=
  modify $ _overwrite_cline a v.

Definition update_cline
           (a:  address)
           (v:  byte)
  : Cache_monad unit :=
  modify $ _update_cline (address_to_index a) v.

Definition get_val
           (i:  index)
  : Cache_monad byte :=
  val <$> get_cline i.

Definition get_tag
           (i:  index)
  : Cache_monad address:=
  tag <$> get_cline i.

Definition do_mc
           {A:  Type}
           (i:  MemoryController_interface A)
  : Cache_monad A :=
  '[i].

Definition prepare_line
           (a:     address)
           (priv:  bool)
  : Cache_monad unit :=
  miss <- negb <$> cache_hit a                                       ;
  when miss (d  <- dirty_cline $ address_to_index a                  ;
             v' <- get_val $ address_to_index a                      ;
             a' <- get_tag $ address_to_index a                      ;

             when d $ do_mc (write_mc a' priv v')                   ;;

             v <- do_mc $ read_mc a priv                             ;
             overwrite_cline a v).

Definition reset_cache
  : Cache_monad unit :=
  put empty_cache.

Definition match_smrr
           (a:  address)
  : Cache_monad bool :=
  pure (in_smram a).

Definition Cache_specification
  : StatefulRefinement Cache_interface
                       MemoryController_interface
                       Cache_state :=
  fun (A:  Type)
      (i:  Cache_interface A)
  => match i with
     | read_cache a priv UC (* --- Uncachable read ---------------- *)
       => do_mc $ read_mc a priv
       (* --------------------------------------------------------- *)
     | read_cache a priv WB (* --- Write-back read ---------------- *)
       => smrr <- match_smrr a                                       ;
          if negb priv && smrr
          then pure (box 8 255)
          else prepare_line a priv                                  ;;
               get_val $ address_to_index a
       (* --------------------------------------------------------- *)
     | write_cache a priv UC val (* --- Uncachable write ---------- *)
       => do_mc $ write_mc a priv val
       (* --------------------------------------------------------- *)
     | write_cache a priv WB val (* --- Write-back write ---------- *)
       => smrr <- match_smrr a                                       ;
          if negb priv && smrr
          then pure tt
          else prepare_line a priv                                  ;;
               update_cline a val
       (* --------------------------------------------------------- *)
     end.
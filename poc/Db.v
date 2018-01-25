Require Import FreeSpec.Specification.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Either.
Require Import FreeSpec.Abstract.
Require Import FreeSpec.Fail.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.

Local Open Scope free_weq_scope.

Generalizable All Variables.
Set Implicit Arguments.

Module Type DbSpec.
  Parameters (K:         Type)
             (Res:       Type)
             (Err:       Type).
End DbSpec.

Module DB (Spec:  DbSpec).

  Record Entity :=
    { key:  Spec.K
    ; val:  Spec.Res
    }.

  (** * Simple

   *)

  Inductive Query
    : Interface :=
  | select (selector:  Entity -> bool)
    : Query (list Entity)
  | insert (value:     Spec.Res)
    : Query Entity
  | update (selector:  Entity -> bool)
           (update:    Spec.Res -> Spec.Res)
    : Query unit
  | delete (selector:  Entity -> bool)
    : Query unit.

  Module DSL.
    Definition select
               (sel:  Entity -> bool)
    : Program Query (list Entity) :=
      Request (select sel).

    Definition update
               (sel:  Entity -> bool)
               (up:   Spec.Res -> Spec.Res)
    : Program Query unit :=
      Request (update sel up).

    Definition delete
               (sel:  Entity -> bool)
      : Program Query unit :=
      Request (delete sel).

    Definition insert
               (v:  Spec.Res)
      : Program Query Entity :=
      Request (insert v).
  End DSL.

  (** ** Functional Specification

   *)

  Module QuerySemantics.
    Definition State
    : Type :=
      Spec.K -> option Spec.Res.

    Definition empty
      : State :=
      fun _
      => None.

    Definition query_insert
              `{WEqBool Spec.K}
               (k:  Spec.K)
               (r:  Spec.Res)
               (s:  State)
      : State :=
      fun (k':  Spec.K)
      => if k ?= k'
         then Some r
         else s k'.

    Definition query_delete
               (select:  Entity -> bool)
               (s:  State)
      : State :=
      fun (k:  Spec.K)
      => match s k with
         | Some x
           => if select {| key := k; val := x |}
              then None
              else Some x
         | None
           => None
         end.

    Definition query_update
               (select:  Entity -> bool)
               (up:      Spec.Res -> Spec.Res)
               (s:  State)
      : State :=
      fun (k:  Spec.K)
      => match s k with
         | Some x
           => if select {| key := k; val := x |}
              then Some $ up x
              else Some x
         | None
           => None
         end.

    Definition query_step
              `{WEqBool Spec.K}
               (A:      Type)
               (q:      Query A)
               (x:      A)
               (state:  State)
      : State :=
      match q, x with
      | insert _, entity
        => query_insert (key entity) (val entity) state
      | update sel up, tt
        => query_update sel up state
      | delete sel, tt
        => query_delete sel state
      | _, _
        => state
      end.

    Definition query_precondition
               (A:  Type)
               (q:  Query A)
               (s:  State)
      : Prop :=
      True.

    Definition is_key_of
               (k:      Spec.K)
               (v:      Spec.Res)
               (state:  State)
      : Prop :=
      match state k with
      | Some x => x = v
      | None => False
      end.

    Inductive is_key_of_l
              (k:  Spec.K)
              (v:  Spec.Res)
      : list Entity -> Prop :=
    | is_key (l:   list Entity)
      : is_key_of_l k v (cons {| key := k; val := v |} l)
    | was_key (l:       list Entity)
              (Hl:      is_key_of_l k v l)
              (entity:  Entity)
      : is_key_of_l k v (cons entity l).

    Fixpoint key_count
            `{WEqBool Spec.K}
             (k:  Spec.K)
             (l:  list Entity)
      : nat :=
      match l with
      | cons entity rest
        => (if key entity ?= k then 1 else 0) + key_count k rest
      | nil
        => 0
      end.

    Definition query_select_postcondition_res_wf
              `{WEqBool Spec.K}
               (res:       list Entity)
      : Prop :=
      forall (k:  Spec.K),
        key_count k res < 2.

    Definition query_select_postcondition_state_to_res
               (selector:  Entity -> bool)
               (res:       list Entity)
               (state:     State)
      : Prop :=
      forall (k:  Spec.K)
             (v:  Spec.Res),
        is_key_of k v state
        -> selector {| key := k; val := v |} = true
        -> is_key_of_l k v res.

    Definition query_select_postcondition_res_to_state
               (selector:  Entity -> bool)
               (res:       list Entity)
               (state:     State)
      : Prop :=
      forall (k:  Spec.K)
             (v:  Spec.Res),
        is_key_of_l k v res
        -> selector {| key := k; val := v |} = true
           /\ is_key_of k v state.

    Inductive query_postcondition
             `{WEqBool Spec.K}
      : forall (A:  Type),
        Query A -> A -> State -> Prop :=
    | insert_postcondition (state:  State)
                      (v:      Spec.Res)
                      (res:    Entity)
                      (Hval:   val res = v)
                      (Hkey:   state (key res) = None)
      : query_postcondition (insert v) res state
    | select_postcondition (selector:  Entity -> bool)
                      (res:       list Entity)
                      (state:     State)
                      (Hwf:       query_select_postcondition_res_wf res)
                      (Hrs:       query_select_postcondition_res_to_state selector res state)
                      (Hsr:       query_select_postcondition_state_to_res selector res state)
      : query_postcondition (select selector) res state
    | update_postcondition (state:     State)
                      (selector:  Entity -> bool)
                      (up:        Spec.Res -> Spec.Res)
      : query_postcondition (update selector up) tt state
    | delete_postcondition (state:     State)
                      (selector:  Entity -> bool)
      : query_postcondition (delete selector) tt state.

    Definition query_specs
              `{WEqBool Spec.K}
      : Specification State Query :=
      {| abstract_step := query_step
         ; precondition := query_precondition
         ; postcondition := query_postcondition
      |}.

    Lemma query_specs_compliance
         `{WEqBool Spec.K}
          {A:      Type}
          (p:      Program Query A)
          (state:  State)
      : p =| query_specs[state].
    Proof.
      revert state.
      induction p; intros state.
      + constructor.
      + repeat constructor.
      + constructor.
        ++ apply IHp.
        ++ intros int Hint.
           apply H1.
    Qed.
  End QuerySemantics.

  (** * Transactional

   *)
  Definition Transaction (A:  Type)
    : Type :=
    Program Query A.

  Polymorphic Inductive i
    : Interface :=
  | transaction {A:  Type}
                (p:  Transaction A)
    : i A.

  Module TransactionSemantics.
    Record State
          `{WEqBool Spec.K}
    : Type :=
      { view:                QuerySemantics.State
      ; semantics:           Semantics Query
      ; semantics_complies:  semantics |= QuerySemantics.query_specs [view]
      }.

    (* For the record, an implementation of this function using
    Program (the Coq Spec.Keyword, not the FreeSpec Monad) would failed
    here because of universe error. *)
    Definition transaction_step
           `{WEqBool Spec.K}
            (A:      Type)
            (instr:  i A)
            (x:      A)
            (state:  State)
      : State.
      refine (
          match instr with
          | transaction p
            => {| view                := specification_derive p (semantics state) QuerySemantics.query_specs (view state)
                ; semantics           := execProgram (semantics state) p
                ; semantics_complies  := _
               |}
      end
        ).
      rewrite <- abstract_exec_exec_program_same with (w:=view state)
                                                      (abs_step:=abstract_step QuerySemantics.query_specs).
      apply compliant_correct_compliant.
      + exact (semantics_complies state).
      + apply QuerySemantics.query_specs_compliance.
    Qed.

    Definition transaction_req
              `{WEqBool Spec.K}
               (A:      Type)
               (instr:  i A)
               (state:  State)
      : Prop :=
      True.

    Definition transaction_postcondition
              `{WEqBool Spec.K}
               (A:      Type)
               (instr:  i A)
               (x:      A)
               (state:  State)
      : Prop :=
      match instr, x with
      | transaction p, x
        => evalProgram (semantics state) p = x
      end.

    Definition transaction_specs
               `{WEqBool Spec.K}
      : Specification State i :=
      {| abstract_step := transaction_step
       ; precondition := transaction_req
       ; postcondition := transaction_postcondition
       |}.
  End TransactionSemantics.
End DB.
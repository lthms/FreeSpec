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

Require Import Coq.Bool.Bool.
Require Import Sumbool.

Require Import FreeSpec.TemporalLogic.
Require Import FreeSpec.TemporalLogic.Notations.
Require Import FreeSpec.Program.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.
Require Import FreeSpec.Specification.Constant.

Require Import Prelude.PropBool.
Require Import Prelude.Equality.
Require Import Prelude.Control.

Local Open Scope formula_scope.
Local Open Scope prelude_scope.
Local Open Scope free_prog_scope.

Lemma neq_sym
      {T:        Type}
     `{Equality T}
      (t:        T)
      (Hneq_sym: t /= t)
  : False.
Proof.
  assert (t == t) as Heq by (reflexivity).
  apply Hneq_sym in Heq.
  exact Heq.
Qed.

Section MAP.
  Variables (Key:         Type)
            (key_eq:      Equality Key)
            (key_eqdec:   EqualityBool Key)
            (Value:       Type)
            (value_eq:    Equality Value)
            (value_eqdec: EqualityBool Value).

  Inductive IMap
    : Interface :=
  | Read (k: Key)
    : IMap Value
  | Write (k: Key)
          (v: Value)
    : IMap unit.

  Definition State := Key -> Value.

  Definition map_program_step
             (A:   Type)
             (map: State)
             (i:   IMap A)
    : (A * State) :=
    match i with
    | Read k
      => (map k, map)
    | Write k v
      => (tt, fun k'
              => if k ?= k'
                 then v
                 else map k')
    end.

  Definition MapSemantics
             (s: State)
    : Semantics IMap
    := mkSemantics map_program_step s.

  Definition MapProgram := Program IMap.

  Definition read_then_write
             (k: Key)
             (v: Value)
    : MapProgram Value :=
    _ <- [Write k v];
    [Read k].

  Lemma write_then_read_1
        (s: State)
        (k: Key)
        (v: Value)
    : evalProgram (MapSemantics s) (read_then_write k v) == v.
  Proof.
    cbn.
    rewrite weq_bool_refl.
    reflexivity.
  Qed.

  Lemma write_then_read_2
        (s:    State)
        (k k': Key)
        (v:    Value)
        (Hneq: k' /= k)
    : evalProgram (MapSemantics s)
                  (_ <- [Write k' v];
                     [Read k])
       == evalProgram (MapSemantics s) ([Read k]) .
  Proof.
    cbn.
    apply equalb_false in Hneq.
    rewrite Hneq.
    reflexivity.
  Qed.

  Section SPECIFICATION.
    Variable (x: Value).

    Definition never_read_x_precondition
               (A: Type)
               (i: IMap A) :=
      match i with
      | Read k => True
      | Write k v => v /= x
      end.

    Definition never_read_x_postcondition
               (A: Type)
               (i: IMap A)
      : A -> Prop :=
      match i with
      | Read k
        => fun v => v /= x
      | Write k v
        => fun x => True
      end.

    Definition never_read_x_specification :=
      constant_specification never_read_x_precondition
                             never_read_x_postcondition.

    Definition x_free_map
               (s: State)
      : Prop :=
      forall k, (s k) /= x.

    Lemma map_semantics_preserves_inv
      : precondition_preserves_inv never_read_x_precondition
                                   map_program_step
                                   x_free_map.
    Proof.
      unfold precondition_preserves_inv.
      induction e.
      + intros s Hinv Hreq.
        exact Hinv.
      + intros s Hinv Hreq.
        cbn in *.
        unfold x_free_map.
        intros k'.
        destruct (k ?= k').
        ++ exact Hreq.
        ++ unfold x_free_map in Hinv.
           apply (Hinv k').
    Qed.

    Lemma map_semantics_enforces_postcondition
      : precondition_enforces_postcondition never_read_x_precondition
                                            never_read_x_postcondition
                                            map_program_step x_free_map.
    Proof.
      unfold precondition_enforces_postcondition.
      induction e.
      + intros s Hinv Hreq.
        apply (Hinv k).
      + intros s Hinv Hreq.
        cbn in *.
        trivial.
    Qed.

    Corollary MapSemantics_complies_with_specification
              (s:    State)
              (Hinv: x_free_map s)
      : MapSemantics s |= never_read_x_specification[tt].
    Proof.
      apply (const_specification_enforcement never_read_x_precondition
                                        never_read_x_postcondition
                                        map_program_step
                                        x_free_map
                                        map_semantics_preserves_inv
                                        map_semantics_enforces_postcondition).
      exact Hinv.
    Qed.

    Variables (k k': Key).

    Definition read_write
      : MapProgram unit :=
      v <- [Read k];
      [Write k' v].

    Lemma read_write_specificationful
      : read_write =| never_read_x_specification[tt].
    Proof.
      unfold read_write.
      constructor.
      + constructor.
        cbn.
        trivial.
      + intros int Henf.
        rewrite (tt_singleton
                   (specification_derive ([Read k]) int never_read_x_specification tt)
                   tt).
        unfold never_read_x_specification in Henf.
        inversion Henf as [Hprom Hreq].
        assert (never_read_x_postcondition Value (Read k) (evalEffect int (Read k)))
          as Hnext
            by (apply Hprom; cbn; trivial).
        constructor.
        exact Hnext.
    Qed.

    Definition write_k_x
               (i: ISet IMap)
      : Prop :=
      match i with
      | effect (Write k' v')
        => k == k' /\ x == v'
      | _
        => False
      end.

    Definition write_k_x_bool
               (i: ISet IMap)
      : bool :=
      match i with
      | effect (Write k' v')
        => andb (k ?= k') (x ?= v')
      | _
        => false
      end.

    Instance write_k_x_PropBool
      : PropBool1 write_k_x write_k_x_bool.
    Proof.
      constructor.
      intro i.
      split; induction i; induction i.
      + intro Heq.
        cbn in *.
        discriminate Heq.
      + intro Heq.
        cbn in *.
        apply andb_prop in Heq.
        destruct Heq as [H1 H2].
        split.
        ++ apply equalb_equal in H1.
           exact H1.
        ++ apply equalb_equal in H2.
           exact H2.
      + intro Heq.
        cbn in *.
        destruct Heq.
      + intro Heq.
        cbn in *.
        destruct Heq as [H1 H2].
        apply andb_true_intro.
        split.
        ++ apply equalb_equal in H1.
           exact H1.
        ++ apply equalb_equal in H2.
           exact H2.
    Defined.

    Definition write_k_x_inst
      : Dec (ISet IMap) :=
      {| prop      := write_k_x
       ; prop_bool := write_k_x_bool
       |}.

    Definition not_read_k
               (i: ISet IMap)
      : Prop :=
      match i with
      | effect (Read k')
        => k /= k'
      | _
        => False
      end.

    Definition not_read_k_bool
               (i: ISet IMap)
      : bool :=
      match i with
      | effect (Read k')
        => negb (k ?= k')
      | _
        => false
      end.

    Instance not_read_k_PropBool
      : PropBool1 not_read_k not_read_k_bool.
    Proof.
      constructor.
      intros i.
      split.
      + intro Heq.
        induction i; induction i.
        ++ cbn in *.
           apply negb_true_iff in Heq.
           apply equalb_false.
           exact Heq.
        ++ cbn in *.
           discriminate Heq.
      + intro H.
        induction i; induction i.
        ++ cbn in *.
           apply negb_true_iff.
           apply equalb_false in H.
           exact H.
        ++ cbn in *.
           destruct H.
    Defined.

    Definition not_read_k_inst
      : Dec (ISet IMap) :=
      {| prop      := not_read_k
       ; prop_bool := not_read_k_bool
       |}.

    Definition policy_step
      : Formula (ISet IMap) :=
      (⟙) ⊢ write_k_x_inst ⟶ (⬜ not_read_k_inst).

    Definition write_read_write
               (k': Key)
               (v': Value)
      : MapProgram unit :=
      _ <- [Write k x]                                               ;
      _ <- [Read k']                                                 ;
      [Write k v'].

    Variables (int: Semantics IMap).

    Lemma enforces_policy
          (s: State)
      : forall k' v',
        k /= k'
        -> x /= v'
        -> halt_satisfies (snd (runFormula int
                                      (write_read_write k' v')
                                      policy_step)).
    Proof.
      intros.
      cbn.
      repeat rewrite weq_bool_refl.
      cbn.
      trivial.
    Qed.

    Inductive invar
              (s: State)
      : Formula (ISet IMap) -> Prop :=
    | invar_1 (H: s k /= x)
      : invar s policy_step
    | invar_2
      : invar s (globally not_read_k_inst).

    (*
    Definition tl_never_read_x_specification :=
      {| tl_precondition := policy_step
       ; tl_postcondition     := never_read_x_postcondition
       |}.

    Lemma enforcing_policy_step_invar
          {A: Type}
          (i: IMap A)
          (s: State)
      : invar s policy_step
        -> instruction_satisfies (instruction i) policy_step
        -> invar (snd (map_program_step _ s i)) (tl_step (instruction i) policy_step).
    Proof.
      intros Hinvar Hinst.
      inversion Hinvar.
      induction i.
      + cbn.
        apply invar_1.
        exact H.
      + cbn in *.
     *)
  End SPECIFICATION.
End MAP.

Arguments Write [Key Value].
Arguments Read [Key Value].
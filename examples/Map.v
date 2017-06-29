Require Import FreeSpec.TemporalLogic.
Require Import FreeSpec.TemporalLogic.Notations.
Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Utils.
Require Import FreeSpec.Equiv.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Contract.Constant.

Require Import Sumbool.

Local Open Scope formula_scope.
Local Open Scope eq_scope.

Lemma neq_sym
      {T: Type}
     `{Eq T}
      (t: T)
      (Hneq_sym: t /= t)
  : False.
Proof.
  assert (t == t) as Heq by (reflexivity).
  apply Hneq_sym in Heq.
  exact Heq.
Qed.

Section MAP.
  Local Open Scope prog_scope.

  Variables (Key: Type)
            (key_eq: Eq Key)
            (key_eqdec: EqDec Key)
            (Value: Type)
            (value_eq: Eq Value)
            (value_eqdec: EqDec Value).

  Inductive IMap: Type -> Type :=
  | Read (k: Key)
    : IMap Value
  | Write (k: Key)
          (v: Value)
    : IMap unit.

  Definition State := Key -> Value.

  Definition map_program_step
             (A: Type)
             (map: State)
             (i: IMap A)
    : (A * State) :=
    match i with
    | Read k => (map k, map)
    | Write k v => (tt, fun k' =>
                          if k =? k'
                          then v
                          else map k')
    end.

  Definition MapInterp
             (s: State)
    := mkInterp map_program_step s.

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
    : evalProgram (MapInterp s) (read_then_write k v) == v.
  Proof.
    cbn.
    destruct (equiv_dec) as [He|Hne].
    + reflexivity.
    + apply neq_sym in Hne.
      destruct Hne.
  Qed.

  Lemma write_then_read_2
        (s: State)
        (k k': Key)
        (v: Value)
        (Hneq: ~ (k == k'))
    : evalProgram (MapInterp s)
                  (_ <- [Write k' v];
                     [Read k])
       == evalProgram (MapInterp s) ([Read k]) .
  Proof.
    cbn.
    destruct (equiv_dec k' k) as [He|Hne].
    + apply eq_sym in He.
      apply Hneq in He.
      destruct He.
    + reflexivity.
  Qed.

  Section CONTRACT.
    Variable (x: Value).

    Definition never_read_x_requirements
               (A: Type)
               (i: IMap A) :=
      match i with
      | Read k => True
      | Write k v => v /= x
      end.

    Definition never_read_x_promises
               (A: Type)
               (i: IMap A)
      : typeret i -> Prop :=
      match i with
      | Read k => fun v => v /= x
      | Write k v => fun x => True
      end.

    Definition never_read_x_contract := constant_contract never_read_x_requirements
                                                          never_read_x_promises.

    Definition x_free_map
               (s: State)
      : Prop :=
      forall k, (s k) /= x.

    Lemma map_interp_preserves_inv
      : requirements_preserves_inv never_read_x_requirements map_program_step x_free_map.
    Proof.
      unfold requirements_preserves_inv.
      induction i.
      + intros s Hinv Hreq.
        exact Hinv.
      + intros s Hinv Hreq.
        cbn in *.
        unfold x_free_map.
        intros k'.
        destruct (equiv_dec k k').
        ++ exact Hreq.
        ++ unfold x_free_map in Hinv.
           apply (Hinv k').
    Qed.

    Lemma map_interp_enforces_promises
      : requirements_brings_promises never_read_x_requirements never_read_x_promises map_program_step x_free_map.
    Proof.
      unfold requirements_brings_promises.
      induction i.
      + intros s Hinv Hreq.
        apply (Hinv k).
      + intros s Hinv Hreq.
        cbn in *.
        trivial.
    Qed.

    Corollary MapInterp_enforce_contract
              (s:    State)
              (Hinv: x_free_map s)
      : Enforcer (MapInterp s) never_read_x_contract.
    Proof.
      apply (const_contract_enforcement never_read_x_requirements
                                        never_read_x_promises
                                        map_program_step
                                        x_free_map
                                        map_interp_preserves_inv
                                        map_interp_enforces_promises).
      exact Hinv.
    Qed.

    Variables (k k': Key).

    Definition read_write
      : MapProgram unit :=
      v <- [Read k];
      [Write k' v].

    Lemma read_write_contractful
      : contractfull_program never_read_x_contract read_write.
    Proof.
      unfold read_write.
      constructor.
      + constructor.
        cbn.
        trivial.
      + intros int Henf.
        assert (contract_derive ([Read k]) int never_read_x_contract = never_read_x_contract).
        reflexivity.
        repeat rewrite H.
        unfold never_read_x_contract in Henf.
        inversion Henf as [c Hprom Hreq].
        assert (never_read_x_promises Value (Read k) (evalInstruction int (Read k)))
          as Hnext
            by (apply Hprom; cbn; trivial).
        constructor.
        exact Hnext.
    Qed.

    Definition write_k_x
               (i: ISet IMap)
      : Prop :=
      match i with
      | instruction (Write k' v')
        => k == k' /\ x == v'
      | _
        => False
      end.

    Definition write_k_x_dec
               (i: ISet IMap)
      : {write_k_x i}+{~write_k_x i}.
      induction i.
      refine (
          match i with
          | (Write k' v')
            => decide_dec (sumbool_and _ _ _ _
                                       (k =? k')
                                       (x =? v'))
          | _
            => false_dec
          end
        ); cbn; intuition.
    Defined.

    Definition write_k_x_inst
      : Dec (ISet IMap) :=
      {| prop := write_k_x
       ; prop_dec := write_k_x_dec
      |}.

    Definition not_read_k
               (i: ISet IMap)
      : Prop :=
      match i with
      | instruction (Read k')
        => k /= k'
      | _
        => False
      end.

    Definition not_read_k_dec
               (i: ISet IMap)
      : {not_read_k i}+{~not_read_k i}.
      induction i.
      refine (
          match i with
          | (Read k')
            => if k =? k'
               then false_dec
               else true_dec
          | _
            => false_dec
          end
        ); cbn; intuition.
    Defined.

    Definition not_read_k_inst
      : Dec (ISet IMap) :=
      {| prop := not_read_k
       ; prop_dec := not_read_k_dec
      |}.

    Definition policy_step
      : Formula (ISet IMap) :=
      (⟙) ⊢ write_k_x_inst ⟶ (⬜ not_read_k_inst).

    Definition write_read_write
               (k': Key)
               (v': Value)
      : MapProgram unit :=
      _ <- [Write k x];
      _ <- [Read k'];
      [Write k v'].

    Variables (int: Interp IMap).

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
      destruct (sumbool_and _ _ _ _ (k =? k) (x =? x)); cbn.
      + trivial.
      + destruct (sumbool_and _ _ _ _ (k =? k) (x =? v')); cbn; trivial.
    Qed.

    Inductive invar
              (s: State)
      : Formula (ISet IMap) -> Prop :=
    | invar_1 (H: s k /= x)
      : invar s policy_step
    | invar_2
      : invar s (globally not_read_k_inst).

    (*
    Definition tl_never_read_x_contract :=
      {| tl_requirements := policy_step
       ; tl_promises     := never_read_x_promises
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
    Admitted.
     *)
  End CONTRACT.
End MAP.
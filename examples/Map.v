Require Import Coq.Bool.Bool.

Require Import FreeSpec.PropBool.
Require Import FreeSpec.TemporalLogic.
Require Import FreeSpec.TemporalLogic.Notations.
Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Utils.
Require Import FreeSpec.WEq.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Contract.Constant.

Require Import Sumbool.

Local Open Scope formula_scope.
Local Open Scope free_weq_scope.
Local Open Scope prog_scope.

Lemma neq_sym
      {T:        Type}
     `{WEq T}
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
            (key_eq:      WEq Key)
            (key_eqdec:   WEqBool Key)
            (Value:       Type)
            (value_eq:    WEq Value)
            (value_eqdec: WEqBool Value).

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

  Definition MapInterp
             (s: State)
    : Interp IMap
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
    rewrite weq_bool_refl.
    reflexivity.
  Qed.

  Lemma write_then_read_2
        (s:    State)
        (k k': Key)
        (v:    Value)
        (Hneq: k' /= k)
    : evalProgram (MapInterp s)
                  (_ <- [Write k' v];
                     [Read k])
       == evalProgram (MapInterp s) ([Read k]) .
  Proof.
    cbn.
    apply weq_bool_false in Hneq.
    rewrite Hneq.
    reflexivity.
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
      : A -> Prop :=
      match i with
      | Read k
        => fun v => v /= x
      | Write k v
        => fun x => True
      end.

    Definition never_read_x_contract :=
      constant_contract never_read_x_requirements
                        never_read_x_promises.

    Definition x_free_map
               (s: State)
      : Prop :=
      forall k, (s k) /= x.

    Lemma map_interp_preserves_inv
      : requirements_preserves_inv never_read_x_requirements
                                   map_program_step
                                   x_free_map.
    Proof.
      unfold requirements_preserves_inv.
      induction i.
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

    Lemma map_interp_enforces_promises
      : requirements_brings_promises never_read_x_requirements
                                     never_read_x_promises
                                     map_program_step x_free_map.
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
      : MapInterp s :> never_read_x_contract[tt].
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
      : read_write :> never_read_x_contract[tt].
    Proof.
      unfold read_write.
      constructor.
      + constructor.
        cbn.
        trivial.
      + intros int Henf.
        rewrite (tt_singleton
                   (contract_derive ([Read k]) int never_read_x_contract tt)
                   tt).
        unfold never_read_x_contract in Henf.
        inversion Henf as [Hprom Hreq].
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

    Definition write_k_x_bool
               (i: ISet IMap)
      : bool :=
      match i with
      | instruction (Write k' v')
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
        ++ apply weq_bool_weq in H1.
           exact H1.
        ++ apply weq_bool_weq in H2.
           exact H2.
      + intro Heq.
        cbn in *.
        destruct Heq.
      + intro Heq.
        cbn in *.
        destruct Heq as [H1 H2].
        apply andb_true_intro.
        split.
        ++ apply weq_bool_weq in H1.
           exact H1.
        ++ apply weq_bool_weq in H2.
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
      | instruction (Read k')
        => k /= k'
      | _
        => False
      end.

    Definition not_read_k_bool
               (i: ISet IMap)
      : bool :=
      match i with
      | instruction (Read k')
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
           apply weq_bool_false.
           exact Heq.
        ++ cbn in *.
           discriminate Heq.
      + intro H.
        induction i; induction i.
        ++ cbn in *.
           apply negb_true_iff.
           apply weq_bool_false in H.
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

Arguments Write [Key Value].
Arguments Read [Key Value].
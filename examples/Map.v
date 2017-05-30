Require Import FreeSpec.TemporalLogic.
Require Import FreeSpec.Program.
Require Import FreeSpec.Utils.

Require Import Sumbool.

Class Eq (T: Type) :=
  { eq (t t': T): Prop
  ; eq_refl (t: T): eq t t
  ; eq_sym (t t': T): eq t t' -> eq t' t
  ; eq_trans (t t' t'': T): eq t t' -> eq t' t'' -> eq t t''
  ; eq_dec (t t': T): {eq t t'}+{~ eq t t'}
  }.

Lemma neq_sym
      {T: Type}
     `{Eq T}
      (t: T)
      (Hneq_sym: ~ eq t t)
  : False.
Proof.
  assert (eq t t) as Heq by (apply eq_refl).
  apply Hneq_sym in Heq.
  exact Heq.
Qed.

Section MAP.
  Local Open Scope prog_scope.

  Variables (Key: Type)
            (key_eq: Eq Key)
            (Value: Type)
            (value_eq: Eq Value).

  Inductive Instruction: Type -> Type :=
  | Read (k: Key)
    : Instruction Value
  | Write (k: Key)
          (v: Value)
    : Instruction unit.

  Definition State := Key -> Value.

  Definition map_program_step
             (A: Type)
             (map: State)
             (i: Instruction A)
    : (A * State) :=
    match i with
    | Read k => (map k, map)
    | Write k v => (tt, fun k' =>
                          if eq_dec k k'
                          then v
                          else map k')
    end.

  Definition MapInterp
             (s: State)
    := mkInterp map_program_step s.


  Definition MapProgram := Program Instruction.

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
    : MapInterp s <· read_then_write k v = v.
  Proof.
    cbn.
    destruct (eq_dec) as [He|Hne].
    + reflexivity.
    + apply neq_sym in Hne.
      destruct Hne.
  Qed.

  Lemma write_then_read_2
        (s: State)
        (k k': Key)
        (v: Value)
        (Hneq: ~ eq k k')
    : MapInterp s <· (_ <- [Write k' v];
                      [Read k])
       = MapInterp s <· [Read k].
  Proof.
    cbn.
    destruct (eq_dec k' k) as [He|Hne].
    + apply eq_sym in He.
      apply Hneq in He.
      destruct He.
    + reflexivity.
  Qed.

  Section CONTRACT.
    Variable (x: Value).

    Definition never_read_x_requirements
               (A: Type)
               (i: Instruction A) :=
      match i with
      | Read k => True
      | Write k v => ~ eq v x
      end.

    Definition never_read_x_promises
               (A: Type)
               (i: Instruction A)
      : typeret i -> Prop :=
      match i with
      | Read k => fun v => ~ eq v x
      | Write k v => fun x => True
      end.

    Definition never_read_x_contract :=
      {| requirements := never_read_x_requirements
       ; promises     := never_read_x_promises
       |}.

    Definition x_free_map
               (s: State)
      : Prop :=
      forall k, ~eq (s k) x.

    Lemma map_interp_preserves_inv
      : contract_preserves_inv map_program_step x_free_map never_read_x_contract.
    Proof.
      unfold contract_preserves_inv.
      induction i.
      + intros s Hinv Hreq.
        exact Hinv.
      + intros s Hinv Hreq.
        cbn in *.
        unfold x_free_map.
        intros k'.
        destruct (eq_dec k k').
        - exact Hreq.
        - unfold x_free_map in Hinv.
          apply (Hinv k').
    Qed.

    Lemma map_interp_enforces_promises
      : contract_enforces_promises map_program_step x_free_map never_read_x_contract.
    Proof.
      unfold contract_enforces_promises.
      induction i.
      + intros s Hinv Hreq.
        cbn in *.
        apply (Hinv k).
      + intros s Hinv Hreq.
        cbn in *.
        trivial.
    Qed.

    Lemma MapInterp_enforce_contract
      : forall (s:    State)
               (Hinv: x_free_map s),
        Enforcer never_read_x_contract (MapInterp s).
    Proof.
      apply (stateful_contract_enforcement map_program_step
                                           x_free_map
                                           never_read_x_contract
                                           map_interp_preserves_inv
                                           map_interp_enforces_promises).
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
        constructor.
        inversion Henf as [Hprom Hreq].
        assert (never_read_x_promises Value (Read k) (fst (interpret int (Read k))))
          as Hnext
            by (apply Hprom; cbn; trivial).

        cbn in *.
        exact Hnext.
    Qed.
  End CONTRACT.

  Section TL.
    Variables (k: Key)
              (v: Value).

    Definition write_k_v
               (i: ISet Instruction)
      : Prop :=
      match i with
      | instruction _ (Write k' v')
        => eq k k' /\ eq v v'
      | _
        => False
      end.

    Definition write_k_v_dec
               (i: ISet Instruction)
      : {write_k_v i}+{~write_k_v i}.
      induction i.
      refine (
          match i with
          | (Write k' v')
            => decide_dec (sumbool_and _ _ _ _
                                       (eq_dec k k')
                                       (eq_dec v v'))
          | _
            => false_dec
          end
        ); cbn; intuition.
    Defined.

    Definition write_k_v_inst
      : Instant (ISet Instruction) :=
      {| prop := write_k_v
       ; prop_dec := write_k_v_dec
      |}.

    Definition not_read_k
               (i: ISet Instruction)
      : Prop :=
      match i with
      | instruction _ (Read k')
        => ~eq k k'
      | _
        => False
      end.

    Definition not_read_k_dec
               (i: ISet Instruction)
      : {not_read_k i}+{~not_read_k i}.
      induction i.
      refine (
          match i with
          | (Read k')
            => if eq_dec k k'
               then false_dec
               else true_dec
          | _
            => false_dec
          end
        ); cbn; intuition.
    Defined.

    Definition not_read_k_inst
      : Instant (ISet Instruction) :=
      {| prop := not_read_k
       ; prop_dec := not_read_k_dec
      |}.

    Definition erase_k
               (i: ISet Instruction)
      : Prop :=
      match i with
      | instruction _ (Write k v')
        => eq v v'
      | _
        => False
      end.

    Definition erase_k_dec
               (i: ISet Instruction)
      : {erase_k i}+{~erase_k i}.
      induction i.
      refine (
          match i with
          | (Write k v')
            => eq_dec v v'
          | _
            => false_dec
          end
        ); cbn; intuition.
    Defined.

    Definition erase_k_inst
      : Instant (ISet Instruction) :=
      {| prop := erase_k
       ; prop_dec := erase_k_dec
      |}.

    Definition policy_step
      : TL (ISet Instruction) :=
      switch _
             (true _)
             write_k_v_inst
             (switch _
                     (globally _ not_read_k_inst)
                     erase_k_inst
                     (true _)).

    Definition policy
      : TL (ISet Instruction) :=
      loop _ policy_step policy_step.

    Definition write_read_write
               (k': Key)
               (v': Value)
      : MapProgram unit :=
      _ <- [Write k v];
      _ <- [Read k'];
      [Write k v'].

    Section PROOF.
      Variables (int: Interp Instruction).

      Lemma enforces_policy
            (s: State)
      : forall k' v',
        ~ eq k k'
        -> ~ eq v v'
        -> halt_satisfies _ (snd (runTL _
                                        int
                                        (write_read_write k' v')
                                        policy)).
        intros.
        cbn.
        destruct (sumbool_and _ _ _ _ (eq_dec k k) (eq_dec v v)).
        cbn.
        destruct (eq_dec v v).
        destruct (sumbool_and _ _ _ _ (true_dec) (true_dec)).
        cbn.
        destruct (eq_dec k k').
        cbn.
        trivial.
        cbn.
        destruct (eq_dec v v').
        apply H0 in e0.
        destruct e0.
        destruct a0.
        destruct H1.
        cbn.
        trivial.
        cbn.
        trivial.
        cbn.
        trivial.
        cbn.
        destruct (sumbool_and _ _ _ _ (eq_dec k k) (eq_dec v v')).
        destruct (eq_dec v v').
        cbn.
        trivial.
        cbn.
        trivial.
        cbn.
        trivial.
      Qed.
    End PROOF.
  End TL.
End MAP.
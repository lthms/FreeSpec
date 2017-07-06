Require Import FreeSpec.Interp.
Require Import FreeSpec.Contract.
Require Import FreeSpec.TemporalLogic.
Require Import FreeSpec.Contract.

Definition temporal_step (I: Interface) :=
  fun (R: Type) (i: I R) => tl_step (instruction i).

Definition temporal_requirements (I: Interface) :=
  fun (R: Type) (i: I R) => instruction_satisfies (instruction i).

Definition temporal_contract
           {I: Interface}
           (promises: forall (R: Type)
                             (i: I R),
               R -> Formula (ISet I) -> Prop)
  : Contract (Formula (ISet I)) I :=
  {| abstract_step := temporal_step I
   ; requirements := temporal_requirements I
   ; promises := fun (R: Type) => @promises R
   |}.

Definition temporal_requirements_preserves_inv
           {I: Interface}
           {State: Type}
           (step: @PS I State)
           (inv: Formula (ISet I) -> State -> Prop)
  := forall (A: Type)
            (i: I A)
            (s: State)
            (tl: Formula (ISet I)),
    inv tl s
    -> instruction_satisfies (instruction i) tl
    -> inv (tl_step (instruction i) tl) (snd (step A s i)).

Lemma temporal_contract_preserves_inv
      {I: Interface}
      {State: Type}
      (step: @PS I State)
      (inv: Formula (ISet I) -> State -> Prop)
  : temporal_requirements_preserves_inv step inv
    -> contract_preserves_inv (temporal_requirements I)
                              (temporal_step I)
                              inv
                              step.
Proof.
  unfold temporal_requirements_preserves_inv, contract_preserves_inv.
  intros Hreq B i tl s Hinv Hsatisfies.
  apply (Hreq B i s tl Hinv Hsatisfies).
Qed.

Definition temporal_requirements_enforces_promises
           {I: Interface}
           {State: Type}
           (step: @PS I State)
           (inv: Formula (ISet I) -> State -> Prop)
           (promises: forall (R: Type)
                             (i: I R),
               R -> Formula (ISet I) -> Prop)
  := forall (A: Type)
            (i: I A)
            (s: State)
            (tl: Formula (ISet I)),
    inv tl s
    -> instruction_satisfies (instruction i) tl
    -> promises A i (fst (step A s i)) tl.

Lemma temporal_contract_enforces_promises
      {I: Interface}
      {State: Type}
      (step: @PS I State)
      (inv: Formula (ISet I) -> State -> Prop)
      (promises: forall (R: Type)
                        (i: I R),
          R -> Formula (ISet I) -> Prop)
  : temporal_requirements_enforces_promises step inv promises
    -> contract_enforces_promises (temporal_requirements I)
                                  promises
                                  (temporal_step I)
                                  inv
                                  step.
Proof.
  unfold temporal_requirements_enforces_promises, contract_enforces_promises.
  intros Hreq B i tl s Hinv Hsatisfies.
  apply (Hreq B i tl s Hinv Hsatisfies).
Qed.

Lemma temporal_contract_enforcement
      {I: Interface}
      {State: Type}
      (step: @PS I State)
      (inv: Formula (ISet I) -> State -> Prop)
      (promises: forall (R: Type)
                        (i: I R),
          R -> Formula (ISet I) -> Prop)
      (tl: Formula (ISet I))
      (Hpres: temporal_requirements_preserves_inv step inv)
      (Henf: temporal_requirements_enforces_promises step inv promises)
  : forall (s: State),
    inv tl s
    -> Enforcer (mkInterp step s) (temporal_contract promises) tl.
Proof.
  intros s Hinv.
  apply (stateful_contract_enforcement (temporal_contract promises)
                                       tl
                                       inv
                                       step).
  + apply temporal_contract_preserves_inv.
    exact Hpres.
  + apply temporal_contract_enforces_promises.
    exact Henf.
  + exact Hinv.
Qed.
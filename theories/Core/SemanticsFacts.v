From ExtLib Require Import StateMonad.

From FreeSpec.Core Require Import Impure Contract.
From FreeSpec.Core Require Export Semantics.

(** * Semantics Compliance *)

(** Given a semantics [sem], and a witness [ω] if [sem] computes results which
    satisfies [c] callee obligations for effects which satisfy [c] caller
    obligations and if the resulting semantics produces after interpreting [e]
    complies to [c] in accordance to [ω'], where [ω'] is the new witness state
    after [e] interpretation then [sem] complies to [c] in accordance to [ω] *)

CoInductive compliant_semantics `{MayProvide ix i} `(c : contract i Ω)
  : Ω -> semantics ix -> Prop :=
| compliant_semantics_rec
    (sem : semantics ix) (ω : Ω)
    (o_callee : forall {α} (e : ix α),
        gen_caller_obligation c ω e -> gen_callee_obligation c ω e (eval_effect sem e))
    (next : forall {α} (e : ix α),
        gen_caller_obligation c ω e
        -> compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e))
  : compliant_semantics c ω sem.

(** Proving that semantics obtained from the [store] function are compliant with
    [store_specs] is relatively simple. *)

Lemma store_complies_to_store_specs {s} (st : s)
  : compliant_semantics (store_specs s) st (store st).

Proof.
  revert st; cofix compliant_semantics_rec; intros st.
  constructor.
  + intros a [ | st' ] _.
    ++ now constructor.
    ++ now constructor.
  + intros a e req.
    cbn.
    replace (exec_effect (store st) e)
      with (store (store_update s st a e (eval_effect (store st) e)))
      by now destruct e as [| st'].
    apply compliant_semantics_rec.
Qed.

Hint Resolve store_complies_to_store_specs : freespec.

Lemma compliant_semantics_caller_obligation_callee_obligation `{MayProvide ix i}
   `(c : contract i Ω) (ω : Ω)
   `(e : ix α) (o_caller : gen_caller_obligation c ω e)
    (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : gen_callee_obligation c ω e (eval_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply o_callee.
Qed.

Hint Resolve compliant_semantics_caller_obligation_callee_obligation : freespec.

Lemma compliant_semantics_caller_obligation_compliant `{MayProvide ix i} {Ω α} (c : contract i Ω) (ω : Ω)
  (e : ix α) (o_caller : gen_caller_obligation c ω e)
  (sem : semantics ix) (comp : compliant_semantics c ω sem)
  : compliant_semantics c (gen_witness_update c ω e (eval_effect sem e)) (exec_effect sem e).

Proof.
  inversion comp; ssubst.
  now apply next.
Qed.

Hint Resolve compliant_semantics_caller_obligation_compliant : freespec.

Lemma no_contract_compliant_semantics `{MayProvide ix i} (sem : semantics ix) (u : unit)
  : compliant_semantics (no_contract i) u sem.

Proof.
  revert sem.
  cofix no_contract_compliant_semantics; intros sem.
  constructor.
  + intros α e req.
    unfold gen_caller_obligation, gen_callee_obligation.
    destruct proj_p; constructor.
  + intros α e req.
    unfold gen_witness_update.
    destruct (proj_p e); [ apply no_contract_compliant_semantics | auto with freespec ].
Qed.

Hint Resolve no_contract_compliant_semantics : freespec.

#[program]
Instance compliant_semantics_Proper `{MayProvide ix i} `(c : contract i Ω)
  : Proper (eq ==> semantics_eq ==> Basics.impl) (compliant_semantics c).

Next Obligation.
  add_morphism_tactic.
  unfold Basics.impl.
  cofix proper.
  intros ω sem sem' equ comp.
  inversion equ; subst.
  inversion comp; subst.
  constructor; intros a e pre.
  + rewrite <- res_eq.
    now apply o_callee.
  + specialize next_eqv with a e.
    eapply proper.
    exact next_eqv.
    rewrite <- res_eq.
    now apply next.
Qed.

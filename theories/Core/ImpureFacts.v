From FreeSpec.Core Require Export Impure.

(** ** Equivalence *)

(** Due to the definition of [impure] and [impure_bind], we could decide to rely
    on Coq built-in [eq] to reason about impure computations equivalence, but we
    would have to use the functional extensionality axiom to handle the
    continuation of the [request_then] constructor. In order to keep FreeSpec
    axiom-free, we rather provide a custom equivalence for [impure] terms.

    The definition of [impure_equiv] is two-fold. *)

Inductive impure_eq {i α} : impure i α -> impure i α -> Prop  :=

(** - Two impure computations are equivalent if and only if they compute the
      exact same term (wrt. Coq [eq] function). *)

| local_eq (x : α) : impure_eq (local x) (local x)

(** - Two computations which consist in requesting the interpretation of an
      primitive and passing the result to a monadic continuation are equivalent
      if and only if they use the exact same primitive in the first place, and
      given any result the interpretation of this primitive may produce, their
      continuation returns equivalent impure computations. *)

| request_eq {β} (e : i β) (f g : β -> impure i α)
    (equ : function_eq impure_eq f g)
  : impure_eq (request_then e f) (request_then e g).

Infix "===" := impure_eq : impure_scope.

(** The definition of [impure_equiv] is very similar to [eq], with the exception
    of the treatment of the continuation. There is no much effort to put into
    proving this is indeed a proper equivalence. *)

#[program]
Instance impure_Equivalence : @Equivalence (impure i α) impure_eq := {}.

Next Obligation.
  intros p.
  induction p; constructor.
  intros x.
  apply H.
Qed.

Next Obligation.
  intros p q equ.
  induction equ; constructor.
  intros x.
  apply H.
Qed.

Next Obligation.
  intros p q r pq qr.
  revert p r pq qr.
  induction q; intros p r pq qr.
  + inversion pq; ssubst; inversion qr; ssubst.
    constructor.
  + inversion pq; ssubst; inversion qr; ssubst.
    constructor.
    intros x.
    cbv in H.
    now apply H with (β := x).
Qed.

#[program]
Instance request_then_Proper
  : Proper (eq ==> function_eq impure_eq ==> impure_eq) (@request_then i α β).

Next Obligation.
  add_morphism_tactic.
  intros e f g equ.
  constructor.
  intros y.
  specialize (equ y).
  now rewrite equ.
Qed.

#[program]
Instance impure_bind_Proper
  : Proper (impure_eq ==> function_eq impure_eq ==> impure_eq) (@impure_bind i α β).

Next Obligation.
  add_morphism_tactic.
  intros x y equ1 f g equ2.
  induction equ1.
  + cbn.
    now rewrite (equ2 x).
  + cbn.
    constructor.
    intros x.
    apply H.
Qed.

Ltac change_request_then :=
  match goal with
  | |- (request_then ?e ?f === request_then ?e ?g)%impure =>
    let R := fresh "R" in
    assert (R: function_eq impure_eq f g); [ intros ?x | rewrite R; clear R ]
  end.

Ltac change_impure_bind :=
  match goal with
  | |- (impure_bind ?e ?f === impure_bind ?e ?g)%impure =>
    let R := fresh "R" in
    assert (R: function_eq impure_eq f g); [ intros ?x | now rewrite R ]
  end.

Lemma impure_bind_local {i α} (p : impure i α)
  : (impure_bind p (fun x => local x) === p)%impure.

Proof.
  induction p.
  + reflexivity.
  + cbn.
    change_request_then; [ | reflexivity ].
    now rewrite H.
Qed.

Lemma impure_bind_assoc {i α β δ}
  (p : impure i α) (f : α -> impure i β) (g : β -> impure i δ)
  : (impure_bind (impure_bind p f) g
     === impure_bind p (fun x => impure_bind (f x) g))%impure.

Proof.
  induction p; [reflexivity | ].
  cbn.
  change_request_then; auto.
  reflexivity.
Qed.

Instance impure_map_Proper
  : Proper (function_eq eq ==> impure_eq ==> impure_eq) (@impure_map i α β).

Proof.
  add_morphism_tactic.
  intros f g equf p q equp.
  unfold impure_map.
  rewrite equp.
  change_impure_bind.
  now rewrite equf.
Qed.

#[program]
Instance impure_apply_Proper
  : Proper (impure_eq ==> impure_eq ==> impure_eq) (@impure_apply i α β).

Next Obligation.
  add_morphism_tactic.
  intros p q equ1 r s equ2.
  unfold impure_apply.
  rewrite equ1.
  change_impure_bind.
  cbn.
  now rewrite equ2.
Qed.

Lemma bind_request_then_assoc `(e : i a) `(f : a -> impure i b) `(g : b -> impure i c)
  : request_then e f >>= g = request_then e (fun x => f x >>= g).

Proof.
  reflexivity.
Qed.

Require Import FreeSpec.Semantics.
Require Import FreeSpec.Specification.
Require Import FreeSpec.TemporalLogic.
Require Import FreeSpec.Specification.

Definition temporal_step
           (I: Interface) :=
  fun (R:  Type)
      (e:  I R)
      (_:  R)
  => tl_step (effect e).

Definition temporal_precondition
           (I: Interface) :=
  fun (R:  Type)
      (e:  I R)
  => effect_satisfies (effect e).

Definition temporal_specification
           {I:        Interface}
           (postcondition: forall (R: Type)
                             (i: I R),
               R -> Formula (ISet I) -> Prop)
  : Specification (Formula (ISet I)) I :=
  {| abstract_step  := temporal_step I
   ; precondition   := temporal_precondition I
   ; postcondition  := fun (R: Type) => @postcondition R
   |}.

Definition temporal_precondition_preserves_inv
           {I:      Interface}
           {State:  Type}
           (step:   @PS I State)
           (inv:    Formula (ISet I) -> State -> Prop)
  := forall (A:   Type)
            (e:   I A)
            (s:   State)
            (tl:  Formula (ISet I)),
    inv tl s
    -> effect_satisfies (effect e) tl
    -> inv (tl_step (effect e) tl) (snd (step A s e)).

Fact temporal_specification_preserves_inv
     {I:              Interface}
     {State:          Type}
     (postcondition:  forall (R:  Type)
                             (e:  I R),
         R -> Formula (ISet I) -> Prop)
     (step:           @PS I State)
     (inv:            Formula (ISet I) -> State -> Prop)
  : temporal_precondition_preserves_inv step inv
    -> specification_preserves_inv (temporal_specification postcondition)
                                   inv
                                   step.
Proof.
  unfold temporal_precondition_preserves_inv, specification_preserves_inv.
  intros Hreq B e tl s Hinv Hsatisfies.
  apply (Hreq B e s tl Hinv Hsatisfies).
Qed.

Definition temporal_precondition_enforces_postcondition
           {I:              Interface}
           {State:          Type}
           (step:           @PS I State)
           (inv:            Formula (ISet I) -> State -> Prop)
           (postcondition:  forall (R:  Type)
                                   (i:  I R),
               R -> Formula (ISet I) -> Prop)
  := forall (A:   Type)
            (e:   I A)
            (s:   State)
            (tl:  Formula (ISet I)),
    inv tl s
    -> effect_satisfies (effect e) tl
    -> postcondition A e (fst (step A s e)) tl.

Fact temporal_specification_enforces_postcondition
     {I:              Interface}
     {State:          Type}
     (step:           @PS I State)
     (inv:            Formula (ISet I) -> State -> Prop)
     (postcondition:  forall (R:  Type)
                             (e:  I R),
         R -> Formula (ISet I) -> Prop)
  : temporal_precondition_enforces_postcondition step inv postcondition
    -> specification_enforces_postcondition (temporal_specification postcondition)
                                            inv
                                            step.
Proof.
  unfold temporal_precondition_enforces_postcondition, specification_enforces_postcondition.
  intros Hreq B e tl s Hinv Hsatisfies.
  apply (Hreq B e tl s Hinv Hsatisfies).
Qed.

Lemma temporal_specification_enforcement
      {I:              Interface}
      {State:          Type}
      (step:           @PS I State)
      (inv:            Formula (ISet I) -> State -> Prop)
      (postcondition:  forall (R:  Type)
                              (e:  I R),
          R -> Formula (ISet I) -> Prop)
      (tl:             Formula (ISet I))
      (Hpres:          temporal_precondition_preserves_inv step inv)
      (Henf:           temporal_precondition_enforces_postcondition step inv postcondition)
  : forall (s: State),
    inv tl s
    -> (mkSemantics step s) |= (temporal_specification postcondition)[tl].
Proof.
  intros s Hinv.
  apply (stateful_specification_enforcement (temporal_specification postcondition)
                                            tl
                                            inv
                                            step).
  + apply temporal_specification_preserves_inv.
    exact Hpres.
  + apply temporal_specification_enforces_postcondition.
    exact Henf.
  + exact Hinv.
Qed.
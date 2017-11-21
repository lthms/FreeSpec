(* begin hide *)
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Import FreeSpec.WEq.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.

Local Open Scope free_weq_scope.

(** Often, one [Program] will rely on more than one [Interface]. As a
    consequence, we need to compose together the main components of
    the FreeSpec Formalism. This library provides several operators to
    do so.

 *)

(** * [Interface] Composition

 *)
Inductive IntCompose
          (I I': Interface)
          (A:    Type)
  : Type :=
| ileft (i: I A)
  : IntCompose I I' A
| iright (i: I' A)
  : IntCompose I I' A.

Arguments ileft [I I' A] (i).
Arguments iright [I I' A] (i).

(** Let [I] and [I'] be two Interfaces. [I <+> I'] denotes the
    [Interface] which unify [I] and [I'].

 *)

Infix "<+>" :=
  (IntCompose)
    (at level 50, left associativity)
  : free_scope.

Local Open Scope free_scope.

Fixpoint liftl
         {I I': Interface}
         {A: Type}
         (p: Program I A)
  : Program (I <+> I') A :=
  match p with
  | ret a => ret a
  | instr i => instr (ileft i)
  | pbind p f => pbind (liftl p) (fun x =>  liftl (f x))
  end.

Fixpoint liftr
         {I I': Interface}
         {A: Type}
         (p: Program I' A)
  : Program (I <+> I') A :=
  match p with
  | ret a => ret a
  | instr i => instr (iright i)
  | pbind p f => pbind (liftr p) (fun x =>  liftr (f x))
  end.

(** * Interpretation

    It is easy to derive an [Interp]reter for [I <+> I'] with one
    interpreter for [I] and one for [I'].

    ** Proof-friendly Interpretation

 *)

CoFixpoint mkCompInterp
           {I I': Interface}
           (int:  Interp I)
           (int': Interp I')
  : Interp (I <+> I') :=
  interp (fun {A: Type}
              (x: (I <+> I') A)
          => match x with
             | ileft i => ( fst (interpret int i)
                          , mkCompInterp (snd (interpret int i)) int'
                          )
             | iright i' => ( fst (interpret int' i')
                            , mkCompInterp int (snd (interpret int' i'))
                            )
             end).

(** We define three morphisms. Just in case. By doing so, we will be
    able to use the [rewrite] tactic to replace one interpreter with
    an equivalent one.

 *)

Add Parametric Morphism
    (I I': Interface)
  : (@mkCompInterp I I')
    with signature (interp_eq) ==> (interp_eq) ==> (interp_eq)
      as mk_comp_interp_complete_morphism.
Proof.
  cofix.
  intros int1 int2 Heq int1' int2' Heq'.
  constructor.
  + intros A i.
    unfold mkCompInterp.
    induction i;
      cbn; [ rewrite Heq | rewrite Heq' ];
      reflexivity.
  + intros A i.
    induction i;
      cbn.
    ++ assert (snd (interpret int1 i) == snd (interpret int2 i)). {
         rewrite Heq.
         reflexivity.
       }
       apply (mk_comp_interp_complete_morphism_Proper (snd (interpret int1 i))
                                                      (snd (interpret int2 i))
                                                      H
                                                      int1'
                                                      int2'
                                                      Heq').
    ++ assert (snd (interpret int1' i) == snd (interpret int2' i)). {
         rewrite Heq'.
         reflexivity.
       }
       apply (mk_comp_interp_complete_morphism_Proper int1
                                                      int2
                                                      Heq
                                                      (snd (interpret int1' i))
                                                      (snd (interpret int2' i))
                                                      H).
Qed.

(* TODO: are these two morphisms really needed? *)
Add Parametric Morphism
    (I I': Interface)
  : (@mkCompInterp I I')
    with signature (interp_eq) ==> (eq) ==> (interp_eq)
      as mk_comp_interp_left_morphism.
Proof.
  intros int1 int2 Heq int'.
  rewrite Heq.
  reflexivity.
Qed.

Add Parametric Morphism
    (I I': Interface)
  : (@mkCompInterp I I')
    with signature (eq) ==> (interp_eq) ==> (interp_eq)
      as mk_comp_interp_right_morphism.
Proof.
  intros int int1' int2' Heq.
  rewrite Heq.
  reflexivity.
Qed.

Infix "|+|" :=
  (mkCompInterp)
    (at level 50, left associativity)
  : free_scope.

(** ** Effective Interpretation

    We also define a “maybe more efficient version” of [mkCompInterp]
    which uses the [let ... in] language construction.

 *)

CoFixpoint mkCompInterp'
           {I I': Interface}
           (int:  Interp I)
           (int': Interp I')
  : Interp (I <+> I') :=
  interp (fun {A: Type}
              (x: (I <+> I') A)
          => match x with
             | ileft i => let (a, int2) := interpret int i
                          in (a, mkCompInterp' int2 int')
             | iright i' => let (a, int2') := interpret int' i'
                            in (a, mkCompInterp' int int2')
             end).

(** It can be shown that these two interpreter compositions are
    equivalent.

 *)

Fact mk_comp_interp_equivalence
     {I I': Interface}
  : forall (int:  Interp I)
           (int': Interp I'),
    int |+| int' == mkCompInterp' int int'.
Proof.
  cofix.
  intros int int'.
  constructor.
  + intros A i.
    induction i;
      unfold mkCompInterp, mkCompInterp';
      unfold evalInstruction;
      cbn; [ induction (interpret int i)
           | induction (interpret int' i)
           ];
      reflexivity.
  + intros A i.
    induction i;
      unfold mkCompInterp, mkCompInterp', execInstruction;
      cbn; [
        induction (interpret int i)
      | induction (interpret int' i)
      ]; cbn;
        apply mk_comp_interp_equivalence.
Qed.

(** * Contract Composition

    Because Interfaces can be composed together, contracts need their
    composition operator too.

 *)

Definition compose_step
           {S S':  Type}
           {I I':  Interface}
           (step:  forall {A: Type}, I A -> A -> S -> S)
           (step': forall {A: Type}, I' A -> A -> S' -> S')
           (A:     Type)
           (i:     (I <+> I') A)
           (a:     A)
           (x:     S * S')
  : S * S' :=
  match x, i with
  | (s, s'), ileft i =>
    (step i a s, s')
  | (s, s'), iright i =>
    (s, step' i a s')
  end.

Definition compose_requirements
           {S S': Type}
           {I I': Interface}
           (req:  forall {A: Type}, I A -> S -> Prop)
           (req': forall {A: Type}, I' A -> S' -> Prop)
           (A:    Type)
           (i:    (I <+> I') A)
           (x:    S * S')
  : Prop :=
  match x, i with
  | (s, s'), ileft i =>
    req i s
  | (s, s'), iright i =>
    req' i s'
  end.

Definition compose_promises
           {S S':  Type}
           {I I':  Interface}
           (prom:  forall {A: Type} (i: I A), A -> S -> Prop)
           (prom': forall {A: Type} (i: I' A), A -> S' -> Prop)
           (A:     Type)
           (i:     (I <+> I') A)
           (ret:   A)
           (x:     S * S')
  : Prop :=
  match x, i with
  | (s, s'), ileft i
    => prom i ret s
  | (s, s'), iright i
    => prom' i ret s'
  end.

Definition composeContract
           {S S': Type}
           {I I': Interface}
           (c:    Contract S I)
           (c':   Contract S' I')
  : Contract (S * S') (I <+> I') :=
  {| abstract_step := compose_step (abstract_step c) (abstract_step c')
   ; requirements := compose_requirements (requirements c) (requirements c')
   ; promises := compose_promises (promises c) (promises c')
   |}.

Infix ":+:" :=
  (composeContract)
    (at level 50, left associativity)
  : free_scope.

Lemma compliant_interpreters_compose_compliant_interpreter
      {S S': Type}
      {I I': Interface}
  : forall (int:  Interp I)
           (int': Interp I')
           (c:    Contract S I)
           (c':   Contract S' I')
           (s:    S)
           (s':   S'),
    int |= c[s]
    -> int' |= c'[s']
    -> int |+| int' |= (c :+: c')[(s, s')].
Proof.
  cofix.
  intros int int' c c' s s' Hint Hint'.
  constructor.
  + intros A i Hreq.
    induction i; cbn; cbn in Hreq.
    ++ apply enforcer_enforces_promises; [ exact Hint
                                         | exact Hreq
                                         ].
    ++ apply enforcer_enforces_promises; [ exact Hint'
                                         | exact Hreq
                                         ].
  + intros A i Hreq.
    induction i; cbn; cbn in *.
    ++ apply compliant_interpreters_compose_compliant_interpreter.
       +++ apply enforcer_instruction_compliant_enforcer.
           ++++ exact Hint.
           ++++ constructor.
                exact Hreq.
       +++ exact Hint'.
    ++ apply compliant_interpreters_compose_compliant_interpreter.
       +++ exact Hint.
       +++ apply enforcer_instruction_compliant_enforcer.
           ++++ exact Hint'.
           ++++ constructor.
                exact Hreq.
Qed.

(** ** Left

 *)

Definition expand_step_left
           {S:    Type}
           {I:    Interface}
           (step: forall {A: Type} (i: I A), A -> S -> S)
           (I':   Interface)
           (A:    Type)
           (i:    (I <+> I') A)
           (a:    A)
           (s:    S)
  : S :=
  match i with
  | ileft i
    => step i a s
  | _
    => s
  end.

Definition expand_req_left
           {S:   Type}
           {I:   Interface}
           (req: forall {A: Type}, I A -> S -> Prop)
           (I':  Interface)
           (A:   Type)
           (i:   (I <+> I') A)
           (s:   S)
  : Prop :=
  match i with
  | ileft i
    => req i s
  | _
    => True
  end.

Definition expand_prom_left
           {S:    Type}
           {I:    Interface}
           (prom: forall {A: Type} (i: I A), A -> S -> Prop)
           (I':   Interface)
           (A:    Type)
           (i:    (I <+> I') A)
           (a:    A)
           (s:    S)
  : Prop :=
  match i with
  | ileft i
    => prom i a s
  | _
    => True
  end.

Definition expand_contract_left
           {S:  Type}
           {I:  Interface}
           (c:  Contract S I)
           (I': Interface)
  : Contract S (I <+> I') :=
  {| abstract_step := expand_step_left (abstract_step c) I'
   ; requirements := expand_req_left (requirements c) I'
   ; promises := expand_prom_left (promises c) I'
   |}.

Lemma expand_enforcer_left
  : forall {S:    Type}
           {I I': Interface}
           {c:    Contract S I}
           {s:    S}
           {int:  Interp I}
           (Henf: int |= c[s])
           (int': Interp I'),
    int |+| int' |= (expand_contract_left c I')[s].
Proof.
  cofix.
  intros S I I' c s int Henf int'.
  assert (Henf': int |= c[s]) by apply Henf.
  destruct Henf.
  constructor.
  + intros A i; induction i; cbn; [| trivial].
    apply Hprom.
  + intros A i Hreq.
    induction i; cbn.
    ++ apply expand_enforcer_left.
       apply Henf.
       exact Hreq.
    ++ apply expand_enforcer_left.
       exact Henf'.
Qed.

(** ** Right

 *)

Definition expand_step_right
           {S:    Type}
           {I:    Interface}
           (step: forall {A: Type} (i: I A), A -> S -> S)
           (I':   Interface)
           (A:    Type)
           (i:    (I' <+> I) A)
           (a:    A)
           (s:    S)
  : S :=
  match i with
  | iright i
    => step i a s
  | _
    => s
  end.

Definition expand_req_right
           {S:   Type}
           {I:   Interface}
           (req: forall {A: Type}, I A -> S -> Prop)
           (I':  Interface)
           (A:   Type)
           (i:   (I' <+> I) A)
           (s:   S)
  : Prop :=
  match i with
  | iright i
    => req i s
  | _
    => True
  end.

Definition expand_prom_right
           {S:    Type}
           {I:    Interface}
           (prom: forall {A: Type} (i: I A), A -> S -> Prop)
           (I':   Interface)
           (A:    Type)
           (i:    (I' <+> I) A)
           (a:    A)
           (s:    S)
  : Prop :=
  match i with
  | iright i
    => prom i a s
  | _
    => True
  end.

Definition expand_contract_right
           {S:  Type}
           {I:  Interface}
           (c:  Contract S I)
           (I': Interface)
  : Contract S (I' <+> I) :=
  {| abstract_step := expand_step_right (abstract_step c) I'
   ; requirements := expand_req_right (requirements c) I'
   ; promises := expand_prom_right (promises c) I'
   |}.

Lemma expand_enforcer_right
  : forall {S:    Type}
           {I I': Interface}
           {c:    Contract S I}
           {s:    S}
           {int:  Interp I}
           (Henf: int |= c[s])
           (int': Interp I'),
    int' |+| int |= (expand_contract_right c I')[s].
Proof.
  cofix.
  intros S I I' c s int Henf int'.
  assert (Henf': int |= c[s]) by apply Henf.
  destruct Henf.
  constructor.
  + intros A i; induction i; cbn; [trivial |].
    apply Hprom.
  + intros A i Hreq.
    induction i; cbn.
    ++ apply expand_enforcer_right.
       exact Henf'.
    ++ apply expand_enforcer_right.
       apply Henf.
       exact Hreq.
Qed.

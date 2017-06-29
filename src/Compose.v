(* begin hide *)
Require Import Coq.Setoids.Setoid.
(* end hide *)

Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Equiv.

Local Open Scope eq_scope.

(** * [Interface] Composition

    A given Component may rely on more than one [Interface]. We
    therefore propose the [IntCompose] structure to compose
    [Interface]s together.

 *)
Inductive IntCompose
          (I I': Interface)
  : Interface :=
| ileft (A: Type)
        (i: I A)
  : IntCompose I I' A
| iright (A: Type)
         (i: I' A)
  : IntCompose I I' A.

Arguments ileft [I I' A] (i).
Arguments iright [I I' A] (i).

(** Let [I] and [I'] be two Interfaces. [I <+> I'] denotes the
    [Interface] which unify [I] and [I'].

 *)

Notation "a '<+>' b" := (IntCompose a b) (at level 20, left associativity).

(** * Interpretation

    It is easy to derive an [Interp]reter for [I <+> I'] with one
    interpreter for [I] and one for [I'].

    ** Proof-friendly Interpretation

 *)

CoFixpoint mkCompInterp
           {I I': Interface}
           (int: Interp I)
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

(** We define three morphisms. Just in case.

 *)

Add Parametric Morphism
    (I I': Interface)
  : (@mkCompInterp I I')
    with signature (interp_eq) ==> (interp_eq) ==> (interp_eq)
      as mk_comp_interp_complete_morphism.
Proof.
  (* program_eq is a co-inductive property *)
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

Infix "|+|" := (mkCompInterp) (at level 42).

(** ** Effective Interpretation

    We also define a “maybe more efficient version” of [mkCompInterp]
    which uses the [let ... in] language construction.

 *)

CoFixpoint mkCompInterp'
           {I I': Interface}
           (int: Interp I)
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

Fact mk_comp_interp_equivalence
     {I I': Interface}
  : forall (int: Interp I)
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
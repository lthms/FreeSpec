Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.PropBool.
Require Import FreeSpec.MonadInterp.
Require Import FreeSpec.Control.Classes.

Local Open Scope free_control_scope.
Local Close Scope nat_scope.
Local Open Scope list_scope.

Class ContractBool
      {S:  Type}
      {I:  Interface}
      (c:  Contract S I) :=
  { requirements_bool {A:  Type}
    : I A -> S -> bool
  ; promises_bool {A:  Type}
    : I A -> A -> S -> bool
  ; req_propbool :> forall (A:  Type),
      PropBool2 (requirements c (A:=A)) (@requirements_bool A)
  ; prom_propbool :> forall (A:  Type),
      PropBool3 (promises c (A:=A)) (@promises_bool A)
  }.

Arguments requirements_bool [S I] (c) [_ A] (_ _).
Arguments promises_bool [S I] (c) [_ A] (_ _ _).

Inductive InterpreterStep
          (I:  Interface)
  : Type :=
| interpreter_step {A:    Type}
                   (i:    I A)
                   (res:  A)
  : InterpreterStep I.

Arguments interpreter_step [I A] (i res).

Definition step_type
           {I:   Interface}
           (is:  InterpreterStep I)
  : Type :=
  match is with
  | @interpreter_step _ A _ _ => A
  end.

Definition step_instr
           {I:   Interface}
           (is:  InterpreterStep I)
  : I (step_type is) :=
  match is with
  | interpreter_step i _ => i
  end.

Definition step_ret
           {I:   Interface}
           (is:  InterpreterStep I)
  : step_type is :=
  match is with
  | interpreter_step _ x => x
  end.

Definition instruction_picker
           (M:  Type -> Type)
           (I:  Interface) :=
  (forall (A:  Type), I A -> bool) -> M (InterpreterStep I).

Definition test_interpreter_once
           {I:     Interface}
           {S:     Type}
           {M:     Type -> Type}
          `{MonadState M S}
           (pick:  instruction_picker M I)
           (c:     Contract S I)
          `{ContractBool S I c}
  : M (InterpreterStep I * bool) :=
  s    <- get                                                        ;
  is   <- pick (fun {A:  Type} (i: I A) => requirements_bool c i s)  ;
  modify (abstract_step c (step_instr is) (step_ret is))            ;;
  pure (is, promises_bool c (step_instr is) (step_ret is) s).

Fixpoint test_interpreter_aux
         {I:     Interface}
         {S:     Type}
         {M:     Type -> Type}
        `{MonadState M S}
         (pick:  instruction_picker M I)
         (c:     Contract S I)
        `{ContractBool S I c}
         (n: nat)
         (l: list (InterpreterStep I))
  : M (list (InterpreterStep I) * bool) :=
  match n with
  | O
    => pure (l, true)
  | S m
    => res <- test_interpreter_once pick c                           ;
       if (snd res: bool)
       then test_interpreter_aux pick c m (fst res :: l)
       else pure (fst res :: l, false)
  end.

Definition test_interpreter
           {I:     Interface}
           {S:     Type}
           {M:     Type -> Type}
          `{MonadState M S}
           (pick:  instruction_picker M I)
           (c:     Contract S I)
          `{ContractBool S I c}
           (n:     nat)
           (l:     list (InterpreterStep I))
  : M (list (InterpreterStep I) * bool) :=
  test_interpreter_aux pick c n nil.
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

Class InterfaceSelector
      (Archetype:  Type)
      (I:          Interface) :=
  { ret_type  (a: Archetype)
    : Type
  ; at_least_one_primitive (a: Archetype)
    : exists (i: I (ret_type a)), True
  }.

Class RandomGenerator
      (M:  Type -> Type)
      (A:  Type) :=
  { pick: M A
  ; pick_with: (A -> bool) -> M A
  }.

Inductive InterpreterStep
          (I:  Interface)
  : Type :=
| interpreter_step {A:    Type}
                   (i:    I A)
                   (res:  A)
  : InterpreterStep I.

Arguments interpreter_step [I A] (i res).

Definition test_interpreter_once
           {I:          Interface}
           {Archetype:  Type}
           {S:          Type}
           {M:          Type -> Type}
          `{InterfaceSelector Archetype I}
          `{MonadState M S}
          `{MonadInterp I M}
          `{RandomGenerator M Archetype}
          `{forall (a:  Archetype), RandomGenerator M (I (ret_type a))}
           (c:  Contract S I)
          `{ContractBool S I c}
  : M (InterpreterStep I * bool) :=
  s    <- get                                                        ;
  sel  <- pick                                                       ;
  i    <- pick_with (fun (i:  I (ret_type sel))
                     => requirements_bool c i s)                     ;
  x    <- interpret i                                                ;
  modify (abstract_step c i x)                                      ;;
  pure (interpreter_step i x, promises_bool c i x s).

Fixpoint test_interpreter_aux
         {I:          Interface}
         {Archetype:  Type}
         {S:          Type}
         {M:          Type -> Type}
        `{InterfaceSelector Archetype I}
        `{MonadState M S}
        `{MonadInterp I M}
        `{RandomGenerator M Archetype}
        `{forall (a:  Archetype), RandomGenerator M (I (ret_type a))}
         (c:  Contract S I)
        `{ContractBool S I c}
         (n: nat)
         (l: list (InterpreterStep I))
  : M (list (InterpreterStep I) * bool) :=
  match n with
  | O
    => pure (l, true)
  | S m
    => res <- test_interpreter_once c                                ;
       if snd res
       then test_interpreter_aux c m (fst res :: l)
       else pure (fst res :: l, false)
  end.

Definition test_interpreter
           {I:          Interface}
           {Archetype:  Type}
           {S:          Type}
           {M:          Type -> Type}
          `{InterfaceSelector Archetype I}
          `{MonadState M S}
          `{MonadInterp I M}
          `{RandomGenerator M Archetype}
          `{forall (a:  Archetype), RandomGenerator M (I (ret_type a))}
           (c:  Contract S I)
          `{ContractBool S I c}
           (n: nat)
           (l: list (InterpreterStep I))
  : M (list (InterpreterStep I) * bool) :=
  test_interpreter_aux c n nil.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.PropBool.
Require Import FreeSpec.MonadInterp.
Require Import FreeSpec.Control.Classes.

Local Open Scope free_control_scope.

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
  : M bool :=
  s    <- get                                                        ;
  sel  <- pick                                                       ;
  i    <- pick_with (fun (i:  I (ret_type sel))
                     => requirements_bool c i s)                     ;
  x    <- interpret i                                                ;
  modify (abstract_step c i x)                                      ;;
  pure (promises_bool c i x s).
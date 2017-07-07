(** * [Interface] Interpretation

    We consider an [Interface] as a set of _Instructions_. An
    Instruction may take one or more arguments and is associated and,
    once “executed”, returns an element of a given type.

    An [Interface] can easily be defined using a coq inductive
    type. You can have a look at [FreeSpec.Examples] if you want to
    see some simple or more complex examples.

 *)

Definition Interface := Type -> Type.

(** That is, if [I] is an interface, [i : I A] is an instruction which
    returns an element of [A] once interpreted. We define an helper
    function, [typeret], to help Coq in case it struggles with the
    return types. It has been useful for instance to deal with the
    [Contract]s definition.

 *)

Definition typeret
           {I: Interface}
           {A: Type}
           (i: I A)
  : Type := A.
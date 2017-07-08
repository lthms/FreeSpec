(** * Regural [Interface]s

    We consider an [Interface] as a set of _Instructions_. An
    Instruction may take one or more arguments and is associated and,
    once “executed”, returns an element of a given type.

    An [Interface] can easily be defined using a coq inductive
    type. You can have a look at [FreeSpec.Examples] if you want to
    see some simple or more complex examples.

 *)

Definition Interface := Type -> Type.

(** That is, if [I] is an interface, [i : I A] is an instruction which
    returns an element of [A] once interpreted.

    * Labeled [Interface]s

    We can label an interface with a particular type to enrich a
    primitive call with a context. The main idea is this label will be
    stripped before extraction.

 *)

Inductive LabeledInterface
          (I: Interface)
          (L: Type)
  : Interface :=
| labeled_instruction (A: Type)
                      (i: I A)
                      (l: L)
  : LabeledInterface I L A.

Arguments labeled_instruction [I L A] (i l).

Infix "<?>" := LabeledInterface
  (at level 32, no associativity)
  : free_scope.

Infix "<:>" := labeled_instruction
  (at level 32, no associativity)
  : free_scope.
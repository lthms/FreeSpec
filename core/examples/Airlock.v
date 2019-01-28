Require Import Prelude.Control.
Require Import Prelude.Control.Classes.
Require Import Prelude.Control.State.

Require Import FreeSpec.Specification.
Require Import FreeSpec.Abstract.
Require Import FreeSpec.Compose.
Require Import FreeSpec.Semantics.
Require Import FreeSpec.Program.

Local Open Scope prelude_scope.
Local Open Scope free_scope.

Module Door.
  Inductive i
    : Type -> Type :=
    Open
    : i unit
  | Close
    : i unit.

  Inductive w := IsOpen | IsClose.
End Door.

Module Airlock.
  Inductive i
    : Type -> Type :=
  | Open1
    : i unit
  | Open2
    : i unit.

  Notation "'AirlockM' A" :=
    (StateT (bool * bool) (Program (Door.i <+> Door.i)) A)
      (at level 50).

  Definition open_first_door
    : AirlockM unit :=
    lift (singleton (InL Door.Open)).

  Definition close_first_door
    : AirlockM unit :=
    lift (singleton (InL Door.Close)).

  Definition open_second_door
    : AirlockM unit :=
    lift (singleton (InR Door.Open)).

  Definition close_second_door
    : AirlockM unit :=
    lift (singleton (InR Door.Close)).

  Definition first_door_is_open
    : AirlockM bool :=
    fst <$> get.

  Definition second_door_is_open
    : AirlockM bool :=
    snd <$> get.

  Definition update_state_open1
    : AirlockM unit :=
    put (true, false).

  Definition update_state_open2
    : AirlockM unit :=
    put (false, true).

  Definition impl
             {a:    Type}
             (act:  i a)
    : StateT (bool * bool) (Program (Door.i <+> Door.i)) a :=
    match act with
    | Open1
      => d2_open <- second_door_is_open                              ;
         when d2_open close_second_door                             ;;
         open_first_door                                            ;;
         update_state_open1
    | Open2
      => d1_open <- first_door_is_open                               ;
         when d1_open close_first_door                              ;;
         open_second_door                                           ;;
         update_state_open2
    end.

  Definition two_doors_step
             (a:    Type)
             (act:  (Door.i <+> Door.i) a)
             (_:    a)
             (w:    Door.w * Door.w)
    : Door.w * Door.w :=
    match act with
    | InL Door.Open
      => (Door.IsOpen, snd w)
    | InL Door.Close
      => (Door.IsClose, snd w)
    | InR Door.Open
      => (fst w, Door.IsOpen)
    | InR Door.Close
      => (fst w, Door.IsClose)
    end.

  Inductive two_doors_pre
    : forall (a:  Type), (Door.i <+> Door.i) a -> Door.w * Door.w -> Prop :=
  | open_one_two_is_close (f:  Door.w)
    : two_doors_pre unit (InL Door.Open) (f, Door.IsClose)
  | open_two_one_is_close (s:  Door.w)
    : two_doors_pre unit (InR Door.Open) (Door.IsClose, s)
  | always_close_one (s s':  Door.w)
    : two_doors_pre unit (InL Door.Close) (s, s')
  | always_close_two (s s':  Door.w)
    : two_doors_pre unit (InR Door.Close) (s, s').

  Definition two_doors_post
             (a:    Type)
             (act:  (Door.i <+> Door.i) a)
             (x:    a)
             (w:    Door.w * Door.w)
    : Prop :=
    True.

  Definition spec
    : Specification (Door.w * Door.w) (Door.i <+> Door.i) :=
    {| abstract_step := two_doors_step
     ; precondition  := two_doors_pre
     ; postcondition := two_doors_post
    |}.

  Inductive sync_and_sec
    : (bool * bool) -> (Door.w * Door.w) -> Prop :=
  | sync1
    : sync_and_sec (false, false) (Door.IsClose, Door.IsClose)
  | sync2
    : sync_and_sec (true, false) (Door.IsOpen, Door.IsClose)
  | sync3
    : sync_and_sec (false, true) (Door.IsClose, Door.IsOpen).

  Theorem airlock_secure_one_step
    : forall {a:    Type}
             (st:   bool * bool)
             (w:    Door.w * Door.w)
             (act:  i a),
      sync_and_sec st w
      -> impl act st =| spec [w].
  Proof.
    intros a [d1 d2] [w1 w2] act Hsync.
    inversion Hsync;
      induction act;
      repeat constructor.
  Qed.

  Theorem airlock_secure_inv
    : forall {a:    Type}
             (st:   bool * bool)
             (w:    Door.w * Door.w)
             (sem:  Semantics (Door.i <+> Door.i))
             (act:  i a),
      sync_and_sec st w
      -> sem |= spec [w]
      -> sync_and_sec (snd (evalProgram sem (impl act st)))
                      (specification_derive (impl act st) sem spec w).
  Proof.
    intros a [d1 d2] [w1 w2] sem act Hsync Hcomp.
    inversion Hsync;
      induction act;
      repeat constructor.
  Qed.
End Airlock.
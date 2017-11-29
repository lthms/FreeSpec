Require Import FreeSpec.Concurrent.
Require Import FreeSpec.Contract.
Require Import FreeSpec.Control.
Require Import FreeSpec.Control.Classes.
Require Import FreeSpec.Control.State.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Program.
Require Import FreeSpec.Refine.
Require Import FreeSpec.WEq.

Set Implicit Arguments.

Section PROXY.
  Variables (I Ii Io:     Interface)
            (S:           Type)
            (proxy:       StatefulRefinement Ii Io S)
            (to_proxy:    forall (A:  Type), I A -> option (Ii A))
            (from_proxy:  forall (A:  Type), Io A -> I A).

  Definition proxy_aux
             {A:           Type}
             (int:         Interp I)
             (s:           S)
             (i:           I A)
    : (A * S * Interp I) :=
    match to_proxy i with
    | None
      => (evalInstruction int i, s, execInstruction int i)
    | Some i
      => runProgram int (interface_map (proxy i s) from_proxy)
    end.

  CoFixpoint proxify
             (int:  Interp I)
             (s:    S)
    : Interp I :=
    interp (fun (A:  Type)
                (i:  I A)
            => ( fst (fst (proxy_aux int s i))
               , proxify (snd (proxy_aux int s i))
                         (snd (fst (proxy_aux int s i)))
               )
           ).

  Section ABSTRACTSPEC.
    Variables (W:      Type)
              (Wi Wo:  Type)
              (c:      Contract W I)
              (ci:     Contract Wi Ii)
              (co:     Contract Wo Io)
              (fi:     W -> Wi)
              (fo:     W -> Wo)
              (sync:   sync_pred W W S).

    Definition out_req_sync
      : Prop :=
      forall (A:  Type)
             (i:  Io A)
             (w:  W),
        requirements co i (fo w)
        -> requirements c (from_proxy i) w.

    Definition in_req_sync
      : Prop :=
      forall (A:   Type)
             (i:   I A)
             (i':  Ii A)
             (w:   W),
        to_proxy i = Some i'
        -> requirements c i w
        -> requirements ci i' (fi w).

    Definition out_prom_sync
      : Prop :=
      forall (A:  Type)
             (i:  Io A)
             (x:  A)
             (w:  W),
        requirements co i (fo w)
        -> promises c (from_proxy i) x w
        -> promises co i x (fo w).

    Definition in_prom_sync
      : Prop :=
      forall (A:   Type)
             (i:   I A)
             (i':  Ii A)
             (x:   A)
             (w:   W),
        to_proxy i = Some i'
        -> requirements c i w
        -> promises ci i' x (fi w)
        -> promises c i x w.

    Definition in_unproxy_sync
      : Prop :=
      forall (A:   Type)
             (i:   I A)
             (x:   A)
             (w:   W),
        to_proxy i = None
        -> requirements c i w
        -> promises c i x w
        -> fi w = fi (abstract_step c i x w).

    Definition out_unproxy_sync
      : Prop :=
      forall (A:   Type)
             (i:   I A)
             (x:   A)
             (w:   W),
        to_proxy i = None
        -> requirements c i w
        -> promises c i x w
        -> fo w = fo (abstract_step c i x w).

    (** Our goal is to be able to prove something like that:

        Theorem proxy_compliant
                (w:  W)
                (s:  S)
                (int:  Interp I)
                (Hint:  int |= c[w])
          : proxify int s |= c[w].

      By doing that, it become possible to easily adapt a component to
      be used as a proxy. Right now, the best way to do that is to
     *)

  End ABSTRACTSPEC.
End PROXY.
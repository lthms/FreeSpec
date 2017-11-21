Require Import FreeSpec.Control.
Require Import FreeSpec.Program.
Require Import FreeSpec.Interp.
Require Import FreeSpec.Contract.

Ltac next := repeat (try constructor; cbn; trivial).

Ltac destruct_if_when :=
  match goal with
  | [ |- context[when (negb ?B) _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | [ |- context[when ?B _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | [ |- context[if (negb ?B) then _ else _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | [ |- context[if ?B then _ else _]]
    => let eq_cond := fresh "Heq_cond"
       in case_eq B; intros eq_cond; cbn
  | _
    => idtac
  end.

Ltac run_program interp :=
  match goal with
  | [ H : interp |= ?contract [ ?state ] |- context[interpret interp ?instr] ]
    =>  let i := fresh "i" in
        let Hreq_i    := fresh "Hreq_i"    in
        let Hprom_i   := fresh "Hprom_i"   in
        let int       := fresh "int"       in
        let Heq_int   := fresh "Heq_int"   in
        let Henf_int  := fresh "Henf_inf"  in
        let abs       := fresh "abs"       in
        let Heq_abs   := fresh "Heq_abs"   in
        let res       := fresh "res"       in
        let Heq_res   := fresh "Heq_res"   in
        remember (instr) as i;
        cut (requirements contract i state); [
          intro Hreq_i;
          remember (fst (interpret interp i)) as res eqn: Heq_res;
          assert (Hprom_i:  promises contract i res state)
            by (rewrite Heq_res; apply H; exact Hreq_i);
          remember (snd (interpret interp i)) as int eqn: Heq_int;
          remember (abstract_step contract i res state) as abs eqn: Heq_abs;
          assert (Henf_int:  int |= contract [abs])
            by (rewrite Heq_abs;
                rewrite Heq_int;
                apply H;
                exact Hreq_i);
          run_program int
         |]
  | _
    => idtac
  end.

Ltac simplify_promise :=
  match goal with
  | [ Hres:  ?res = fst (interpret _ ?instr) |- _]
    => match goal with
       | [ Hinstr:  instr = _ |- _ ]
         => match goal with
            | [ Hprom:  promises _ instr _ _ |- _ ]
              => rewrite Hinstr in Hprom;
                 cbn in Hprom
            end
       end
  end.

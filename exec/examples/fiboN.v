(* FreeSpec
 * Copyright (C) 2018–2019 ANSSI
 *
 * Contributors:
 * 2019 Thomas Letan <thomas.letan@ssi.gouv.fr>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)

Require Import Coq.Program.Wf.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import FreeSpec.Exec.Interfaces.
Require Import FreeSpec.Exec.Plugin.
Require Import FreeSpec.Program.
Require Import FreeSpec.Compose.
Require Import Prelude.Control.
Require Import Coq.PArith.Pnat.
Require Import Lia.

Local Open Scope prelude_scope.
Local Open Scope char_scope.
Require Import Coq.NArith.NArith.
Local Open Scope N_scope.

Definition ascii_of_nat n :=
  match n mod 10 with
  | 0 =>  "0"
  | 1 =>  "1"
  | 2 =>  "2"
  | 3 =>  "3"
  | 4 =>  "4"
  | 5 =>  "5"
  | 6 =>  "6"
  | 7 =>  "7"
  | 8 =>  "8"
  | _ =>  "9"
  end.

Remark N2nat_inj_lt: forall n m,
    n < m -> (N.to_nat n < N.to_nat m)%nat.
Proof.
  intros n m.
  revert n.
  induction m using N.peano_rec.
  + intros n H.
    now apply N.nlt_0_r in H.
  + induction n using N.peano_rec.
    ++ intro H.
       rewrite N2Nat.inj_succ.
       cbn.
       apply PeanoNat.Nat.lt_0_succ.
    ++ intros H.
       repeat rewrite N2Nat.inj_succ.
       apply Lt.lt_n_S.
       apply IHm.
       now apply N.succ_lt_mono.
Qed.

Program Fixpoint string_of_nat_aux acc n {measure (N.to_nat n)} :=
  match n =? 0 as n in bool with
  | true => acc
  | false => string_of_nat_aux (String (ascii_of_nat (n mod 10)) acc)
                               (n / 10)
  end.
Next Obligation.
  symmetry in Heq_n.
  apply N2nat_inj_lt.
  apply N.div_lt.
  + apply N.eqb_neq in Heq_n.
    now apply N.neq_0_lt_0.
  + repeat constructor.
Defined.

Definition string_of_nat := string_of_nat_aux "".

Definition nat_of_string (s: string) :=
  let fix aux acc s :=
      match s with
      | String "0" rst => aux (10 * acc) rst
      | String "1" rst => aux (1 + 10 * acc) rst
      | String "2" rst => aux (2 + 10 * acc) rst
      | String "3" rst => aux (3 + 10 * acc) rst
      | String "4" rst => aux (4 + 10 * acc) rst
      | String "5" rst => aux (5 + 10 * acc) rst
      | String "6" rst => aux (6 + 10 * acc) rst
      | String "7" rst => aux (7 + 10 * acc) rst
      | String "8" rst => aux (8 + 10 * acc) rst
      | String "9" rst => aux (9 + 10 * acc) rst
      | _ => acc
      end
  in aux 0 s.

Program Fixpoint fibonacci_aux n f {measure (N.to_nat n)} :=
  let update := fun f n x => fun n' => if n =? n' then Some x else f n' in
  match f n with
  | Some x => (x, f)
  | None => match 1 <? n as n with
            | true => let (x, f') := fibonacci_aux (n - 1) f in
                       let (y, f'') := fibonacci_aux (n - 2) f' in
                       (x + y, update f'' n (x + y))
            | false => (1, update f n 1)
            end
  end.
Next Obligation.
  apply N2nat_inj_lt.
  symmetry in Heq_n.
  apply N.ltb_lt in Heq_n.
  lia.
Defined.
Next Obligation.
  apply N2nat_inj_lt.
  symmetry in Heq_n.
  apply N.ltb_lt in Heq_n.
  lia.
Defined.

Definition fibonacci n :=
  fst (fibonacci_aux n (fun _ => None)).

Definition fibo {ix} `{Use Console.i ix} : Program ix unit :=
  Console.echo "Go! ";;
  x <- Console.scan;
  let res := fibonacci (nat_of_string x) in
  Console.echo (string_of_nat res).

Exec fibo.

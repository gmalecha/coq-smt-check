Require Import SMT.Tactic.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Set SMT Solver "z3".
Set SMT Debug.

Goal forall A B : Prop, A /\ B -> B.
Proof.
  intros.
  smt solve.
  tauto.
Qed.

Goal forall A B : Prop, True -> False -> A /\ B.
  intros.
  smt solve calling "z3".
  tauto.
Qed.

Local Open Scope R_scope.

Goal forall x : R, x < 0 -> x + x < x.
Proof.
  intros.
  smt solve.
Abort.

Goal forall x : R, ~(x = -1).
Proof.
  intros.
  Fail smt solve.
Abort.

Goal forall x : R, ~(x = 1).
Proof.
  intros.
  Fail smt solve.
Abort.
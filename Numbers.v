Require Import Nat.

(*
  Datatype for numbers with three constructors:
  - zero
  - n -> 2n + 1
  - n -> 2n + 2

  The point of this representation is uniqueness.
*)
Inductive B : Type :=
| Z : B
| B1 : B -> B
| B2 : B -> B.

Fixpoint to_nat (b : B) : nat :=
  match b with
  | Z => O
  | B1 b => 1 + 2 * to_nat b
  | B2 b => 2 + 2 * to_nat b
  end.

Fixpoint succ (b : B) : B :=
  match b with
  | Z => B1 Z
  | B1 b => B2 b
  (* n = 2m + 2, n + 1 = 2m + 3 = 2(m + 1) + 1 *)
  | B2 b => B1 (succ b)
  end.

Fixpoint from_nat (n : nat) : B :=
  match n with
  | O => Z
  | S n => succ (from_nat n)
  end.

Require Import List.

Import ListNotations.

(*
  Want to prove:
  - to_nat (from_nat n) = n
  - from_nat (to_nat b) = b
*)

Require Import Lia.

Lemma from_nat_succ (n : nat) : from_nat (S n) = succ (from_nat n).
Proof.
  reflexivity.
Qed.

Lemma from_nat_double (n : nat) : succ (from_nat (2 * n)) = B1 (from_nat n).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    replace (n + S (n + 0)) with (S (2 * n)) by lia.
    rewrite from_nat_succ. rewrite IHn.
    reflexivity.
Qed.

Theorem from_nat_to_nat (b : B) : from_nat (to_nat b) = b.
Proof.
  induction b.
  - reflexivity.
  - change (succ (from_nat (2 * to_nat b)) = B1 b).
    rewrite from_nat_double. rewrite IHb. reflexivity.
  - change (succ (succ (from_nat (2 * to_nat b))) = B2 b).
    rewrite from_nat_double. rewrite IHb. reflexivity.
Qed.

Theorem to_nat_lemma (b : B) : to_nat (succ b) = S (to_nat b).
Proof.
  induction b; try reflexivity.
  simpl. rewrite IHb. lia.
Qed.

Theorem to_nat_from_nat (n : nat) : to_nat (from_nat n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite to_nat_lemma. rewrite IHn. reflexivity.
Qed.

(*
  Now I want to define a bunch of more operations, with the hope that they
  would be more efficient than operations on natural numbers.

  double(0) = 0
  double(2n + 1) = 4n + 2 = double(double(n)) + 2
    ^ this equation is not structurally recursive though!
  Maybe I should try to define subtraction by one? The problem is that subtraction
  by one actually needs double as well (to handle the case of 2n+1), and mutually
  recursive definition does not seem to work at all.

  What about the addition, is it going to be cursed as well?

  add(0, b) = b

  add(2n+1, 0) = 2n+1
  add(2n+1, 2m+1) = 2(n + m) + 2
  add(2n+1, 2m+2) = 2(n + m) + 3 -- could be done with succ?

  add(2n+2, 0) = 2n+2
  add(2n+2, 2m+1) = 2(n + m) + 3
  add(2n+2, 2m+2) = 2(n + m) + 4
*)

Fixpoint add (x y : B) : B :=
  match x with
  | Z => y
  | B1 x =>
    match y with
    | Z => B1 x
    | B1 y => B2 (add x y)
    | B2 y => succ (B2 (add x y))
    end
  | B2 x =>
    match y with
    | Z => B2 x
    | B1 y => succ (B2 (add x y))
    | B2 y => succ (succ (B2 (add x y)))
    end
  end.

Theorem add_one (x : B) : add (succ Z) x = succ x.
Proof.
  destruct x; reflexivity.
Qed.

Theorem add_succ (x y : B) : add (succ x) y = succ (add x y).
Proof.
  revert y.
  induction x; intros.
  - rewrite add_one. reflexivity.
  - destruct y; reflexivity.
  - destruct y.
    + reflexivity.
    + simpl. rewrite IHx. reflexivity.
    + simpl. rewrite IHx. reflexivity.
Qed.

Theorem add_correct (x y : B) : to_nat (add x y) = to_nat x + to_nat y.
Proof.
  revert y.
  induction x; intros.
  - reflexivity.
  - destruct y.
    + simpl. lia.
    + simpl. rewrite IHx. lia.
    + simpl. rewrite to_nat_lemma. rewrite IHx. lia.
  - destruct y.
    + simpl. lia.
    + simpl. rewrite to_nat_lemma. rewrite IHx. lia.
    + simpl. rewrite to_nat_lemma. rewrite IHx. lia.
Qed.

Theorem add_correct_simple (x y : nat) : to_nat (add (from_nat x) (from_nat y)) = x + y.
Proof.
  rewrite add_correct.
  repeat (rewrite to_nat_from_nat).
  reflexivity.
Qed.

Definition double (b : B) : B := add b b.

Theorem double_correct (b : B) : to_nat (double b) = 2 * to_nat b.
Proof.
  unfold double.
  rewrite add_correct. lia.
Qed.

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Nat Bool.

Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    eqb (is_even n') false
  end.

Lemma fold_unfold_is_even_0:
  is_even 0 = true.

Proof.
  fold_unfold_tactic is_even.
Qed.

Lemma fold_unfold_is_even_S:
  forall n' : nat,
    is_even (S n') = eqb (is_even n') false.

Proof.
  fold_unfold_tactic is_even.
Qed.

Lemma successor_flips_evenness:
  forall n : nat,
    is_even n = negb (is_even (S n)).

Proof.
  intro n.
  rewrite -> (fold_unfold_is_even_S n).
  destruct (is_even n).

  * simpl.
    reflexivity.

  * simpl.
    reflexivity.
Qed.

(*** https://en.wikipedia.org/wiki/Coq_(software)***)

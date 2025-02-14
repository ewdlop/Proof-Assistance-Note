(* Mathematical Fact: The sum of the first n factorials is always greater than 2^n for n ≥ 4. *)

(* Algorithm: Recursive function to compute the factorial of a number *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

(* Algorithm: Recursive function to compute the sum of the first n factorials *)
Fixpoint sum_of_factorials (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => factorial n + sum_of_factorials n'
  end.

(* Theorem: For n ≥ 4, the sum of the first n factorials is greater than 2^n *)
Require Import Lia.

Theorem sum_of_factorials_greater_than_power_of_two :
  forall n : nat, n >= 4 -> sum_of_factorials n > 2 ^ n.
Proof.
  induction n as [| n' IH].
  - intros H. lia.
  - destruct n'.
    + intros H. lia.
    + destruct n'.
      * intros H. lia.
      * destruct n'.
        -- intros H. lia.
        -- intros H. simpl. 
           assert (factorial (S (S (S (S n')))) >= 2 ^ (S (S (S (S n'))))) by lia.
           specialize (IH (le_n (S (S (S n'))))).
           lia.
Qed.

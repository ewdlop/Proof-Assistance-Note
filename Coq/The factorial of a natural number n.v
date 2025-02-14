(* Mathematical Fact: The factorial of a natural number n (denoted n!) is the product of all positive integers up to n. *)

(* Algorithm: Recursive function to compute the factorial of a number *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

(* Theorem: The factorial of 0 is 1 *)
Theorem factorial_0 : factorial 0 = 1.
Proof.
  simpl. reflexivity.
Qed.

(* Theorem: Factorial is strictly greater than 0 for all n *)
Theorem factorial_positive : forall n : nat, factorial n > 0.
Proof.
  induction n as [| n' IH].
  - simpl. lia.
  - simpl. apply Nat.mul_pos_pos.
    + lia.
    + apply IH.
Qed.

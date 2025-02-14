(* Mathematical Fact: The sum of the first n even numbers is equal to n * (n + 1). *)

(* Algorithm: Recursive function to compute the sum of the first n even numbers *)
Fixpoint sum_of_evens (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => 2 * n + sum_of_evens n'
  end.

(* Theorem: Prove the formula for the sum of the first n even numbers *)
Theorem sum_of_evens_formula :
  forall n : nat, sum_of_evens n = n * (n + 1).
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

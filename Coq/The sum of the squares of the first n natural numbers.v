(* Mathematical Fact: The sum of the squares of the first n natural numbers is given by the formula:
   1^2 + 2^2 + ... + n^2 = n * (n + 1) * (2n + 1) / 6
*)

(* Algorithm: Recursive function to compute the sum of squares of the first n natural numbers *)
Fixpoint sum_of_squares (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n * n + sum_of_squares n'
  end.

(* Theorem: The sum of squares for n = 0 is 0 *)
Theorem sum_of_squares_0 : sum_of_squares 0 = 0.
Proof.
  simpl. reflexivity.
Qed.

(* Theorem: The sum of squares is always greater than or equal to the input number *)
Theorem sum_of_squares_ge_n : forall n : nat, sum_of_squares n >= n.
Proof.
  induction n as [| n' IH].
  - simpl. lia.
  - simpl. nia.
Qed.

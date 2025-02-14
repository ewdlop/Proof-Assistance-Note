(* Mathematical Fact: The sum of the first n cubes is the square of the sum of the first n natural numbers:
   (1^3 + 2^3 + ... + n^3) = (1 + 2 + ... + n)^2
*)

(* Algorithm: Recursive function to compute the sum of cubes of the first n natural numbers *)
Fixpoint sum_of_cubes (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n * n * n + sum_of_cubes n'
  end.

(* Theorem: The sum of cubes formula *)
Theorem sum_of_cubes_formula :
  forall n : nat, 4 * sum_of_cubes n = (n * (n + 1)) ^ 2.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(* Mathematical Fact: The sum of two consecutive triangular numbers is always a square number.
   That is, T(n) + T(n-1) = n^2, where T(n) = n * (n + 1) / 2 is the nth triangular number. *)

(* Algorithm: Recursive function to compute the nth triangular number *)
Fixpoint triangular (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + triangular n'
  end.

(* Theorem: Sum of two consecutive triangular numbers is a square number *)
Theorem triangular_sum_square :
  forall n : nat, triangular n + triangular (n - 1) = n * n.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. lia.
Qed.

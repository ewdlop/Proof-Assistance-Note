(* Mathematical Fact: The nth triangular number is the sum of the first n natural numbers.
   T(n) = n * (n + 1) / 2 *)

(* Algorithm: Recursive function to compute the nth triangular number *)
Fixpoint triangular (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + triangular n'
  end.

(* Theorem: Triangular number formula for n = 0 *)
Theorem triangular_0 : triangular 0 = 0.
Proof.
  simpl. reflexivity.
Qed.

(* Theorem: Triangular number formula for all n *)
Theorem triangular_formula :
  forall n : nat, 2 * triangular n = n * (n + 1).
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. lia.
Qed.

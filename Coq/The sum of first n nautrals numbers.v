(* Mathematical Fact: The sum of the first n natural numbers is given by the formula: n * (n + 1) / 2 *)

Theorem sum_natural_numbers :
  forall n : nat, 2 * (sum_n n) = n * (n + 1).
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. lia.
Qed.

(* Algorithm: Recursive function to compute the sum of the first n natural numbers *)
Fixpoint sum_n (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_n n'
  end.

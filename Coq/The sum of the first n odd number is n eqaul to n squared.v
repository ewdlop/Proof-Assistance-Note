(* Mathematical Fact: For any natural number n, n^2 is equal to the sum of the first n odd numbers:
   n^2 = 1 + 3 + 5 + ... + (2n - 1).
*)

(* Algorithm: Recursive function to compute the sum of the first n odd numbers *)
Fixpoint sum_of_odds (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => (2 * n - 1) + sum_of_odds n'
  end.

(* Theorem: The square of n is equal to the sum of the first n odd numbers *)
Theorem square_sum_of_odds : forall n : nat, n * n = sum_of_odds n.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite <- IH. lia.
Qed.

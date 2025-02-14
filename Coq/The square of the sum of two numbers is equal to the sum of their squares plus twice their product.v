(* Mathematical Fact: The square of the sum of two numbers is equal to the sum of their squares plus twice their product:
   (a + b)^2 = a^2 + 2ab + b^2
*)

(* Algorithm: Function to compute the square of a sum *)
Definition square_of_sum (a b : nat) : nat :=
  (a + b) * (a + b).

(* Theorem: Prove that (a + b)^2 = a^2 + 2ab + b^2 *)
Theorem square_of_sum_expansion :
  forall a b : nat,
    square_of_sum a b = a * a + 2 * a * b + b * b.
Proof.
  intros a b.
  unfold square_of_sum.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_add_distr_r.
  lia.
Qed.

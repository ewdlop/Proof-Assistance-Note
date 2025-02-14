(* Mathematical Fact: The product of any number n and 0 is always 0.
   That is, for any natural number n, n * 0 = 0. *)

(* Algorithm: Recursive function to compute multiplication *)
Fixpoint multiply (a b : nat) : nat :=
  match b with
  | 0 => 0
  | S b' => a + multiply a b'
  end.

(* Theorem: Multiplication by zero results in zero *)
Theorem multiply_by_zero : forall n : nat, multiply n 0 = 0.
Proof.
  intros n. simpl. reflexivity.
Qed.

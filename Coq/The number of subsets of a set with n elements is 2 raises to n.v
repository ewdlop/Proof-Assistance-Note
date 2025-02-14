(* Mathematical Fact: The number of subsets of a set with n elements is 2^n. *)

(* Algorithm: Function to compute 2^n recursively *)
Fixpoint power_of_two (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * power_of_two n'
  end.

(* Theorem: The number of subsets of a set with n elements is 2^n *)
Theorem subsets_count :
  forall n : nat, power_of_two n = 2 ^ n.
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

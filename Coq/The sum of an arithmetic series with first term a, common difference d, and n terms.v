(* Mathematical Fact: The sum of an arithmetic series with first term a, common difference d, and n terms is:
   S_n = (n / 2) * (2a + (n - 1) * d)
*)

(* Algorithm: Function to compute the sum of the first n terms of an arithmetic sequence *)
Fixpoint arithmetic_series (a d n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => (a + n' * d) + arithmetic_series a d n'
  end.

(* Theorem: The sum of the first n natural numbers is n(n+1)/2 (special case with a = 1, d = 1) *)
Theorem sum_of_naturals :
  forall n : nat, 2 * arithmetic_series 1 1 n = n * (n + 1).
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

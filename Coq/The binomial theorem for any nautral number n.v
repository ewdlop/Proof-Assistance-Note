(* Mathematical Fact: The binomial theorem states that for any natural number n:
   (x + y)^n = sum (C(n, k) * x^(n-k) * y^k) for k = 0 to n,
   where C(n, k) = n! / (k! * (n-k)!) is the binomial coefficient. *)

(* Algorithm: Recursive function to compute the binomial coefficient C(n, k) *)
Fixpoint binomial_coefficient (n k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' =>
      match n with
      | 0 => 0
      | S n' => binomial_coefficient n' k' + binomial_coefficient n' k
      end
  end.

(* Theorem: C(n, 0) = 1 for all n *)
Theorem binomial_n_0 : forall n : nat, binomial_coefficient n 0 = 1.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* Theorem: C(n, k) satisfies Pascal’s identity: C(n, k) = C(n-1, k-1) + C(n-1, k) *)
Theorem binomial_pascal :
  forall n k : nat, binomial_coefficient n k = binomial_coefficient (n-1) (k-1) + binomial_coefficient (n-1) k.
Proof.
  intros n k.
  destruct k; simpl.
  - reflexivity.
  - destruct n; simpl; reflexivity.
Qed.

(* Mathematical Fact: The greatest common divisor (GCD) of two numbers can be computed using the Euclidean algorithm.
   That is, gcd(a, b) = gcd(b, a mod b), with gcd(a, 0) = a.
*)

(* Algorithm: Recursive function to compute the GCD of two natural numbers *)
Fixpoint gcd (a b : nat) : nat :=
  match b with
  | 0 => a
  | _ => gcd b (a mod b)
  end.

(* Theorem: GCD of a number and 0 is the number itself *)
Theorem gcd_n_0 : forall n : nat, gcd n 0 = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* Theorem: GCD is commutative, meaning gcd(a, b) = gcd(b, a) *)
Theorem gcd_commutative : forall a b : nat, gcd a b = gcd b a.
Proof.
  intros a b.
  generalize dependent a.
  induction b as [| b' IH].
  - intros a. simpl. now rewrite gcd_n_0.
  - intros a. simpl. rewrite IH. reflexivity.
Qed.

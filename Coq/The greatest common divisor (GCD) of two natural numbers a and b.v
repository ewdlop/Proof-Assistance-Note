(* Mathematical Fact: The greatest common divisor (GCD) of two natural numbers a and b satisfies:
   gcd(a, b) = gcd(b, a mod b), where gcd(a, 0) = a.
*)

(* Algorithm: Recursive function to compute the GCD of two natural numbers *)
Fixpoint gcd (a b : nat) : nat :=
  match b with
  | 0 => a
  | _ => gcd b (a mod b)
  end.

(* Theorem: GCD of a number and 0 is the number itself *)
Theorem gcd_a_0 : forall a : nat, gcd a 0 = a.
Proof.
  intros a.
  simpl. reflexivity.
Qed.

(* Theorem: GCD is symmetric, i.e., gcd(a, b) = gcd(b, a) *)
Theorem gcd_symmetric : forall a b : nat, gcd a b = gcd b a.
Proof.
  intros a b.
  revert a.
  induction b as [| b' IH]; intros a.
  - simpl. now rewrite gcd_a_0.
  - simpl. rewrite IH. reflexivity.
Qed.
s
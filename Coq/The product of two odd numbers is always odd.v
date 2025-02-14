(* Mathematical Fact: The product of two odd numbers is always odd. *)

(* Definition of oddness *)
Definition is_odd (n : nat) : Prop :=
  exists k : nat, n = 2 * k + 1.

(* Algorithm: Function to multiply two natural numbers *)
Definition multiply (a b : nat) : nat := a * b.

(* Theorem: The product of two odd numbers is odd *)
Theorem product_of_two_odds :
  forall a b : nat, is_odd a -> is_odd b -> is_odd (multiply a b).
Proof.
  intros a b [k1 H1] [k2 H2].
  unfold multiply. unfold is_odd.
  exists (2 * k1 * k2 + k1 + k2).
  rewrite H1, H2.
  simpl. lia.
Qed.

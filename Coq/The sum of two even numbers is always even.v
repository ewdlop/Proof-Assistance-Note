(* Mathematical Fact: The sum of two even numbers is always even. *)

(* Definition of evenness *)
Definition is_even (n : nat) : Prop :=
  exists k : nat, n = 2 * k.

(* Algorithm: Function to add two natural numbers *)
Definition add (a b : nat) : nat := a + b.

(* Theorem: The sum of two even numbers is even *)
Theorem sum_of_two_evens :
  forall a b : nat, is_even a -> is_even b -> is_even (add a b).
Proof.
  intros a b [k1 H1] [k2 H2].
  unfold add. unfold is_even.
  exists (k1 + k2).
  rewrite H1, H2.
  simpl. lia.
Qed.

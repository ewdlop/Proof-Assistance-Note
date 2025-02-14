(* Mathematical Fact: A number is even if and only if it is divisible by 2 *)

(* Definition of evenness *)
Definition is_even (n : nat) : Prop :=
  exists k : nat, n = 2 * k.

(* Theorem: 0 is even *)
Theorem zero_is_even : is_even 0.
Proof.
  exists 0. simpl. reflexivity.
Qed.

(* Algorithm: Function to check if a number is even *)
Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => evenb n'
  end.

(* Verification: The evenb function correctly identifies 0 as even *)
Theorem evenb_correct_zero : evenb 0 = true.
Proof.
  simpl. reflexivity.
Qed.

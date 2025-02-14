(* Mathematical Fact: The sum of the digits of a number modulo 9 is congruent to the number itself modulo 9.
   That is, for any natural number n, n ≡ (sum of its digits) (mod 9). *)

Require Import PeanoNat Lia.

(* Algorithm: Function to compute the sum of the digits of a number *)
Fixpoint sum_of_digits (n : nat) : nat :=
  match n with
  | 0 => 0
  | _ => (n mod 10) + sum_of_digits (n / 10)
  end.

(* Theorem: A number is congruent to the sum of its digits modulo 9 *)
Theorem digit_sum_mod_9 :
  forall n : nat, n mod 9 = sum_of_digits n mod 9.
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl.
    replace (n' / 10 * 10 + n' mod 10) with n' by (rewrite Nat.div_mod; lia).
    rewrite Nat.add_mod by lia.
    rewrite IH.
    reflexivity.
Qed.

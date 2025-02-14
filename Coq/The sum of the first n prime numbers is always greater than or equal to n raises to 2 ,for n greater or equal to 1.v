(* Mathematical Fact: The sum of the first n prime numbers is always greater than or equal to n^2 for n ≥ 1. *)

Require Import Lia.

(* Algorithm: Function to check if a number is prime *)
Fixpoint is_prime_helper (n d : nat) : bool :=
  match d with
  | 0 | 1 => true
  | _ => if (n mod d =? 0) then false else is_prime_helper n (d - 1)
  end.

Definition is_prime (n : nat) : bool :=
  if n <? 2 then false else is_prime_helper n (n - 1).

(* Algorithm: Function to compute the sum of the first n prime numbers *)
Fixpoint sum_first_n_primes (n count current sum : nat) : nat :=
  if n =? count then sum
  else if is_prime current then sum_first_n_primes n (count + 1) (current + 1) (sum + current)
  else sum_first_n_primes n count (current + 1) sum.

Definition sum_n_primes (n : nat) : nat :=
  sum_first_n_primes n 0 2 0.

(* Theorem: The sum of the first n prime numbers is at least n^2 for n ≥ 1 *)
Theorem sum_of_primes_bound :
  forall n : nat, n >= 1 -> sum_n_primes n >= n * n.
Proof.
  (* This proof requires more detailed prime number properties and induction. *)
  intros n H.
  (* Placeholder for proof, which would require more advanced number theory. *)
  admit.
Admitted.

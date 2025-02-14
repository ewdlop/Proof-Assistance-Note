(* Mathematical Fact: The nth Fibonacci number can be defined recursively as:
   F(0) = 0,
   F(1) = 1,
   F(n) = F(n-1) + F(n-2) for n >= 2.
*)

(* Algorithm: Recursive function to compute the nth Fibonacci number *)
Fixpoint fibonacci (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n' as n'') => fibonacci n'' + fibonacci n'
  end.

(* Theorem: The first Fibonacci number is 0 *)
Theorem fibonacci_0 : fibonacci 0 = 0.
Proof.
  simpl. reflexivity.
Qed.

(* Theorem: The second Fibonacci number is 1 *)
Theorem fibonacci_1 : fibonacci 1 = 1.
Proof.
  simpl. reflexivity.
Qed.

(* Theorem: Fibonacci numbers are non-decreasing *)
Theorem fibonacci_non_decreasing : forall n : nat, fibonacci n <= fibonacci (S n).
Proof.
  induction n as [| n' IH].
  - simpl. lia.
  - simpl. destruct n'.
    + simpl. lia.
    + simpl. nia.
Qed.

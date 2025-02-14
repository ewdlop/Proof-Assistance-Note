(* Mathematical Fact: The sum of the first n Fibonacci numbers is equal to the (n+2)th Fibonacci number minus 1:
   F(0) + F(1) + ... + F(n) = F(n+2) - 1
*)

(* Algorithm: Recursive function to compute the Fibonacci number *)
Fixpoint fibonacci (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n' as n'') => fibonacci n'' + fibonacci n'
  end.

(* Algorithm: Compute the sum of the first n Fibonacci numbers *)
Fixpoint sum_fibonacci (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => fibonacci n + sum_fibonacci n'
  end.

(* Theorem: Sum of first n Fibonacci numbers follows F(n+2) - 1 formula *)
Theorem sum_fibonacci_formula :
  forall n : nat, sum_fibonacci n = fibonacci (n + 2) - 1.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

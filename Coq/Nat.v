Require Import Arith.
Require Import Nat.

(* Basic Fixpoint Example - Factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => S n * factorial n'
  end.

(* Fixpoint for Addition *)
Fixpoint plus (n m:nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus n' m)
  end.

(* Fixpoint with Multiple Parameters - Power function *)
Fixpoint power (base exp:nat) : nat :=
  match exp with
  | 0 => 1
  | S exp' => base * power base exp'
  end.

(* Fixpoint with Nested Pattern Matching *)
Fixpoint even (n:nat) : bool :=
  match n with
  | 0 => true
  | S n' => odd n'
  end
with odd (n:nat) : bool :=
  match n with
  | 0 => false
  | S n' => even n'
  end.

(* Fixpoint with Structural Recursion - List Length *)
Fixpoint length {A:Type} (l:list A) : nat :=
  match l with
  | nil => 0
  | _ :: l' => S (length l')
  end.

(* Fixpoint with Accumulator - Tail Recursive Factorial *)
Fixpoint factorial_aux (n acc:nat) : nat :=
  match n with
  | 0 => acc
  | S n' => factorial_aux n' (acc * S n')
  end.

Definition factorial_tail n := factorial_aux n 1.

(* Fixpoint for Tree Operations *)
Inductive binary_tree : Type :=
  | Leaf : nat -> binary_tree
  | Node : binary_tree -> binary_tree -> binary_tree.

Fixpoint tree_sum (t:binary_tree) : nat :=
  match t with
  | Leaf n => n
  | Node left right => tree_sum left + tree_sum right
  end.

(* Fixpoint with Custom Type and Multiple Cases *)
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Fixpoint next_workday (d:day) : day :=
  match d with
  | friday => monday
  | saturday => monday
  | sunday => monday
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  end.

(* Fixpoint with Dependent Types *)
Fixpoint vector_length {A:Type} (n:nat) : Type :=
  match n with
  | 0 => unit
  | S n' => A * vector_length n'
  end.

(* Examples of Usage and Proofs *)

(* Proof about factorial *)
Theorem factorial_pos : forall n:nat,
  factorial n > 0.
Proof.
  induction n.
  - simpl. lia.
  - simpl. apply gt_trans with (m:=factorial n).
    + apply Nat.mul_gt_0; [lia | assumption].
    + lia.
Qed.

(* Proof about power *)
Theorem power_0_n : forall n:nat,
  power 0 (S n) = 0.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Fixpoint Termination Example *)
(* This would not be accepted by Coq because recursion is not structural *)
(*
Fixpoint bad_recursion (n:nat) : nat :=
  match n with
  | 0 => 0
  | S n' => bad_recursion (S (S n'))
  end.
*)

(* Mutual Recursion Example *)
Fixpoint is_even (n:nat) : bool :=
  match n with
  | 0 => true
  | S n' => is_odd n'
  end
with is_odd (n:nat) : bool :=
  match n with
  | 0 => false
  | S n' => is_even n'
  end.

(* Proof about mutual recursion *)
Theorem even_odd_complement : forall n:nat,
  is_even n = negb (is_odd n).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. apply negb_involutive.
Qed.

(* Examples Using Fixpoint Functions *)
Example factorial_5 : factorial 5 = 120.
Proof. reflexivity. Qed.

Example power_2_3 : power 2 3 = 8.
Proof. reflexivity. Qed.

Example tree_sum_example :
  tree_sum (Node (Leaf 1) (Node (Leaf 2) (Leaf 3))) = 6.
Proof. reflexivity. Qed.

(* Computing with Fixpoint Functions *)
Compute (factorial 6).        (* = 720 *)
Compute (power 2 4).         (* = 16 *)
Compute (is_even 42).        (* = true *)
Compute (factorial_tail 5).  (* = 120 *)

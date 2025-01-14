Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

(* Example 1: Prove that not all natural numbers are even *)
Definition is_even (n: nat) := exists k, n = 2 * k.

Theorem not_all_numbers_even: 
  ~ (forall n: nat, is_even n).
Proof.
  unfold not.
  intros H.
  (* Use 1 as counterexample *)
  assert (is_even 1) as H1. { apply H. }
  unfold is_even in H1.
  destruct H1 as [k Hk].
  (* Show contradiction *)
  assert (1 = 2 * k) as Contra. { exact Hk. }
  discriminate Contra.
Qed.

(* Example 2: Prove that list reversal is not always identity *)
Theorem reverse_not_identity:
  ~ (forall (A: Type) (l: list A), rev l = l).
Proof.
  unfold not.
  intros H.
  (* Use [1;2] as counterexample *)
  specialize (H nat [1;2]).
  (* Compute both sides *)
  simpl in H.
  (* Show contradiction *)
  discriminate H.
Qed.

(* Example 3: More complex counterexample with custom type *)
Inductive Tree : Type :=
  | Leaf : nat -> Tree
  | Node : Tree -> Tree -> Tree.

Fixpoint tree_size (t: Tree) : nat :=
  match t with
  | Leaf _ => 1
  | Node l r => tree_size l + tree_size r
  end.

Theorem size_not_constant:
  ~ (forall t1 t2: Tree, tree_size t1 = tree_size t2).
Proof.
  unfold not.
  intros H.
  (* Create two different sized trees as counterexample *)
  set (t1 := Leaf 0).
  set (t2 := Node (Leaf 0) (Leaf 1)).
  (* Apply hypothesis *)
  specialize (H t1 t2).
  (* Compute sizes *)
  simpl in H.
  (* Show contradiction *)
  discriminate H.
Qed.

(* Example 4: Disprove a property about sorting *)
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Lt.

Definition is_sorted (l: list nat) := Sorted lt l.

Theorem sorting_not_preserving_length:
  exists l1 l2: list nat,
    is_sorted l1 /\ is_sorted l2 /\ length l1 <> length l2.
Proof.
  exists [1], [1;2].
  split; [|split].
  - constructor; constructor.
  - constructor; constructor; constructor; auto with arith.
  - simpl. discriminate.
Qed.

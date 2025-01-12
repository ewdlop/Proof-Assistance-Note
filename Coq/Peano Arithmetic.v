(* First, let's define natural numbers inductively *)
Inductive nat : Set :=
  | O : nat         (* Zero *)
  | S : nat -> nat. (* Successor function *)

(* Basic recursive definitions for addition *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

(* Multiplication definition *)
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S p => add m (mult p m)
  end.

(* Notation for easier reading *)
Notation "x + y" := (add x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).

(* Some basic properties *)

(* Adding zero on the right *)
Theorem add_O_r : forall n:nat,
  n + O = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Adding successor on the right *)
Theorem add_S_r : forall n m:nat,
  n + (S m) = S (n + m).
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Commutativity of addition *)
Theorem add_comm : forall n m:nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite add_O_r. reflexivity.
  - simpl. rewrite IHn. rewrite add_S_r. reflexivity.
Qed.

(* Associativity of addition *)
Theorem add_assoc : forall n m p:nat,
  (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Multiplication by zero *)
Theorem mult_O_r : forall n:nat,
  n * O = O.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(* Multiplication by successor *)
Theorem mult_S_r : forall n m:nat,
  n * (S m) = n + (n * m).
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn.
    rewrite add_assoc.
    rewrite (add_comm m (n * m)).
    rewrite <- add_assoc.
    reflexivity.
Qed.

(* Distributivity *)
Theorem mult_dist_l : forall n m p:nat,
  n * (m + p) = (n * m) + (n * p).
Proof.
  intros n m p.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn.
    repeat rewrite add_assoc.
    rewrite (add_comm m (n * m)).
    rewrite <- add_assoc.
    rewrite (add_comm p (n * p)).
    reflexivity.
Qed.

(* Commutativity of multiplication *)
Theorem mult_comm : forall n m:nat,
  n * m = m * n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite mult_O_r. reflexivity.
  - simpl. rewrite IHn. rewrite mult_S_r. reflexivity.
Qed.

(* Less than relation *)
Inductive lt : nat -> nat -> Prop :=
  | lt_O : forall n:nat, lt O (S n)
  | lt_S : forall n m:nat, lt n m -> lt (S n) (S m).

Notation "x < y" := (lt x y) (at level 70).

(* Transitivity of less than *)
Theorem lt_trans : forall n m p:nat,
  n < m -> m < p -> n < p.
Proof.
  intros n m p H1 H2.
  induction H2.
  - inversion H1.
    + constructor.
    + apply lt_S. apply IHlt. inversion H1. apply H3.
  - apply lt_S. apply IHH2. apply H1.
Qed.

(* Less than or equal relation *)
Definition le (n m:nat) := n < (S m).
Notation "x <= y" := (le x y) (at level 70).

(* Some properties of inequality *)
Theorem le_n : forall n:nat,
  n <= n.
Proof.
  unfold le.
  induction n.
  - constructor.
  - apply lt_S. apply IHn.
Qed.

(* Strong induction principle *)
Theorem strong_induction :
  forall P : nat -> Prop,
  (forall n : nat, (forall k : nat, k < n -> P k) -> P n) ->
  forall n : nat, P n.
Proof.
  intros P H n.
  assert (forall m, m <= n -> P m).
  { induction n.
    - intros m H1. inversion H1. apply H. intros. inversion H3.
    - intros m H1. apply H. intros k H2.
      apply IHn. unfold le. apply lt_trans with m; assumption. }
  apply H0. apply le_n.
Qed.

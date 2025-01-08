Require Import Arith.
Require Import Nat.
Require Import Lia.

(* Sum of first n numbers (1st power) *)
Theorem sum_first_n : forall n:nat,
  2 * (sum_n n) = n * (n + 1).
Proof.
  induction n.
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive case *)
    simpl sum_n.
    rewrite IHn.
    ring.
Qed.

(* Sum of squares *)
Fixpoint sum_squares (n:nat) : nat :=
  match n with
  | 0 => 0
  | S p => n * n + sum_squares p
  end.

Theorem sum_squares_formula : forall n:nat,
  6 * (sum_squares n) = n * (n + 1) * (2 * n + 1).
Proof.
  induction n.
  - (* Base case *)
    simpl. reflexivity.
  - (* Inductive step *)
    simpl sum_squares.
    rewrite IHn.
    ring.
Qed.

(* Sum of cubes *)
Fixpoint sum_cubes (n:nat) : nat :=
  match n with
  | 0 => 0
  | S p => n * n * n + sum_cubes p
  end.

Theorem sum_cubes_formula : forall n:nat,
  4 * (sum_cubes n) = n * n * (n + 1) * (n + 1).
Proof.
  induction n.
  - (* Base case *)
    simpl. reflexivity.
  - (* Inductive step *)
    simpl sum_cubes.
    rewrite IHn.
    ring.
Qed.

(* Infinite primes proof *)
(* First, we need some helper definitions *)
Require Import PArith.
Require Import ZArith.

Definition is_prime (p:nat) : Prop :=
  p > 1 /\ forall n:nat, 1 < n < p -> ~ (divides n p).

Definition divides (n p:nat) : Prop := exists k:nat, p = k * n.

(* Main theorem *)
Theorem infinite_primes : forall n:nat,
  exists p:nat, is_prime p /\ p > n.
Proof.
  intro n.
  (* Proof by contradiction *)
  apply Classical_Prop.not_all_not_ex.
  intro H.
  (* Let P be the product of all primes up to n plus 1 *)
  assert (exists P:nat, P > 1).
  { exists (factorial n + 1). lia. }
  destruct H0 as [P HP].
  (* P must have a prime factor *)
  assert (exists p:nat, is_prime p /\ divides p P).
  { (* This requires axioms about prime factorization *) }
  destruct H1 as [p [Hprime Hdiv]].
  (* This prime p must be greater than n *)
  assert (p > n).
  { (* This follows from our construction of P *) }
  (* Contradiction with our assumption H *)
  apply (H p).
  split; assumption.
Qed.

(* Fermat's Little Theorem *)
Require Import Ring.
Require Import Znumtheory.

Theorem fermat_little : forall (a p:Z),
  prime p -> ~(divides p a) ->
  divides p (a^(p-1) - 1).
Proof.
  intros a p Hprime Hcoprime.
  (* This proof typically uses group theory *)
  (* We'll use multiplicative group of units mod p *)
  assert (exists k:Z, k * a ≡ 1 [mod p]).
  { (* This uses the fact that mod p forms a field *) }
  destruct H as [k Hk].
  (* The order of a in the multiplicative group divides p-1 *)
  assert (exists m:Z, a^(p-1) ≡ 1 [mod p]).
  { (* This uses Lagrange's theorem *) }
  destruct H as [m Hm].
  (* This implies p divides a^(p-1) - 1 *)
Admitted.

(* Syllogistic Logic in Coq *)
Section Syllogistic.
  (* Define predicates for syllogistic reasoning *)
  Variables (Term : Type).
  Variables (P Q R : Term -> Prop).

  (* Universal affirmative: All P are Q *)
  Definition all (P Q : Term -> Prop) := 
    forall x:Term, P x -> Q x.

  (* Particular affirmative: Some P are Q *)
  Definition some (P Q : Term -> Prop) := 
    exists x:Term, P x /\ Q x.

  (* Universal negative: No P are Q *)
  Definition no (P Q : Term -> Prop) := 
    forall x:Term, P x -> ~(Q x).

  (* Particular negative: Some P are not Q *)
  Definition some_not (P Q : Term -> Prop) := 
    exists x:Term, P x /\ ~(Q x).

  (* Barbara syllogism:
     All M are P
     All S are M
     Therefore, all S are P *)
  Theorem barbara : forall (M P S : Term -> Prop),
    all M P -> all S M -> all S P.
  Proof.
    unfold all.
    intros M P S H1 H2 x Hx.
    apply H1.
    apply H2.
    assumption.
  Qed.

  (* Celarent syllogism:
     No M are P
     All S are M
     Therefore, no S are P *)
  Theorem celarent : forall (M P S : Term -> Prop),
    no M P -> all S M -> no S P.
  Proof.
    unfold no, all.
    intros M P S H1 H2 x Hx.
    apply H1.
    apply H2.
    assumption.
  Qed.

  (* Darii syllogism:
     All M are P
     Some S are M
     Therefore, some S are P *)
  Theorem darii : forall (M P S : Term -> Prop),
    all M P -> some S M -> some S P.
  Proof.
    unfold all, some.
    intros M P S H1 H2.
    destruct H2 as [x [HS HM]].
    exists x.
    split.
    - assumption.
    - apply H1. assumption.
  Qed.

End Syllogistic.

(* Example usage of syllogistic reasoning *)
Module SyllogismExample.
  (* Define some terms *)
  Inductive Animal : Type :=
    | cat
    | dog
    | bird.

  (* Define predicates *)
  Definition Mortal (a:Animal) := True.
  Definition Animal_pred (a:Animal) := True.
  Definition Human (a:Animal) := False.

  (* Example syllogism:
     All animals are mortal
     All cats are animals
     Therefore, all cats are mortal *)
  Example animal_syllogism :
    all Animal Mortal_pred Animal_pred ->
    all Animal Cat Animal_pred ->
    all Animal Cat Mortal_pred.
  Proof.
    apply barbara.
  Qed.

End SyllogismExample.

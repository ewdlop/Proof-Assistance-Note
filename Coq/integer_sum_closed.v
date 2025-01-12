Require Import ZArith.
Open Scope Z_scope.

(* First let's state our theorem *)
Theorem integer_sum_closed: forall n m : Z,
  exists o : Z, n + m = o.

Proof.
  (* Take any two integers n and m *)
  intros n m.
  
  (* We can directly show that their sum exists as an integer *)
  exists (n + m).
  
  (* The proof is trivial by reflexivity *)
  reflexivity.
Qed.

(* Let's also prove some specific examples *)
Example sum_specific: exists o : Z,
  5 + 3 = o.
Proof.
  exists 8.
  reflexivity.
Qed.

Example sum_with_negative: exists o : Z,
  5 + (-3) = o.
Proof.
  exists 2.
  reflexivity.
Qed.

(* Let's prove that integer addition is commutative *)
Theorem integer_sum_commutative: forall n m : Z,
  n + m = m + n.
Proof.
  intros n m.
  ring.
Qed.

(* Let's prove that integer addition is associative *)
Theorem integer_sum_associative: forall n m p : Z,
  (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  ring.
Qed.

(* Proof that adding 0 doesn't change the number *)
Theorem add_zero_identity: forall n : Z,
  n + 0 = n.
Proof.
  intro n.
  ring.
Qed.

(* Every integer has an additive inverse *)
Theorem additive_inverse: forall n : Z,
  exists m : Z, n + m = 0.
Proof.
  intro n.
  exists (-n).
  ring.
Qed.

(* The sum of any integer with itself is even *)
Theorem sum_with_self_even: forall n : Z,
  exists k : Z, n + n = 2 * k.
Proof.
  intro n.
  exists n.
  ring.
Qed.

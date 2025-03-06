(* This file proves a handful simple lemmas about transpositions and
   permutations. Specifically finite(ly supported) permutations, that
   is invertible functions from `nat` to `nat`, which fix all but a
   finite number of elements. These permutations can be decomposed in
   a finite number of transpositions.

   We use permutations to rename holes, inspired by nominal techniques
   (as in Andrew Pitt's nominal sets). Our early attempts at renaming
   weren't bijective, and the proofs were much harder. This is largely
   because we use actual functions to represent contexts (see
   `Finitely.v`, see also lemmas such as `pre_cshift_surjective` in
   `Lemmas.v`).

   There's nothing special about `nat` in this file, it was just
   simpler to commit to a concrete type than to abstract over it.  *)

Require Import Arith.
Require Import List.
From Hammer Require Import Tactics.

Module Transposition.

  Record T := {
      from : nat;
      to : nat }.

  Definition sem (t : T) : nat -> nat :=
    fun n => if Nat.eq_dec n t.(from)
          then t.(to)
          else if Nat.eq_dec n t.(to)
               then t.(from)
               else n
  .

  Notation "⟦ t ⟧" := (sem t).

  Lemma inverse : forall (t : T) n, ⟦t⟧ (⟦t⟧ n) = n.
  Proof.
    intros *. unfold sem.
    hauto q: on.
  Qed.

End Transposition.

Definition T := list Transposition.T.

Definition sem (p : T) : nat -> nat :=
  fun n => List.fold_right Transposition.sem n p
.

Notation "⟦ t ⟧" := (sem t).

Lemma sem_cons : forall t p n, ⟦t::p⟧ n = Transposition.sem t (⟦p⟧ n).
Proof.
  reflexivity.
Qed.

Lemma sem_snoc : forall t p n, ⟦p++(t::nil)⟧ n = ⟦p⟧ (Transposition.sem t n).
Proof.
  intros *. unfold sem.
  rewrite List.fold_right_app. cbn.
  reflexivity.
Qed.

Lemma pre_inverse : forall (p : T) n, ⟦p⟧ (⟦List.rev p⟧ n) = n.
Proof.
  induction p as [| t p h].
  { reflexivity. }
  intros n. simpl.
  rewrite sem_snoc.
  rewrite h.
  apply Transposition.inverse.
Qed.

Lemma post_inverse : forall (p : T) n, ⟦List.rev p⟧ (⟦p⟧ n) = n.
Proof.
  induction p as [| t p h].
  { reflexivity. }
  intros n. simpl.
  rewrite sem_snoc.
  rewrite Transposition.inverse.
  trivial.
Qed.

Lemma eqn_inverse : forall (p : T) n m, ⟦List.rev p⟧  n = m <-> n = ⟦p⟧ m.
Proof.
  intros *.
  sfirstorder use: pre_inverse, post_inverse.
Qed.

Lemma eqn_inverse' : forall (p : T) n m, ⟦p⟧  n = m <-> n = ⟦List.rev p⟧ m.
Proof.
  intros.
  hauto q: on use: eqn_inverse.
Qed.

Corollary surjective : forall p n, exists m, ⟦p⟧ m = n.
Proof.
  intros *.
  exists (⟦List.rev p⟧ n).
  apply pre_inverse.
Qed.

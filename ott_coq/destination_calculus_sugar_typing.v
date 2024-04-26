Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.destination_calculus_notations.
Require Import Dest.ext_nat.
Require Import Coq.Program.Equality.
Require Import Dest.Finitely.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
(* ⬇️ for the `impl` relation. *)
Require Coq.Program.Basics.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.Plus.
Require Import Arith.
Require Import Dest.destination_calculus_proofs.

Theorem Ty_termS_Alloc : forall (P : ctx) (T : type), DisposableOnly P -> P ⊢ alloc : T ⧔ (⌊ T ⌋ ¹ν).
Proof.
  intros P T DisposP.
  unfold termS_Alloc.
  rewrite union_empty_r_eq with (G := P).
  apply Ty_term_Val.
  - assumption.
  - rewrite union_empty_r_eq with (G := ᴳ{}).
    assert (hvarsᴳ(ᴳ- ᴳ{+ 1 : ¹ν ⌊ T ⌋ ¹ν }) = ᴴ{ 1}) as hvarsD3Eq.
      { rewrite hvars_minus_eq. unfold hvars_ctx, hvars_dom, ctx_singleton, hminus. rewrite dom_singleton_eq. cbn. reflexivity. }
    rewrite <- hvarsD3Eq. apply TyR_val_A; swap 1 10; swap 2 11.
    + rewrite stimes_empty_eq, <- union_empty_l_eq. apply TyR_val_D.
    + rewrite <- union_empty_l_eq. rewrite hminus_singleton. apply TyR_val_H.
    + apply DestOnly_singleton_dest.
    + apply LinOnly_singleton_iff. cbn. constructor.
    + apply FinAgeOnly_singleton_iff. cbn. constructor.
    + apply ValidOnly_singleton_iff. cbn. constructor.
    + apply Disjoint_empty_l.
    + apply Disjoint_empty_l.
    + apply Disjoint_empty_l.
    + apply DestOnly_empty.
    + apply DestOnly_empty.
  - + apply DestOnly_empty.
Qed.

Theorem Ty_termS_FromA' : forall (P : ctx) (t : term) (T : type), P ⊢ t : T ⧔ ① -> P ⊢ from⧔' t : T.
Proof.
  intros * Tyt.
  unfold termS_FromA'.
  replace P with (¹ν ᴳ· P ᴳ+ ᴳ{}). 2:{ crush. }
  apply Ty_term_PatP with (T1 := T) (T2 := ! ¹∞ ⁔ ①).
  - constructor.
  - apply Disjoint_empty_l.
  - apply Disjoint_empty_l.
  - apply Disjoint_singletons_iff. sfirstorder.
  - apply Ty_term_FromA.
    replace P with (P ᴳ+ ᴳ{}). 2:{ crush. }
    apply Ty_term_Map with (T := ①).
    + apply Disjoint_empty_l.
    + assumption.
    + rewrite stimes_empty_eq, union_commutative. apply Ty_term_PatU.
      * rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ①}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
      * rewrite union_empty_l_eq with (G := ᴳ{}). apply Ty_term_Val. { apply DisposableOnly_empty. } { rewrite <- stimes_empty_eq with (m := ¹∞). apply TyR_val_E. apply TyR_val_U. repeat constructor. } { apply DestOnly_empty. }
  - replace (ᴳ{} ᴳ+ ᴳ{ 1 : ¹ν ‗ T} ᴳ+ ᴳ{ 2 : ¹ν ‗ ! ¹∞ ⁔ ①}) with (¹ν ᴳ· ᴳ{ 2 : ¹ν ‗ ! ¹∞ ⁔ ①} ᴳ+ ᴳ{ 1 : ¹ν ‗ T}). 2:{ crush. }
    apply Ty_term_PatE with (T := ①).
    + repeat constructor.
    + repeat constructor.
    + apply Disjoint_singletons_iff. sfirstorder.
    + rewrite union_empty_l_eq with (G := ᴳ{ 2 : ¹ν ‗ ! ¹∞ ⁔ ①}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
    + rewrite union_commutative. apply Ty_term_PatU.
      * cbn. rewrite union_empty_l_eq at 1. apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
      * rewrite union_empty_l_eq with (G := ᴳ{ 1 : ¹ν ‗ T}). apply Ty_term_Var. { apply DisposableOnly_empty. }  { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

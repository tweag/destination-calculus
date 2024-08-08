Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.Notations.
Require Import Dest.Lemmas.
Require Import Dest.ExtNat.
Require Import Coq.Program.Equality.
Require Import Dest.Finitely.
Require Import Dest.TermSubSpec1.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
(* ⬇️ for the `impl` relation. *)
Require Coq.Program.Basics.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Compare_dec.
Require Import Arith.
Require Import Lia.

Lemma term_sub_spec_2 :
  forall (D11 D12 D2 : ctx) (m' : mode) (T1' T2' U' : type) (te : term) (x1' x2' : var) (v1' v2' : val),
  IsValid m' ->
  DestOnly D11 ->
  DestOnly D12 ->
  DestOnly D2 ->
  LinOnly (m' ᴳ· (D11 ᴳ+ D12) ᴳ+ D2) ->
  FinAgeOnly (m' ᴳ· (D11 ᴳ+ D12) ᴳ+ D2) ->
  D2 # ᴳ{ x1' : m' ‗ T1'} ->
  D2 # ᴳ{ x2' : m' ‗ T2'} ->
  (ᴳ{ x1' : m' ‗ T1'} # ᴳ{ x2' : m' ‗ T2'}) ->
  (D2 ᴳ+ ᴳ{ x1' : m' ‗ T1'} ᴳ+ ᴳ{ x2' : m' ‗ T2'} ⊢ te : U') ->
  (D11 ⊢ ᵥ₎ v1' : T1') ->
  (D12 ⊢ ᵥ₎ v2' : T2') ->
  (m' ᴳ· (D11 ᴳ+ D12) ᴳ+ D2 ⊢ te ᵗ[ x1' ≔ v1' ] ᵗ[ x2' ≔ v2' ] : U').
Proof.
  intros * Validm DestOnlyD11 DestOnlyD12 DestOnlyD2 LinOnlyD FinAgeOnlyD DisjointD2x1 DisjointD2x2 Disjointx1x2 Tyte Tyv1 Tyv2.
  pose proof LinOnlyD as ValidOnlyD. apply LinOnly_wk_ValidOnly in ValidOnlyD.
  rewrite stimes_distrib_on_union. rewrite union_swap_1_2_l3. rewrite <- union_associative. rewrite union_commutative.
  apply term_sub_spec_1' with (Tv' := T2'); trivial. crush.
  apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD & _ & _). rewrite stimes_distrib_on_union in LinOnlyD. apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (_ & Lin & _). assumption.
  apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD & _). rewrite stimes_distrib_on_union in FinAgeOnlyD. apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (_ & FinAge). assumption.
  apply ValidOnly_union_backward in ValidOnlyD. destruct ValidOnlyD as (ValidOnlyD & _). rewrite stimes_distrib_on_union in ValidOnlyD. apply ValidOnly_union_backward in ValidOnlyD. apply ValidOnly_union_forward. destruct ValidOnlyD as (ValidOnlyD & _). assumption. apply LinOnly_wk_ValidOnly in LinOnlyD. crush. crush.
  apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative; crush. apply Disjoint_union_l_iff; split. apply DestOnly_Disjoint_singleton_var. crush. crush.
  rewrite <- union_associative, union_commutative.
  apply term_sub_spec_1' with (Tv' := T1'); trivial. crush.
  apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD & _ & _). rewrite stimes_distrib_on_union in LinOnlyD. apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (Lin & _ & _). assumption.
  apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD & _). rewrite stimes_distrib_on_union in FinAgeOnlyD. apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD & _). assumption.
  apply ValidOnly_union_forward. crush. apply ValidOnly_singleton_iff. simpl. assumption. apply DestOnly_Disjoint_singleton_var; assumption.
  apply Disjoint_union_l_iff; split. apply Disjoint_commutative; crush. apply Disjoint_commutative, DestOnly_Disjoint_singleton_var. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative; crush.
  rewrite union_swap_2_3_l3. assumption.
Qed.

(* ========================================================================= *)

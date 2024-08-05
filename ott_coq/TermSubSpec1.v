Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.Notations.
Require Import Dest.Lemmas.
Require Import Dest.ExtNat.
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
Require Import Coq.Arith.Compare_dec.
Require Import Arith.
Require Import Lia.

Lemma term_sub_spec_1 :
  forall (D1 D2 : ctx) (m' : mode) (T' U' : type) (te : term) (x' : var) (v' : val),
  IsValid m' ->
  DestOnly D1 ->
  DestOnly D2 ->
  LinOnly (m' ᴳ· D1 ᴳ+ D2) ->
  FinAgeOnly (m' ᴳ· D1 ᴳ+ D2) ->
  (D2 ᴳ+ ᴳ{ x' : m' ‗ T'} ⊢ te : U') ->
  (D1 ⊢ ᵥ₎ v' : T') ->
  (m' ᴳ· D1 ᴳ+ D2 ⊢ te ᵗ[ x' ≔ v'] : U').
Proof.
  intros * Validmp DestOnlyD1 DestOnlyD2 LinOnlyD FinAgeOnlyD Tyte Tyvp.
  dependent induction Tyte; simpl.
  - rename x into Hu.
    assert (P ᴳ+ D = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
    assert (P = ᴳ{ x' : m' ‗ T'} /\ D = D2) as UnionEqSplit.
      { rewrite union_commutative with (G1 := D2) in UnionEq.
        apply ctx_split_DestOnly_VarOnly. (* any dest in P must have multiplicity omega, but cannot be either in singl {x : ...} (no dest) or D2 (LinOnly) *) admit. apply VarOnly_singleton_var. all:assumption.
      } destruct UnionEqSplit; subst.
    assert (ᴳ{ x' : m' ‗ T'} (ˣ x') = Some (ₓ m' ‗ T')) as mapstoSing.
      { unfold ctx_singleton. apply (@singleton_MapsTo_at_elt name binding_type_of). }
    assert (IsUr m'). { unfold DisposableOnly in DisposP. specialize (DisposP (ˣ x') (ₓ m' ‗ T') mapstoSing). simpl in DisposP. assumption. }
    assert (D1 = ᴳ{}). { assert (LinOnly (m' ᴳ· D1)) as LinOnlymD1. { crush. } destruct (LinOnly_stimes_dec D1 m' Validmp LinOnlymD1). inversion H0. inversion i. congruence. destruct a. assumption. }
    rewrite H1 in *. rewrite stimes_empty_eq. rewrite <- union_empty_l_eq. term_Val_no_dispose D2.
  - rename x into Hu, x0 into x.
    assert (P ᴳ+ (ᴳ{ x : m ‗ T}) = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
    assert (VarOnly (P ᴳ+ ᴳ{ x : m ‗ T})).
      { apply VarOnly_union_iff. split. (* any dest in P must have multiplicity omega, but cannot be either in singl {x : ...} (no dest) or D2 (LinOnly) *) admit. apply VarOnly_singleton_var. }
    rewrite union_empty_r_eq with (G := P ᴳ+ ᴳ{ x : m ‗ T}) in UnionEq.
    rewrite union_commutative with (G1 := D2) in UnionEq.
    apply ctx_split_DestOnly_VarOnly in UnionEq; swap 1 5. assumption. assumption. apply VarOnly_singleton_var. apply DestOnly_empty.
    destruct UnionEq; subst. rewrite <- union_empty_r_eq in *.
    pose proof DisjointPx as DisjointPx'.
    apply nIn_iff_Disjoint_singleton in DisjointPx'.
    destruct (HNamesFacts.eq_dec x x').
    * subst. assert ((P ᴳ+ ᴳ{ x' : m ‗ T}) (ˣ x') = ᴳ{ x' : m' ‗ T'} (ˣ x')). { rewrite H0. reflexivity. }
      assert (ₓ m ‗ T = ₓ m' ‗ T'). { unfold union, ctx_singleton in H1. rewrite (@merge_with_None_Some_eq name binding_type_of) with (x := (ˣ x')) (y2 := (ₓ m ‗ T)) in H1. rewrite singleton_MapsTo_at_elt in H1. inversion H1. constructor. split.
        unfold Disjoint in DisjointPx. specialize (DisjointPx (ˣ x')). destruct (In_dec (ˣ x') P). assert (In (ˣ x') ᴳ{ x' : m ‗ T}). { unfold ctx_singleton. apply In_singleton_iff. reflexivity. } specialize (DisjointPx H2 H3). contradiction. apply nIn_iff_nMapsTo. assumption. apply singleton_MapsTo_at_elt.
      } inversion H2. subst. destruct (LinOnly_stimes_dec D1 m' Validmp LinOnlyD), (FinAgeOnly_stimes_dec D1 m' Validmp FinAgeOnlyD).
      + inversion i. inversion i0. inversion Subtypem; subst. congruence. inversion H8; inversion H9; subst. rewrite <- H7. rewrite <- stimes_linnu_eq. assumption. congruence. congruence. congruence.
      + rewrite e in *. rewrite stimes_empty_eq. assumption.
      + destruct a. rewrite H4 in *. rewrite stimes_empty_eq. assumption.
      + rewrite e in *. rewrite stimes_empty_eq. assumption.
    * assert (In (ˣ x) (P ᴳ+ ᴳ{ x : m ‗ T})). { apply In_union_forward_r. apply In_singleton_iff. reflexivity. } rewrite H0 in H1. apply In_singleton_iff in H1. inversion H1. congruence.
  - rename x into Hu.
    assert (m ᴳ· P1 ᴳ+ P2 = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
    pose proof UnionEq as UnionEq'. apply ctx_split_dec_bound_var in UnionEq'. 2:{ crush. } 2:{ crush. } destruct UnionEq' as [[in_both | in_left_only] | in_right_only].
    + destruct in_both as (D1' & D2' & m1 & m2 & mP1eq & DestOnlyD1p & P2eq & DestOnlyD2p & meq).
      apply ctx_split_union_singl_stimes_inv in mP1eq. 2:{ assumption. } destruct mP1eq as (m1' & m1eq & D1'' & P1eq & DestOnlyD1pp).
      pose proof Validmp as Validmp'. rewrite <- meq in Validmp'. apply IsValid_plus_backward in Validmp'. destruct Validmp' as (Validm1 & Validm2). pose proof Validm1 as Validm1'. rewrite <- m1eq in Validm1'. apply IsValid_times_backward in Validm1'. destruct Validm1' as (_ & Validm1').
      subst.
      assert (m ᴳ· D1'' ᴳ+ D2' = D2). { apply remove_singletons_in_union_eq_stimes_l in UnionEq; assumption. } rewrite <- H in *.
      assert (LinOnly (m1' ᴳ· D1 ᴳ+ D1'')). { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). apply LinOnly_stimes_plus_backward in LinOnlyD1. destruct LinOnlyD1 as (LinOnlyD1 & _). apply LinOnly_union_iff in LinOnlyD1ppD2p. destruct LinOnlyD1ppD2p as (LinOnlyD1pp & _ & _). apply LinOnly_stimes_backward in LinOnlyD1pp. apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m1' ᴳ· D1 ᴳ+ D1'')). { apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2p). apply FinAgeOnly_stimes_plus_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (FinAgeOnlyD1 & _). apply FinAgeOnly_union_backward in FinAgeOnlyD1ppD2p. destruct FinAgeOnlyD1ppD2p as (FinAgeOnlyD1pp & _). apply FinAgeOnly_stimes_backward in FinAgeOnlyD1pp. apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD); crush. }
      specialize (IHTyte1 DestOnlyD1 x' T' m1' Validm1' D1'' DestOnlyD1pp H0 H1 eq_refl Tyvp).
      assert (LinOnly (m2 ᴳ· D1 ᴳ+ D2')). {
        apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). apply LinOnly_stimes_plus_backward in LinOnlyD1. destruct LinOnlyD1 as (_ & LinOnlyD1). apply LinOnly_union_iff in LinOnlyD1ppD2p. destruct LinOnlyD1ppD2p as (LinOnlyD1pp & LinOnlyD2p & DisjointD1ppD2p). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m2 ᴳ· D1 ᴳ+ D2')). {
        apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2p). apply FinAgeOnly_stimes_plus_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (_ & FinAgeOnlyD1). apply FinAgeOnly_union_backward in FinAgeOnlyD1ppD2p. destruct FinAgeOnlyD1ppD2p as (FinAgeOnlyD1pp & FinAgeOnlyD2p). apply FinAgeOnly_stimes_backward in FinAgeOnlyD1pp. apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD); crush. }
      specialize (IHTyte2 DestOnlyD1 x' T' m2 Validm2 D2' DestOnlyD2p H2 H3 eq_refl Tyvp).
      rewrite <- union_self_stimes_plus_eq.
      replace (m · m1' ᴳ· D1 ᴳ+ m2 ᴳ· D1 ᴳ+ (m ᴳ· D1'' ᴳ+ D2')) with (m ᴳ· (m1' ᴳ· D1 ᴳ+ D1'') ᴳ+ (m2 ᴳ· D1 ᴳ+ D2')).
      apply Ty_term_App with (T := T) (P1 := m1' ᴳ· D1 ᴳ+ D1'') (P2 := m2 ᴳ· D1 ᴳ+ D2'); trivial.
      rewrite stimes_distrib_on_union. rewrite <- union_associative. rewrite union_associative with (G1 := m ᴳ· D1''). rewrite union_commutative with (G1 := m ᴳ· D1''). crush.
    + destruct in_left_only as (D1' & mP1eq & DestOnlyD1p & DestOnlyP2).
      apply ctx_split_union_singl_stimes_inv in mP1eq. 2:{ assumption. } destruct mP1eq as (m1 & m1eq & D1'' & P1eq & DestOnlyD1pp).
      pose proof Validmp as Validmp'. rewrite <- m1eq in Validmp'. apply IsValid_times_backward in Validmp'. destruct Validmp' as (_ & Validm1).
      subst.
      assert (m ᴳ· D1'' ᴳ+ P2 = D2). { apply remove_singletons_in_union_eq_stimes_l_varonly_l in UnionEq; assumption. } rewrite <- H in *.
      assert (LinOnly (m1 ᴳ· D1 ᴳ+ D1'')). { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2 & DisjointD). apply LinOnly_stimes_times_backward in LinOnlyD1. destruct LinOnlyD1 as (_ & LinOnlyD1). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m1 ᴳ· D1 ᴳ+ D1'')). { apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2). apply FinAgeOnly_stimes_times_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (_ & FinAgeOnlyD1). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2 & DisjointD); crush. }
      specialize (IHTyte1 DestOnlyD1 x' T' m1 Validm1 D1'' DestOnlyD1pp H0 H1 eq_refl Tyvp).
      assert (t' ᵗ[ x' ≔ v'] = t'). { apply term_sub_nIn_no_effect with (P := P2) (T := T ⁔ m → U). { apply nIn_iff_nMapsTo. apply DestOnly_nMapsTo_var. assumption. } { assumption. } }
      rewrite H2 in *.
      rewrite union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
      apply Ty_term_App with (T := T) (P1 := m1 ᴳ· D1 ᴳ+ D1'') (P2 := P2); trivial.
    + destruct in_right_only as (D2' & DestOnlyP1 & mP2eq & DestOnlyD2p).
      subst.
      assert (m ᴳ· P1 ᴳ+ D2' = D2). { apply remove_singletons_in_union_eq_stimes_l_varonly_r in UnionEq; crush. } rewrite <- H in *.
      assert (LinOnly (m' ᴳ· D1 ᴳ+ D2')). { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyP1D2p & DisjointD). apply LinOnly_union_iff in LinOnlyP1D2p. destruct LinOnlyP1D2p as (_ & LinOnlyD2p & _). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m' ᴳ· D1 ᴳ+ D2')). { apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyP1D2p). apply FinAgeOnly_union_backward in FinAgeOnlyP1D2p. destruct FinAgeOnlyP1D2p as (_ & FinAgeOnlyD2p). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyP1D2p & DisjointD); crush. }
      specialize (IHTyte2 DestOnlyD1 x' T' m' Validmp D2' DestOnlyD2p H0 H1 eq_refl Tyvp).
      assert (t ᵗ[ x' ≔ v'] = t). { apply term_sub_nIn_no_effect with (P := P1) (T := T). { apply nIn_iff_nMapsTo. apply DestOnly_nMapsTo_var. crush. } { assumption. } }
      rewrite H2 in *.
      replace (m' ᴳ· D1 ᴳ+ (m ᴳ· P1 ᴳ+ D2')) with (m ᴳ· P1 ᴳ+ (m' ᴳ· D1 ᴳ+ D2')).
      apply Ty_term_App with (T := T) (P1 := P1) (P2 := m' ᴳ· D1 ᴳ+ D2'); trivial.
      rewrite union_commutative. rewrite <- union_associative. rewrite union_commutative with (G1 := D2'). reflexivity.
    - rename x into Hu.
    assert (P1 ᴳ+ P2 = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
    pose proof UnionEq as UnionEq'. apply ctx_split_dec_bound_var in UnionEq'. 2:{ crush. } 2:{ crush. } destruct UnionEq' as [[in_both | in_left_only] | in_right_only].
    + destruct in_both as (D1' & D2' & m1 & m2 & mP1eq & DestOnlyD1p & P2eq & DestOnlyD2p & meq).
      pose proof Validmp as Validmp'. rewrite <- meq in Validmp'. apply IsValid_plus_backward in Validmp'. destruct Validmp' as (Validm1 & Validm2).
      subst.
      assert (D1' ᴳ+ D2' = D2). { apply remove_singletons_in_union_eq in UnionEq; assumption. } rewrite <- H in *.
      assert (LinOnly (m1 ᴳ· D1 ᴳ+ D1')). { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). apply LinOnly_stimes_plus_backward in LinOnlyD1. destruct LinOnlyD1 as (LinOnlyD1 & _). apply LinOnly_union_iff in LinOnlyD1ppD2p. destruct LinOnlyD1ppD2p as (LinOnlyD1pp & _ & _). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m1 ᴳ· D1 ᴳ+ D1')). { apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2p). apply FinAgeOnly_stimes_plus_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (FinAgeOnlyD1 & _). apply FinAgeOnly_union_backward in FinAgeOnlyD1ppD2p. destruct FinAgeOnlyD1ppD2p as (FinAgeOnlyD1pp & _). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD); crush. }
      specialize (IHTyte1 DestOnlyD1 x' T' m1 Validm1 D1' DestOnlyD1p H0 H1 eq_refl Tyvp).
      assert (LinOnly (m2 ᴳ· D1 ᴳ+ D2')). {
        apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). apply LinOnly_stimes_plus_backward in LinOnlyD1. destruct LinOnlyD1 as (_ & LinOnlyD1). apply LinOnly_union_iff in LinOnlyD1ppD2p. destruct LinOnlyD1ppD2p as (LinOnlyD1pp & LinOnlyD2p & DisjointD1ppD2p). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m2 ᴳ· D1 ᴳ+ D2')). {
        apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2p). apply FinAgeOnly_stimes_plus_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (_ & FinAgeOnlyD1). apply FinAgeOnly_union_backward in FinAgeOnlyD1ppD2p. destruct FinAgeOnlyD1ppD2p as (FinAgeOnlyD1pp & FinAgeOnlyD2p). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD); crush. }
      specialize (IHTyte2 DestOnlyD1 x' T' m2 Validm2 D2' DestOnlyD2p H2 H3 eq_refl Tyvp).
      rewrite <- union_self_stimes_plus_eq.
      replace (m1 ᴳ· D1 ᴳ+ m2 ᴳ· D1 ᴳ+ (D1' ᴳ+ D2')) with ((m1 ᴳ· D1 ᴳ+ D1') ᴳ+ (m2 ᴳ· D1 ᴳ+ D2')).
      apply Ty_term_PatU with (P1 := m1 ᴳ· D1 ᴳ+ D1') (P2 := m2 ᴳ· D1 ᴳ+ D2'); trivial.
      rewrite <- union_associative. rewrite union_associative with (G1 := D1'). rewrite union_commutative with (G1 := D1'). rewrite <- union_associative. rewrite union_associative. reflexivity.
    + destruct in_left_only as (D1' & mP1eq & DestOnlyD1p & DestOnlyP2).
      subst.
      assert (D1' ᴳ+ P2 = D2). { apply remove_singletons_in_union_eq_varonly_l in UnionEq; assumption. } rewrite <- H in *.
      assert (LinOnly (m' ᴳ· D1 ᴳ+ D1')). { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2 & DisjointD). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m' ᴳ· D1 ᴳ+ D1')). { apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2 & DisjointD); crush. }
      specialize (IHTyte1 DestOnlyD1 x' T' m' Validmp D1' DestOnlyD1p H0 H1 eq_refl Tyvp).
      assert (u ᵗ[ x' ≔ v'] = u). { apply term_sub_nIn_no_effect with (P := P2) (T := U). { apply nIn_iff_nMapsTo. apply DestOnly_nMapsTo_var. assumption. } { assumption. } }
      rewrite H2 in *.
      rewrite union_associative.
      apply Ty_term_PatU with (P1 := m' ᴳ· D1 ᴳ+ D1') (P2 := P2); trivial.
    + destruct in_right_only as (D2' & DestOnlyP1 & mP2eq & DestOnlyD2p).
      subst.
      assert (P1 ᴳ+ D2' = D2). { apply remove_singletons_in_union_eq_varonly_r in UnionEq; crush. } rewrite <- H in *.
      assert (LinOnly (m' ᴳ· D1 ᴳ+ D2')). { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyP1D2 & DisjointD). apply LinOnly_union_iff in LinOnlyP1D2. destruct LinOnlyP1D2 as (_ & LinOnlyD2 & _). apply LinOnly_union_iff; repeat split; crush. }
      assert (FinAgeOnly (m' ᴳ· D1 ᴳ+ D2')). { apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyP1D2). apply FinAgeOnly_union_backward in FinAgeOnlyP1D2. destruct FinAgeOnlyP1D2 as (_ & FinAgeOnlyD2). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyP1D2 & DisjointD); crush. }
      specialize (IHTyte2 DestOnlyD1 x' T' m' Validmp D2' DestOnlyD2p H0 H1 eq_refl Tyvp).
      assert (t ᵗ[ x' ≔ v'] = t). { apply term_sub_nIn_no_effect with (P := P1) (T := ①). { apply nIn_iff_nMapsTo. apply DestOnly_nMapsTo_var. crush. } { assumption. } }
      rewrite H2 in *.
      rewrite union_associative. rewrite union_commutative with (G2 := P1). rewrite <- union_associative.
      apply Ty_term_PatU with (P1 := P1) (P2 := (m' ᴳ· D1 ᴳ+ D2')); trivial.
  - rename x into Hu.
    assert (m ᴳ· P1 ᴳ+ P2 = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
    pose proof UnionEq as UnionEq'. apply ctx_split_dec_bound_var in UnionEq'. 2:{ crush. } 2:{ crush. }
    destruct UnionEq' as [[in_both | in_left_only] | in_right_only], (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst; simpl in *;
      try (destruct in_both as (D1' & D2' & m1 & m2 & mP1eq & DestOnlyD1p & P2eq & DestOnlyD2p & meq); try apply ctx_split_union_singl_stimes_inv in mP1eq; try destruct mP1eq as (m1' & m1eq & D1'' & P1eq & DestOnlyD1pp); try pose proof Validmp as Validmp'; try rewrite <- meq in Validmp' ; try apply IsValid_plus_backward in Validmp' ; try destruct Validmp' as (Validm1 & Validm2); try pose proof Validm1 as Validm1'; try rewrite <- m1eq in Validm1'; try apply IsValid_times_backward in Validm1'; try destruct Validm1' as (_ & Validm1'));
      try (destruct in_left_only as (D1' & mP1eq & DestOnlyD1p & DestOnlyP2);
      try apply ctx_split_union_singl_stimes_inv in mP1eq; try destruct mP1eq as (m1 & m1eq & D1'' & P1eq & DestOnlyD1pp); try pose proof Validmp as Validmp'; try rewrite <- m1eq in Validmp'; try apply IsValid_times_backward in Validmp'; try destruct Validmp' as (_ & Validm1));
      try (destruct in_right_only as (D2' & DestOnlyP1 & mP2eq & DestOnlyD2p));
      subst; trivial;
      try (specialize (DisjointP2x1 (ˣ x')); contradiction DisjointP2x1; try apply In_union_forward_r; apply In_singleton_iff; reflexivity);
      try (specialize (DisjointP2x2 (ˣ x')); contradiction DisjointP2x2; try apply In_union_forward_r; apply In_singleton_iff; reflexivity).
    * assert (m ᴳ· D1'' ᴳ+ D2' = D2). { apply remove_singletons_in_union_eq_stimes_l in UnionEq; assumption. } rewrite <- H in *.
      assert (LinOnly (m1' ᴳ· D1 ᴳ+ D1'')). {
        apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). apply LinOnly_stimes_plus_backward in LinOnlyD1. destruct LinOnlyD1 as (LinOnlymm1pD1 & LinOnlym2D1). apply LinOnly_union_iff; repeat split. all:admit. (* all:crush. *) }
      assert (FinAgeOnly (m1' ᴳ· D1 ᴳ+ D1'')). {
        apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2p). apply FinAgeOnly_stimes_plus_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (FinAgeOnlymm1pD1 & FinAgeOnlym2D1). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). all:admit. (* all:crush. *) }
      specialize (IHTyte1 DestOnlyD1 x' T' m1' Validm1' D1'' DestOnlyD1pp H0 H1 eq_refl Tyvp).
      assert (LinOnly (m2 ᴳ· D1 ᴳ+ (D2' ᴳ+ ᴳ{ x1 : m ‗ T1}))). {
        apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). apply LinOnly_stimes_plus_backward in LinOnlyD1. destruct LinOnlyD1 as (LinOnlymm1pD1 & LinOnlym2D1). apply LinOnly_union_iff in LinOnlyD1ppD2p. destruct LinOnlyD1ppD2p as (LinOnlyD1pp & LinOnlyD2p & DisjointD1ppD2p). apply LinOnly_union_iff; repeat split. all:admit. (* all:crush. *) }
      assert (FinAgeOnly (m2 ᴳ· D1 ᴳ+ (D2' ᴳ+ ᴳ{ x1 : m ‗ T1}))). {
        apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD1ppD2p). apply FinAgeOnly_stimes_plus_backward in FinAgeOnlyD1. destruct FinAgeOnlyD1 as (FinAgeOnlymm1pD1 & FinAgeOnlym2D1). apply FinAgeOnly_union_forward; repeat split; apply LinOnly_union_iff in LinOnlyD; destruct LinOnlyD as (LinOnlyD1 & LinOnlyD1ppD2p & DisjointD). all:admit. (* all:crush. *) }
      (* We cannot use IHTyte2 here for two reasons :
        - The subterm doesn't type in D2 + { x1 : ... } + { x' : ... } whereas only a ctx of the form D2 + { x' : ... } is allowed in term_sub lemma.
        - Because of the binding { x1 : m T1 }, the ctx D2 + { x1 : m T1 } is often NOT LinOnly/FinAgeOnly (as the case multiplicity m is not constrained by anything really).
      *)
      (* specialize (IHTyte2 DestOnlyD1 x' T' m2 Validm2 (D2' ᴳ+ ᴳ{ x1 : m ‗ T1}) DestOnlyD2p H2 H3 eq_refl Tyvp). *)
    give_up.
Admitted.

(* ========================================================================= *)

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
Require Coq.Program.Basics.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Compare_dec.
Require Import Arith.
Require Import Lia.

Lemma term_sub_spec_1' :
  forall (Dv' : ctx) (Tv' : type) (x' : var) (v' : val),
  ValidOnly Dv' ->
  DestOnly Dv' ->
  (Dv' ⊢ ᵥ₎ v' : Tv') ->
  forall (Pt : ctx) (t : term) (T : type) (m' : mode),
  LinOnly (m' ᴳ· Dv') ->
  FinAgeOnly (m' ᴳ· Dv') ->
  IsValid m' ->
  ValidOnly Pt ->
  Pt # Dv' ->
  Pt # ᴳ{ x' : m' ‗ Tv'} ->
  (Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'} ⊢ t : T) ->
  (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T).
Proof.
  intros * ValidOnlyDv' DestOnlyDv' Tyv' * LinOnlymDv' FinAgeOnlymDv' Validm' ValidOnlyPt DisjointPtDv DisjointPtx Tyt.
  dependent induction Tyt; simpl.
  - assert (P ᴳ+ D = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
    destruct (ctx_split_union_union P D Pt (ᴳ{ x' : m' ‗ Tv'})) as (PtP & PtD & singP & singD & Pteq & singeq & Peq & Deq); trivial.
    rewrite Peq, Deq, Pteq in *. clear Peq P Deq D Pteq Pt.
    assert (singD = ᴳ{}). { assert (DestOnly singD) by crush. assert (VarOnly singD). { apply VarOnly_union_iff with (G1 := singP). rewrite <- singeq. apply VarOnly_singleton_var. } apply DestOnly_VarOnly_contra; assumption. } rewrite H0 in *. rewrite <- union_empty_r_eq in *.
    clear H0 singD. rewrite <- singeq in *. clear singeq singP.
    rewrite union_swap_2_3_l3.
    assert (DisposableOnly (PtP ᴳ+ m' ᴳ· Dv')). { apply DisposableOnly_sub with (x' := x') (Tv' := Tv'); trivial. crush. crush. }
    apply Ty_term_Val; trivial. supercrush.
  - assert (P ᴳ+ ᴳ{ x0 : m ‗ T} = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x. rename x0 into x.
    destruct (ctx_split_union_union P (ᴳ{ x : m ‗ T}) Pt (ᴳ{ x' : m' ‗ Tv'})) as (PtP & PtD & singP & singD & Pteq & singeq & Peq & Deq); trivial.
    assert (IsValid m) as Validm by (apply IsValid_in_sub_1 with (4 := UnionEq); trivial).
    rewrite Peq, Pteq in *. clear Peq P Pteq Pt. apply eq_sym in singeq, Deq.
    destruct (HNamesFacts.eq_dec x x'), (union_inv_singleton_var singP singD x' m' Tv') as [[(m1' & m2' & singPeq & singDeq & m'eq) | (singPeq & singDeq)] | (singPeq & singDeq)], (union_inv_singleton_var PtD singD x m T) as [[(m1 & m2 & PtDeq & singDeq' & meq) | (PtDeq & singDeq')] | (PtDeq & singDeq')]; trivial; subst;
    try rewrite <- union_empty_l_eq in *; try rewrite <- union_empty_r_eq in *;
    try (apply singletons_var_eq_iff in singDeq'; destruct singDeq' as (_ & -> & ->); subst);
    try (solve [contradiction (singleton_eq_empty_contra _ _ singDeq')]);
    try (solve [apply eq_sym in singDeq'; contradiction (singleton_eq_empty_contra _ _ singDeq')]);
    try (solve [apply Disjoint_union_l_iff in DisjointPx; destruct DisjointPx as (_ & contra); apply Disjoint_singletons_iff in contra; congruence]);
    try (solve [apply Disjoint_union_l_iff in DisjointPtx; destruct DisjointPtx as (_ & contra); apply Disjoint_singletons_iff in contra; congruence]);
    try (solve [contradiction singletons_union_r_neq with (2 := Deq); auto]);
    try (solve [contradiction singletons_union_l_neq with (2 := Deq); auto]);
    try (solve [apply singletons_var_eq_iff in Deq; destruct Deq as (a & b & c); congruence]).
    * rewrite LinOnly_FinAgeOnly_stimes_compatible_linnu_impl_eq; trivial.
      apply Ty_term_Val; trivial. inversion Tyv'; subst.
      assert (P = ᴳ{}). { apply DisposableOnly_LinOnly_contra; trivial. crush. }
      rewrite H, <- union_empty_l_eq in *. assumption.
    * rewrite union_swap_2_3_l3.
      assert (DisposableOnly (PtP ᴳ+ m' ᴳ· Dv')). { apply DisposableOnly_sub with (x' := x') (Tv' := Tv'); trivial. crush. crush. }
      apply Ty_term_Var with (P := (PtP ᴳ+ m' ᴳ· Dv')); trivial. supercrush.
  - assert (m ᴳ· P1 ᴳ+ P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      rewrite stimes_linnu_eq with (G := P2) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *.
      * rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_times_backward with (m1 := m). apply LinOnly_mode_plus_backward with (m2 := m2). assumption. apply FinAgeOnly_mode_times_backward with (m1 := m). apply FinAgeOnly_mode_plus_backward with (m2 := m2). assumption. apply IsValid_times_backward with (m1 := m). apply IsValid_plus_backward with (m2 := m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ t' ᵗ[ x' ≔ v'] : T ⁔ m → U) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply FinAgeOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply IsValid_plus_backward with (m1 := (m · m1)). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        apply Ty_term_App with (2 := Tytsub1) (3 := Tytsub2); trivial.
      * rewrite union_swap_2_3_l3. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_times_backward with (m1 := m). assumption. apply FinAgeOnly_mode_times_backward with (m1 := m). assumption. apply IsValid_times_backward with (m1 := m). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (P2 ⊢ t' ᵗ[ x' ≔ v'] : T ⁔ m → U) as Tytsub2. { replace (t' ᵗ[ x' ≔ v']) with t'. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). rewrite nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ (m · m1) ‗ Tv'). crush. }
        apply Ty_term_App with (2 := Tytsub1) (3 := Tytsub2); trivial.
      * rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : T) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). rewrite nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m2 ‗ Tv'). crush. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ t' ᵗ[ x' ≔ v'] : T ⁔ m → U) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial. crush. crush. Disjoint_singleton_using DisjointPtx. }
        apply Ty_term_App with (2 := Tytsub1) (3 := Tytsub2); trivial.
  - assert (P1 ᴳ+ P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      rewrite stimes_linnu_eq with (G := P1) in UnionEq; rewrite stimes_linnu_eq with (G := P2) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *.
      * rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ①) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_plus_backward with (m2 := m2). assumption.
          apply FinAgeOnly_mode_plus_backward with (m2 := m2). assumption. apply IsValid_plus_backward with (m2 := m2). assumption.
          crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_plus_backward with (m1 := m1). assumption.
          apply FinAgeOnly_mode_plus_backward with (m1 := m1). assumption. apply IsValid_plus_backward with (m1 := m1). assumption.
          crush. crush. Disjoint_singleton_using DisjointPtx. }
        apply Ty_term_PatU with (1 := Tytsub1) (2 := Tytsub2); trivial.
      * rewrite union_swap_2_3_l3.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ①) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial.
          crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (P2 ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. { replace (u ᵗ[ x' ≔ v']) with u. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). rewrite nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m1 ‗ Tv'). crush. }
        apply Ty_term_PatU with (1 := Tytsub1) (2 := Tytsub2); trivial.
      * rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : ①) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). rewrite nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m2 ‗ Tv'). crush. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial.
          crush. crush. Disjoint_singleton_using DisjointPtx. }
        apply Ty_term_PatU with (1 := Tytsub1) (2 := Tytsub2); trivial.
  - assert (m ᴳ· P1 ᴳ+ P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      rewrite stimes_linnu_eq with (G := P2) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *.
      * assert (x1 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x1. rewrite Disjoint_singletons_iff in DisjointP2x1. crush. }
        assert (x2 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x2. rewrite Disjoint_singletons_iff in DisjointP2x2. crush. }
        destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst; try congruence. clear n n0.
        rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T1 ⨁ T2) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_times_backward with (m1 := m). apply LinOnly_mode_plus_backward with (m2 := m2). assumption. apply FinAgeOnly_mode_times_backward with (m1 := m). apply FinAgeOnly_mode_plus_backward with (m2 := m2). assumption. apply IsValid_times_backward with (m1 := m). apply IsValid_plus_backward with (m2 := m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x1 : m ‗ T1} ⊢ u1 ᵗ[ x' ≔ v'] : U) as Tytsub21. {
          rewrite union_swap_2_3_l3.
          apply IHTyt2 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply FinAgeOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply IsValid_plus_backward with (m1 := (m · m1)). assumption. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u2 ᵗ[ x' ≔ v'] : U) as Tytsub22. {
          rewrite union_swap_2_3_l3.
          apply IHTyt3 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply FinAgeOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply IsValid_plus_backward with (m1 := (m · m1)). assumption. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        apply Ty_term_PatS with (4 := Tytsub1) (5 := Tytsub21) (6 := Tytsub22); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. } { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
      * rewrite union_swap_2_3_l3. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T1 ⨁ T2) as Tytsub1. {
            apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. crush. crush. Disjoint_singleton_using DisjointPtx. }
        destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst.
        + apply Ty_term_PatS with (4 := Tytsub1) (5 := Tyt2) (6 := Tyt3); trivial.
        + assert (P2 ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u2 ᵗ[ x' ≔ v'] : U) as Tytsub3.
          { replace (u2 ᵗ[ x' ≔ v']) with u2. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt3). apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m · m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          apply Ty_term_PatS with (4 := Tytsub1) (5 := Tyt2) (6 := Tytsub3); trivial.
        + assert (P2 ᴳ+ ᴳ{ x1 : m ‗ T1} ⊢ u1 ᵗ[ x' ≔ v'] : U) as Tytsub2.
          { replace (u1 ᵗ[ x' ≔ v']) with u1. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m · m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          apply Ty_term_PatS with (4 := Tytsub1) (5 := Tytsub2) (6 := Tyt3); trivial.
        + assert (P2 ᴳ+ ᴳ{ x1 : m ‗ T1} ⊢ u1 ᵗ[ x' ≔ v'] : U) as Tytsub2.
          { replace (u1 ᵗ[ x' ≔ v']) with u1. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m · m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          assert (P2 ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u2 ᵗ[ x' ≔ v'] : U) as Tytsub3.
          { replace (u2 ᵗ[ x' ≔ v']) with u2. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt3). apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m · m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          apply Ty_term_PatS with (4 := Tytsub1) (5 := Tytsub2) (6 := Tytsub3); trivial.
      * assert (x1 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x1. rewrite Disjoint_singletons_iff in DisjointP2x1. crush. }
        assert (x2 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x2. rewrite Disjoint_singletons_iff in DisjointP2x2. crush. }
        destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst; try congruence. clear n n0.
        rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : T1 ⨁ T2) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x1 : m ‗ T1} ⊢ u1 ᵗ[ x' ≔ v'] : U) as Tytsub21. {
          rewrite union_swap_2_3_l3.
          apply IHTyt2 with (Tv' := Tv'); trivial. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var. crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u2 ᵗ[ x' ≔ v'] : U) as Tytsub22. {
          rewrite union_swap_2_3_l3.
          apply IHTyt3 with (Tv' := Tv'); trivial. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var. crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        apply Ty_term_PatS with (4 := Tytsub1) (5 := Tytsub21) (6 := Tytsub22); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. } { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
  - assert (m ᴳ· P1 ᴳ+ P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      rewrite stimes_linnu_eq with (G := P2) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *.
      * assert (x1 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x1. rewrite Disjoint_singletons_iff in DisjointP2x1. crush. }
        assert (x2 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x2. rewrite Disjoint_singletons_iff in DisjointP2x2. crush. }
        destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst; try congruence. clear n n0.
        rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T1 ⨂ T2) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_times_backward with (m1 := m). apply LinOnly_mode_plus_backward with (m2 := m2). assumption. apply FinAgeOnly_mode_times_backward with (m1 := m). apply FinAgeOnly_mode_plus_backward with (m2 := m2). assumption. apply IsValid_times_backward with (m1 := m). apply IsValid_plus_backward with (m2 := m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x1 : m ‗ T1} ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          rewrite union_swap_2_4_l4. rewrite union_swap_2_3_l4.
          apply IHTyt2 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply FinAgeOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply IsValid_plus_backward with (m1 := (m · m1)). assumption. crush. apply Disjoint_union_l_iff; split. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_4_l4. rewrite union_swap_2_3_l4. reflexivity. }
        apply Ty_term_PatP with (5 := Tytsub1) (6 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. } { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
      * rewrite union_swap_2_3_l3. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : T1 ⨂ T2) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. crush. crush. Disjoint_singleton_using DisjointPtx. }
        destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst.
        + apply Disjoint_singletons_iff in Disjointx1x2. contradiction Disjointx1x2. reflexivity.
        + apply Ty_term_PatP with (5 := Tytsub1) (6 := Tyt2); trivial.
        + apply Ty_term_PatP with (5 := Tytsub1) (6 := Tyt2); trivial.
        + assert (P2 ᴳ+ ᴳ{ x1 : m ‗ T1} ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2.
          { replace (u ᵗ[ x' ≔ v']) with u. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). apply nIn_union_iff; split. apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          apply Ty_term_PatP with (5 := Tytsub1) (6 := Tytsub2); trivial.
      * assert (x1 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x1. rewrite Disjoint_singletons_iff in DisjointP2x1. crush. }
        assert (x2 <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x2. rewrite Disjoint_singletons_iff in DisjointP2x2. crush. }
        destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst; try congruence. clear n n0.
        rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : T1 ⨂ T2) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x1 : m ‗ T1} ᴳ+ ᴳ{ x2 : m ‗ T2} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          rewrite union_swap_2_4_l4. rewrite union_swap_2_3_l4.
          apply IHTyt2 with (Tv' := Tv'); trivial. crush. apply Disjoint_union_l_iff; split. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_4_l4. rewrite union_swap_2_3_l4. reflexivity. }
        apply Ty_term_PatP with (5 := Tytsub1) (6 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. } { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
  - assert (m ᴳ· P1 ᴳ+ P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      rewrite stimes_linnu_eq with (G := P2) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *; rename x0 into x.
      * assert (x <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x. rewrite Disjoint_singletons_iff in DisjointP2x. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst; try congruence. clear n0.
        rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ! n ⁔ T) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_times_backward with (m1 := m). apply LinOnly_mode_plus_backward with (m2 := m2). assumption. apply FinAgeOnly_mode_times_backward with (m1 := m). apply FinAgeOnly_mode_plus_backward with (m2 := m2). assumption. apply IsValid_times_backward with (m1 := m). apply IsValid_plus_backward with (m2 := m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x : mode_times' ((cons m nil) ++ (cons n nil) ++ nil) ‗ T}  ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          rewrite union_swap_2_3_l3.
          apply IHTyt2 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply FinAgeOnly_mode_plus_backward with (m1 := (m · m1)). assumption. apply IsValid_plus_backward with (m1 := (m · m1)). assumption.
          apply ValidOnly_union_forward. crush. apply ValidOnly_singleton_iff. simpl. rewrite mode_times_linnu_r_eq. crush. Disjoint_singleton_using DisjointP2x. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        apply Ty_term_PatE with (4 := Tytsub1) (5 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
      * rewrite union_swap_2_3_l3. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ! n ⁔ T) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. crush. crush. Disjoint_singleton_using DisjointPtx. }
        destruct (HNamesFacts.eq_dec x x'); subst.
        + apply Ty_term_PatE with (4 := Tytsub1) (5 := Tyt2); trivial.
        + assert (P2 ᴳ+ ᴳ{ x : mode_times' ((cons m nil) ++ (cons n nil) ++ nil) ‗ T} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2.
          { replace (u ᵗ[ x' ≔ v']) with u. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m · m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          apply Ty_term_PatE with (4 := Tytsub1) (5 := Tytsub2); trivial.
      * assert (x <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x. rewrite Disjoint_singletons_iff in DisjointP2x. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst; try congruence. clear n0.
        rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : ! n ⁔ T) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x : mode_times' ((cons m nil) ++ (cons n nil) ++ nil) ‗ T} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          rewrite union_swap_2_3_l3.
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply ValidOnly_union_forward. crush. apply ValidOnly_singleton_iff. simpl. rewrite mode_times_linnu_r_eq. crush. Disjoint_singleton_using DisjointP2x. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        apply Ty_term_PatE with (4 := Tytsub1) (5 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
  - assert (P1 ᴳ+ P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      rewrite stimes_linnu_eq with (G := P1) in UnionEq.
      rewrite stimes_linnu_eq with (G := P2) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *; rename x0 into x.
      * assert (x <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x. rewrite Disjoint_singletons_iff in DisjointP2x. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst; try congruence. clear n.
        rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : U ⧔ T) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m2 := m2). assumption. apply FinAgeOnly_mode_plus_backward with (m2 := m2). assumption. apply IsValid_plus_backward with (m2 := m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (¹↑ ᴳ· (Pt2 ᴳ+ m2 ᴳ· Dv') ᴳ+ ᴳ{ x : ¹ν ‗ T} ⊢ t' ᵗ[ x' ≔ v'] : T') as Tytsub2. {
          rewrite stimes_distrib_on_union. rewrite union_swap_2_3_l3. rewrite stimes_is_action.
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_times_linone_forward. apply LinOnly_mode_plus_backward with (m1 := m1). assumption. apply FinAgeOnly_times_linone_forward. apply FinAgeOnly_mode_plus_backward with (m1 := m1). assumption. apply IsValid_times_iff; split. constructor. apply IsValid_plus_backward with (m1 := m1). assumption. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. rewrite stimes_distrib_on_union. rewrite stimes_singleton_var. rewrite mode_times_commutative. reflexivity. }
        apply Ty_term_Map with (2 := Tytsub1) (3 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
      * rewrite union_swap_2_3_l3.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : U ⧔ T) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst.
        + apply Ty_term_Map with (2 := Tytsub1) (3 := Tyt2); trivial.
        + assert (¹↑ ᴳ· P2 ᴳ+ ᴳ{ x : ¹ν ‗ T} ⊢ t' ᵗ[ x' ≔ v'] : T') as Tytsub2.
          { replace (t' ᵗ[ x' ≔ v']) with t'. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). apply nIn_union_iff; split. apply nIn_stimes_iff. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          apply Ty_term_Map with (2 := Tytsub1) (3 := Tytsub2); trivial.
      * assert (x <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x. rewrite Disjoint_singletons_iff in DisjointP2x. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst; try congruence. clear n.
        rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : U ⧔ T) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (¹↑ ᴳ· (Pt2 ᴳ+ m2 ᴳ· Dv') ᴳ+ ᴳ{ x : ¹ν ‗ T} ⊢ t' ᵗ[ x' ≔ v'] : T') as Tytsub2. {
          rewrite stimes_distrib_on_union. rewrite union_swap_2_3_l3. rewrite stimes_is_action.
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_times_linone_forward. assumption. apply FinAgeOnly_times_linone_forward. assumption. apply IsValid_times_iff; split. constructor. assumption. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. rewrite stimes_distrib_on_union. rewrite stimes_singleton_var. rewrite mode_times_commutative. reflexivity. }
        apply Ty_term_Map with (2 := Tytsub1) (3 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_ToA with (1 := Tytsub); trivial.
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : U ⧔ ! ¹∞ ⁔ T) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_FromA with (1 := Tytsub); trivial.
    - assert (DisposableOnly (Pt ᴳ+ m' ᴳ· Dv')). { apply DisposableOnly_sub with (x' := x') (Tv' := Tv'); trivial. }
      apply Ty_term_Alloc; trivial.
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ ① ⌋ n) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_FillU with (2 := Tytsub); trivial.
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T1 ⨁ T2 ⌋ n) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_FillL with (2 := Tytsub); trivial.
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T1 ⨁ T2 ⌋ n) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_FillR with (2 := Tytsub); trivial.
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T1 ⨂ T2 ⌋ n) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_FillP with (2 := Tytsub); trivial.
    - assert (Pt ᴳ+ m' ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ ! n' ⁔ T ⌋ n) as Tytsub. { apply IHTyt with (Tv' := Tv'); trivial. }
      apply Ty_term_FillE with (3 := Tytsub); trivial.
    - assert (P1 ᴳ+ (mode_times' ((cons ¹↑ nil) ++ (cons n nil) ++ nil)) ᴳ· P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      assert (mode_times' ((cons ¹↑ nil) ++ (cons n nil) ++ nil) = (¹↑ · n)) as modeeq. { simpl. rewrite mode_times_linnu_r_eq. reflexivity. }
      rewrite modeeq in *.
      rewrite stimes_linnu_eq with (G := P1) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *; rename x0 into x.
      * assert (x <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x. rewrite Disjoint_singletons_iff in DisjointP2x. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst; try congruence. clear n0.
        rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T ⁔ m → U ⌋ n) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m2 := (¹↑ · n) · m2). assumption. apply FinAgeOnly_mode_plus_backward with (m2 := (¹↑ · n) · m2). assumption. apply IsValid_plus_backward with (m2 := (¹↑ · n) · m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x : m ‗ T} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          rewrite union_swap_2_3_l3.
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_times_backward with (m1 := (¹↑ · n)). apply LinOnly_mode_plus_backward with (m1 := m1). assumption. apply FinAgeOnly_mode_times_backward with (m1 := (¹↑ · n)). apply FinAgeOnly_mode_plus_backward with (m1 := m1). assumption. apply IsValid_times_backward with (m1 := (¹↑ · n)). apply IsValid_plus_backward with (m1 := m1). assumption. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        rewrite <- modeeq in *. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        apply Ty_term_FillF with (4 := Tytsub1) (5 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
      * rewrite union_swap_2_3_l3.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T ⁔ m → U ⌋ n) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst.
        + rewrite <- modeeq in *.
          apply Ty_term_FillF with (4 := Tytsub1) (5 := Tyt2); trivial.
        + assert (P2 ᴳ+ ᴳ{ x : m ‗ T} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2.
          { replace (u ᵗ[ x' ≔ v']) with u. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). apply nIn_union_iff; split. assumption. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m1 ‗ Tv'). apply Disjoint_singletons_iff. injection. intros ->. congruence. }
          rewrite <- modeeq in *.
          apply Ty_term_FillF with (4 := Tytsub1) (5 := Tytsub2); trivial.
      * assert (x <> x'). { symmetry. apply Disjoint_union_l_iff in DisjointP2x. rewrite Disjoint_singletons_iff in DisjointP2x. crush. }
        destruct (HNamesFacts.eq_dec x x'); subst; try congruence. clear n0.
        rewrite <- union_associative.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : ⌊ T ⁔ m → U ⌋ n) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ᴳ+ ᴳ{ x : m ‗ T} ⊢ u ᵗ[ x' ≔ v'] : U) as Tytsub2. {
          rewrite union_swap_2_3_l3.
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_times_backward with (m1 := (¹↑ · n)). assumption. apply FinAgeOnly_mode_times_backward with (m1 := (¹↑ · n)). assumption. apply IsValid_times_backward with (m1 := (¹↑ · n)). assumption. crush. apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. apply DestOnly_Disjoint_singleton_var; crush. apply Disjoint_union_l_iff; split. Disjoint_singleton_using DisjointPtx. apply Disjoint_singletons_iff; injection; intros ->; congruence. rewrite union_swap_2_3_l3. reflexivity. }
        rewrite <- modeeq in *. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        apply Ty_term_FillF with (4 := Tytsub1) (5 := Tytsub2); trivial. { apply Disjoint_union_l_iff; split. crush. apply DestOnly_Disjoint_singleton_var; crush. }
  - assert (P1 ᴳ+ (mode_times' ((cons ¹↑ nil) ++ nil)) ᴳ· P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      assert (mode_times' ((cons ¹↑ nil) ++ nil) = ¹↑) as modeeq. { simpl. reflexivity. }
      rewrite modeeq in *.
      rewrite stimes_linnu_eq with (G := P1) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *.
      * rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative; rewrite union_swap_2_3_l4. rewrite <- union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ U ⌋ ¹ν) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m2 := ¹↑ · m2). assumption. apply FinAgeOnly_mode_plus_backward with (m2 := ¹↑ · m2). assumption. apply IsValid_plus_backward with (m2 := ¹↑ · m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ t' ᵗ[ x' ≔ v'] : U ⧔ T) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_times_backward with (m1 := ¹↑). apply LinOnly_mode_plus_backward with (m1 := m1). assumption. apply FinAgeOnly_mode_times_backward with (m1 := ¹↑). apply FinAgeOnly_mode_plus_backward with (m1 := m1). assumption. apply IsValid_times_backward with (m1 := ¹↑). apply IsValid_plus_backward with (m1 := m1). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        apply Ty_term_FillComp with (1 := Tytsub1) (2 := Tytsub2); trivial.
      * rewrite union_swap_2_3_l3.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ U ⌋ ¹ν) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. }
        assert (P2 ⊢ t' ᵗ[ x' ≔ v'] : U ⧔ T) as Tytsub2. {
          replace (t' ᵗ[ x' ≔ v']) with t'. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). assumption. }
        apply Ty_term_FillComp with (1 := Tytsub1) (2 := Tytsub2); trivial.
      * rewrite <- union_associative. rewrite <- stimes_is_action. rewrite <- stimes_distrib_on_union.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : ⌊ U ⌋ ¹ν) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ t' ᵗ[ x' ≔ v'] : U ⧔ T) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_times_backward with (m1 := ¹↑). assumption. apply FinAgeOnly_mode_times_backward with (m1 := ¹↑). assumption. apply IsValid_times_backward with (m1 := ¹↑). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        apply Ty_term_FillComp with (1 := Tytsub1) (2 := Tytsub2); trivial.
  - assert (P1 ᴳ+ mode_times' ((cons ¹↑ nil) ++ (cons n nil) ++ nil) ᴳ· P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear x.
      assert (mode_times' ((cons ¹↑ nil) ++ (cons n nil) ++ nil) = (¹↑ · n)) as modeeq. { simpl. rewrite mode_times_linnu_r_eq. reflexivity. }
      rewrite modeeq in *.
      rewrite stimes_linnu_eq with (G := P1) in UnionEq.
      destruct ctx_split_stimes_union_union with (3 := UnionEq) as [(m1 & m2 & Pt1 & Pt2 & meq & Pteq & P1eq & P2eq) | [(m1 & Pt1 & meq & Pteq & P1eq & nInxpP2) | (m2 & Pt2 & meq & Pteq & P2eq & nInxpP1)]]. { crush. } { crush. }
      all: subst; try rewrite ! mode_times_linnu_l_eq in *; try rewrite ! mode_times_linnu_r_eq in *; try rewrite <- ! union_empty_l_eq in *; try rewrite <- ! union_empty_r_eq in *; try rewrite <- ! stimes_linnu_eq in *.
      * rewrite <- stimes_mode_plus_eq; repeat rewrite union_associative. rewrite union_swap_2_3_l4. rewrite <- union_associative. rewrite <- stimes_is_action with (n := m2). rewrite <- stimes_distrib_on_union.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T ⌋ n) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. apply LinOnly_mode_plus_backward with (m2 := (¹↑ · n) · m2). assumption. apply FinAgeOnly_mode_plus_backward with (m2 := (¹↑ · n) · m2). assumption. apply IsValid_plus_backward with (m2 := (¹↑ · n) · m2). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ t' ᵗ[ x' ≔ v'] : T) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_times_backward with (m1 := ¹↑ · n). apply LinOnly_mode_plus_backward with (m1 := m1). assumption. apply FinAgeOnly_mode_times_backward with (m1 := ¹↑ · n). apply FinAgeOnly_mode_plus_backward with (m1 := m1). assumption. apply IsValid_times_backward with (m1 := ¹↑ · n). apply IsValid_plus_backward with (m1 := m1). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        rewrite <- modeeq in *.
        apply Ty_term_FillLeaf with (2 := Tytsub1) (3 := Tytsub2); trivial.
      * rewrite union_swap_2_3_l3.
        assert (Pt1 ᴳ+ m1 ᴳ· Dv' ⊢ t ᵗ[ x' ≔ v'] : ⌊ T ⌋ n) as Tytsub1. {
          apply IHTyt1 with (Tv' := Tv'); trivial. crush. crush. crush. }
        assert (P2 ⊢ t' ᵗ[ x' ≔ v'] : T) as Tytsub2. {
          replace (t' ᵗ[ x' ≔ v']) with t'. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt2). assumption. }
        rewrite <- modeeq in *.
        apply Ty_term_FillLeaf with (2 := Tytsub1) (3 := Tytsub2); trivial.
      * rewrite <- union_associative. rewrite <- stimes_is_action with (n := m2). rewrite <- stimes_distrib_on_union.
        assert (P1 ⊢ t ᵗ[ x' ≔ v'] : ⌊ T ⌋ n) as Tytsub1. { replace (t ᵗ[ x' ≔ v']) with t. assumption. symmetry. apply term_sub_nIn_no_effect with (2 := Tyt1). assumption. }
        assert (Pt2 ᴳ+ m2 ᴳ· Dv' ⊢ t' ᵗ[ x' ≔ v'] : T) as Tytsub2. {
          apply IHTyt2 with (Tv' := Tv'); trivial.
          apply LinOnly_mode_times_backward with (m1 := ¹↑ · n). assumption. apply FinAgeOnly_mode_times_backward with (m1 := ¹↑ · n). assumption. apply IsValid_times_backward with (m1 := ¹↑ · n). assumption. crush. crush. Disjoint_singleton_using DisjointPtx. }
        rewrite <- modeeq in *.
        apply Ty_term_FillLeaf with (2 := Tytsub1) (3 := Tytsub2); trivial.
Qed.

Lemma term_sub_spec_1 :
  forall (D1 D2 : ctx) (m' : mode) (T' U' : type) (te : term) (x' : var) (v' : val),
  IsValid m' ->
  DestOnly D1 ->
  DestOnly D2 ->
  LinOnly (m' ᴳ· D1 ᴳ+ D2) ->
  FinAgeOnly (m' ᴳ· D1 ᴳ+ D2) ->
  D2 # ᴳ{ x' : m' ‗ T'} ->
  (D2 ᴳ+ ᴳ{ x' : m' ‗ T'} ⊢ te : U') ->
  (D1 ⊢ ᵥ₎ v' : T') ->
  (m' ᴳ· D1 ᴳ+ D2 ⊢ te ᵗ[ x' ≔ v'] : U').
Proof.
  intros * Validmp DestOnlyD1 DestOnlyD2 LinOnlyD FinAgeOnlyD DisjointD2x Tyte Tyvp.
  rewrite union_commutative.
  pose proof LinOnlyD as ValidOnlyD. apply LinOnly_wk_ValidOnly in ValidOnlyD.
  apply term_sub_spec_1' with (Tv' := T'). crush. crush. crush. crush. crush. crush. crush. apply Disjoint_commutative. crush. crush. crush.
Qed.

(* ========================================================================= *)

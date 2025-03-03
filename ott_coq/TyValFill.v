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

Lemma Ty_val_fill : forall (D20 D5 : ctx) (h : hname) (v' : val) (T : type) , D20 ᴳ+ ᴳ-⁻¹ D5 ⫦ v' : T ->
  forall (v : val) (D4 D13 : ctx) (n : mode) (U : type),
  ValidOnly (ᴳ-⁻¹ D13) ->
  IsValid n ->
  D4 # D5 ->
  D4 # D13 ->
  D4 # D20 ->
  D4 # ᴳ{- h : ¹ν ⌊ T ⌋ n} ->
  D5 # D13 ->
  D5 # D20 ->
  D5 # ᴳ{- h : ¹ν ⌊ T ⌋ n} ->
  D13 # D20 ->
  D13 # ᴳ{- h : ¹ν ⌊ T ⌋ n} ->
  D20 # ᴳ{- h : ¹ν ⌊ T ⌋ n} ->
  D4 ᴳ+ ᴳ-⁻¹ (D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n}) ⫦ v : U ->
  D4 ᴳ+ ᴳ-⁻¹ D13 ᴳ+ n ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5) ⫦ val_fill v h hnamesᴳ( D5) v' : U.
Proof.
  intros * Tyv'. induction v; intros * ValidOnlyhiD13 IsValidn DisjointD4D5 DisjointD4D13 DisjointD4D20 DisjointD4h DisjointD5D13 DisjointD5D20 DisjointD5h DisjointD13D20 DisjointD13h DisjointD20h Tyv; simpl.
  - subst. rewrite hminus_inv_distrib_on_union in Tyv. rewrite hminus_inv_singleton in Tyv.
    assert (ᴳ{+ h0 : U ‗ ¹ν} = D4 ᴳ+ (ᴳ-⁻¹ D13 ᴳ+ ᴳ{+ h : T ‗ n})). { dependent destruction Tyv. unfold ctx_singleton, singleton, union, hminus_inv, merge_with, merge; cbn. apply ext_eq'. cbn. rewrite x. reflexivity. } 2:{ crush. } destruct (HNamesFacts.eq_dec h0 h) eqn:h_eq; subst.
    * assert (D4 = ᴳ{} /\ D13 = ᴳ{} /\ T = U /\ n = ¹ν) as (D4eq & D13eq & Teq & neq). { destruct (singleton_is_one_of_disjoint_union_3 (ʰ h) (₊ U ‗ ¹ν) D4 (ᴳ-⁻¹ D13) (ᴳ{+ h : T ‗ n})). { crush. } { Disjoint_singleton_using DisjointD4h. } { Disjoint_singleton_using DisjointD13h. } { assumption. } destruct s. { destruct a as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. } { destruct a as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. }
      repeat split. crush. rewrite <- hminus_inv_empty_iff. crush. all: destruct a as (_ & _ & singeq); apply singleton_same_name_eq_iff in singeq; inversion singeq; reflexivity.
      } subst. rewrite hminus_inv_empty_eq. rewrite <- !stimes_linnu_eq. rewrite <- !union_empty_l_eq. assumption.
    * destruct (singleton_is_one_of_disjoint_union_3 (ʰ h0) (₊ U ‗ ¹ν) D4 (ᴳ-⁻¹ D13) (ᴳ{+ h : T ‗ n})). { crush. } { Disjoint_singleton_using DisjointD4h. } { Disjoint_singleton_using DisjointD13h. } { assumption. }
      destruct s. { destruct a as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. } { destruct a as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. } { destruct a as (_ & _ & contra). apply singleton_eq_impl_same_name in contra. inversion contra. congruence. }
  - subst. rewrite hminus_inv_distrib_on_union in Tyv. rewrite hminus_inv_singleton in Tyv.
    assert (exists m T0 n0, ᴳ{- h0 : m⌊ T0 ⌋ n0} = D4 ᴳ+ (ᴳ-⁻¹ D13 ᴳ+ ᴳ{+ h : T ‗ n})). { dependent destruction Tyv. exists m, T0, n0. unfold ctx_singleton, singleton, union, hminus_inv, merge_with, merge; cbn. apply ext_eq'. cbn. rewrite x. reflexivity. } destruct H as (m & T0 & n0 & H).
    destruct (singleton_is_one_of_disjoint_union_3 (ʰ h0) (₋ m ⌊ T0 ⌋ n0) D4 (ᴳ-⁻¹ D13) (ᴳ{+ h : T ‗ n})). { crush. } { Disjoint_singleton_using DisjointD4h. } { Disjoint_singleton_using DisjointD13h. } { assumption. } destruct s. { destruct a as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. } { destruct a as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. } { destruct a as (_ & _ & contra). pose proof contra as contra'. apply singleton_eq_impl_same_name in contra. inversion contra; subst. apply singleton_same_name_eq_iff in contra'. congruence. } { crush. }
  - subst. rewrite hminus_inv_distrib_on_union in Tyv. rewrite hminus_inv_singleton in Tyv.
    assert (ᴳ{} = D4 ᴳ+ (ᴳ-⁻¹ D13 ᴳ+ ᴳ{+ h : T ‗ n})). { dependent destruction Tyv. unfold ctx_singleton, singleton, union, hminus_inv, merge_with, merge; cbn. apply ext_eq'. cbn. rewrite x. reflexivity. }
    apply eq_sym in H. rewrite union_empty_iff in H. rewrite union_empty_iff in H. destruct H as (_ & _ & contra). apply singleton_eq_empty_contra in contra. exfalso; assumption. { crush. }
  - dependent destruction Tyv. rewrite DestOnly_union_iff in DestOnlyD. rewrite hminus_inv_distrib_on_union in DestOnlyD. rewrite DestOnly_union_iff in DestOnlyD. destruct DestOnlyD as (_ & _ & contra). rewrite hminus_inv_singleton in contra. apply DestOnly_singleton_hole_contra in contra. contradiction. { crush. }
  - dependent destruction Tyv. apply Ty_val_Left. apply IHv; trivial.
  - dependent destruction Tyv. apply Ty_val_Right. apply IHv; trivial.
  - dependent destruction Tyv.
    assert (m ᴳ· G = D4 ᴳ+ ᴳ-⁻¹ (D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n})). { apply ext_eq. intros name. cbn; rewrite x. reflexivity. } clear x.
    rewrite hminus_inv_distrib_on_union in H. rewrite hminus_inv_singleton in H.
    destruct (ctx_split_stimes_union_3 m G D4 (ᴳ-⁻¹ D13) (ᴳ{+ h : T ‗ n})) as (D4' & D13' & hSing' & D4eq & D13eq & hSingeq & Geq); trivial. { crush. } { Disjoint_singleton_using DisjointD4h. } { Disjoint_singleton_using DisjointD13h. } 2:{ assumption. }
    destruct (stimes_inv_singleton_hole m hSing' h T n) as (m' & neq & hSingeq').
    symmetry; assumption. rewrite Disjoint_hminus_inv_r_iff with (D' := D13) in *. rewrite Disjoint_hminus_inv_l_iff with (D := D13) in *. rewrite D4eq, D13eq, neq in *. rewrite <- stimes_is_action. rewrite <- 2 stimes_distrib_on_union.
    constructor. apply eq_sym in D13eq. apply stimes_inv_hminus_inv in D13eq. rewrite D13eq in *. apply IHv; trivial; swap 1 12. rewrite hSingeq' in Geq. rewrite Geq in Tyv. rewrite hminus_inv_distrib_on_union. rewrite hminus_inv_singleton. assumption.
    { Disjoint_singleton_using DisjointD13h. } { crush. } { crush. } { crush. } { crush. } { Disjoint_singleton_using DisjointD4h. } { crush. } { Disjoint_singleton_using DisjointD5h. } { crush. } { Disjoint_singleton_using DisjointD13h. } { Disjoint_singleton_using DisjointD20h. } { crush. } { rewrite <- D13eq; assumption. } { assumption. }
  - dependent destruction Tyv.
    assert (G1 ᴳ+ G2 = D4 ᴳ+ ᴳ-⁻¹ (D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n})). { apply ext_eq. intros name. cbn; rewrite x. reflexivity. } clear x.
    rewrite hminus_inv_distrib_on_union in H. rewrite hminus_inv_singleton in H.
    destruct (ctx_split_union_union_3 G1 G2 D4 (ᴳ-⁻¹ D13) (ᴳ{+ h : T ‗ n})) as (D41 & D42 & D131' & D132' & sing1 & sing2 & D4eq & D13eq & singeq & G1eq & G2eq); trivial. { crush. } { Disjoint_singleton_using DisjointD4h. } { Disjoint_singleton_using DisjointD13h. } 2:{ assumption. }
    pose proof singeq as singeq'.
    apply eq_sym in singeq. apply union_inv_singleton_hole in singeq. 2:{ assumption. }
    pose proof D13eq as D13eq'.
    apply union_inv_hminus_inv in D13eq. destruct D13eq as (D131eq & D132eq).
    rewrite G1eq, G2eq in *.
    rewrite Disjoint_hminus_inv_r_iff with (D' := D13) in *. rewrite Disjoint_hminus_inv_l_iff with (D := D13) in *.
    rewrite D4eq, D131eq, D132eq in *. rewrite D13eq' in *. 2:{ assumption. }
    destruct singeq as [[(n1 & n2 & sing1eq & sing2eq & neq) | (sing1eq & sing2eq)] | (sing1eq & sing2eq)].
    * rewrite sing1eq, sing2eq, neq in *. rewrite singeq' in *.
      replace (D41 ᴳ+ D42 ᴳ+ (ᴳ-⁻¹ (ᴳ- D131') ᴳ+ ᴳ-⁻¹ (ᴳ- D132')) ᴳ+ mode_plus n1 n2 ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5)) with ((D41 ᴳ+ ᴳ-⁻¹ (ᴳ- D131') ᴳ+ n1 ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5)) ᴳ+ (D42 ᴳ+ ᴳ-⁻¹ (ᴳ- D132') ᴳ+ n2 ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5))).
      constructor.
      apply IHv1.
        { crush. } { crush. } { crush. } { crush. } { crush. } { Disjoint_singleton_using DisjointD4h. } { crush. } { crush. } { Disjoint_singleton_using DisjointD5h. } { crush. } { Disjoint_singleton_using DisjointD13h. } { Disjoint_singleton_using DisjointD20h. }
        { rewrite hminus_inv_distrib_on_union. rewrite hminus_inv_singleton. assumption. Disjoint_singleton_using DisjointD13h. }
      apply IHv2.
        { crush. } { crush. } { crush. } { crush. } { crush. } { Disjoint_singleton_using DisjointD4h. } { crush. } { crush. } { Disjoint_singleton_using DisjointD5h. } { crush. } { Disjoint_singleton_using DisjointD13h. } { Disjoint_singleton_using DisjointD20h. }
        { rewrite hminus_inv_distrib_on_union. rewrite hminus_inv_singleton. assumption. Disjoint_singleton_using DisjointD13h. }
      rewrite <- stimes_mode_plus_eq.
      repeat rewrite union_associative.
      rewrite union_swap_2_4_l6.
      rewrite union_swap_3_4_l6.
      rewrite union_swap_4_5_l6.
      reflexivity.
    * rewrite sing2eq in *. rewrite <- union_empty_r_eq in *. rewrite sing1eq in *.
      replace (D41 ᴳ+ D42 ᴳ+ (ᴳ-⁻¹ (ᴳ- D131') ᴳ+ ᴳ-⁻¹ (ᴳ- D132')) ᴳ+ n ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5)) with ((D41 ᴳ+ ᴳ-⁻¹ (ᴳ- D131') ᴳ+ n ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5)) ᴳ+ (D42 ᴳ+ ᴳ-⁻¹ (ᴳ- D132'))).
      constructor.
      apply IHv1.
        { crush. } { crush. } { crush. } { crush. } { crush. } { Disjoint_singleton_using DisjointD4h. } { crush. } { crush. } { Disjoint_singleton_using DisjointD5h. } { crush. } { Disjoint_singleton_using DisjointD13h. } { Disjoint_singleton_using DisjointD20h. }
        { rewrite hminus_inv_distrib_on_union. rewrite hminus_inv_singleton. assumption. Disjoint_singleton_using DisjointD13h. }
      rewrite val_fill_nIn_no_effect with (G := D42 ᴳ+ ᴳ-⁻¹ (ᴳ- D132')) (T := T2).
        { assumption. } { apply nIn_union_iff; split; apply nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ n). crush. crush. } { assumption. }
      repeat rewrite union_associative.
      rewrite union_swap_2_4_l5.
      rewrite union_swap_3_5_l5.
      rewrite union_swap_3_4_l5.
      reflexivity.
    * rewrite sing1eq in *. rewrite <- union_empty_r_eq in *. rewrite sing2eq in *.
      replace (D41 ᴳ+ D42 ᴳ+ (ᴳ-⁻¹ (ᴳ- D131') ᴳ+ ᴳ-⁻¹ (ᴳ- D132')) ᴳ+ n ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5)) with ((D41 ᴳ+ ᴳ-⁻¹ (ᴳ- D131')) ᴳ+ (D42 ᴳ+ ᴳ-⁻¹ (ᴳ- D132') ᴳ+ n ᴳ· (D20 ᴳ+ ᴳ-⁻¹ D5))).
      constructor.
      rewrite val_fill_nIn_no_effect with (G := D41 ᴳ+ ᴳ-⁻¹ (ᴳ- D131')) (T := T1).
        { assumption. } { apply nIn_union_iff; split; apply nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ n). crush. crush. } { assumption. }
      apply IHv2.
        { crush. } { crush. } { crush. } { crush. } { crush. } { Disjoint_singleton_using DisjointD4h. } { crush. } { crush. } { Disjoint_singleton_using DisjointD5h. } { crush. } { Disjoint_singleton_using DisjointD13h. } { Disjoint_singleton_using DisjointD20h. }
        { rewrite hminus_inv_distrib_on_union. rewrite hminus_inv_singleton. assumption. Disjoint_singleton_using DisjointD13h. }
      repeat rewrite union_associative.
      rewrite union_swap_2_3_l5.
      reflexivity.
  - assert (exists D1 D2, D1 ᴳ+ D2 = D4 ᴳ+ ᴳ-⁻¹ (D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n}) /\ DestOnly D1 /\ DestOnly D2). { dependent destruction Tyv. exists D1, D2. repeat split; trivial. unfold ctx_singleton, singleton, union, hminus_inv, merge_with, merge; cbn. apply ext_eq'. cbn. rewrite x. reflexivity. }
    destruct H0 as (D1 & D2 & CtxEq & DestOnlyD1 & DestOnlyD2).
    assert (DestOnly (D1 ᴳ+ D2)). { crush. }
    rewrite CtxEq in H0. rewrite hminus_inv_distrib_on_union in H0. autorewrite with propagate_down in H0. destruct H0 as (_ & _ & contra). rewrite hminus_inv_singleton in contra. apply DestOnly_singleton_hole_contra in contra. contradiction. { crush. }
Qed.

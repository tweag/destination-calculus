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

Lemma ectxs_fillCtor_spec' : forall (C : ectxs) (h : hname) (v : val) (D3: ctx) (U: type) (n : mode), IsValid n -> DestOnly D3 -> D3 # ᴳ{- h : ¹ν ⌊ U ⌋ n } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  ValidOnly (ᴳ-⁻¹ D3) ->
  ᴳ-⁻¹ D3 ⫦ v : U ->
  forall (m0 : mode) (T U0 : type) (D1: ctx),
  IsValid m0 ->
  DestOnly D1 ->
  D1 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ U ⌋ n } ->
  D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ U ⌋ n } ⊣ C : T ↣ U0 ->
  D1 ᴳ+ m0 ᴳ· (ᴳ- (n ᴳ· (ᴳ-⁻¹ D3))) ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T ↣ U0.
Proof.
  intros * Validn DestOnlyD3 DisjointD3h HDisjointCD3 ValidOnlyhiD3 Tyv. induction C.
  - intros * Validm0 DestOnlyD1 DisjointD1D3 DisjointD1h TyC. (* Prove that union of singleton + other things is not the empty context *) admit.
  - intros * Validm0 DestOnlyD1 DisjointD1D3 DisjointD1h TyC.
    destruct a; simpl; dependent destruction TyC.
    * (* Ty-ectxs-App1 *)
      assert (LinOnly (m ᴳ· (D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ U ⌋ n}) ᴳ+ D2) /\ FinAgeOnly (m ᴳ· (D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ U ⌋ n}) ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply Ty_ectxs_LinOnly_FinAgeOnly with (C := C) (T := U1) (U0 := U0). tauto. }
      assert (HNames.Subset hnamesᴳ(m ᴳ· (D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ U ⌋ n}) ᴳ+ D2) hnames©(C)) as HDisjointCD2.
        { apply hnames_C_wk_hnames_G with (T := U1) (U0 := U0); trivial. }
      assert ((m ᴳ· (D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ U ⌋ n}) ᴳ+ D2) # D3).
        { apply HDisjoint_to_Disjoint. supercrush. apply HSubset_preserves_HDisjoint with (H2 := hnames©( C)); trivial. }
      constructor 2 with (D2 := D2) (m := m) (U := U1); trivial.
        { supercrush. } { supercrush. }
        { replace (m ᴳ· (D1 ᴳ+ m0 ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D3)) ᴳ+ D2) with (m ᴳ· D1 ᴳ+ D2 ᴳ+ (m · m0) ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D3)) in *. 2:{ rewrite stimes_distrib_on_union. rewrite stimes_is_action. rewrite union_swap_2_3_l3. reflexivity. }
          apply IHC with (D1 := m ᴳ· D1 ᴳ+ D2) (m0 := m · m0); trivial.
          { crush. } { crush. } { crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. }
          { rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC. assumption. }
        }
    * (* Ty-ectxs-App2 *) admit.
    * (* Ty-ectxs-PatU *) admit.
    * (* Ty-ectxs-PatS *) admit.
    * (* Ty-ectxs-PatP *) admit.
    * (* Ty-ectxs-PatE *) admit.
    * (* Ty-ectxs-Map *) admit.
    * (* Ty-ectxs-ToA *) admit.
    * (* Ty-ectxs-FromA *) admit.
    * (* Ty-ectxs-FillU *) admit.
    * (* Ty-ectxs-FillL *) admit.
    * (* Ty-ectxs-FillR *) admit.
    * (* Ty-ectxs-FillE *) admit.
    * (* Ty-ectxs-FillP *) admit.
    * (* Ty-ectxs-FillF *) admit.
    * (* Ty-ectxs-FillComp1 *) admit.
    * (* Ty-ectxs-FillComp2 *) admit.
    * (* Ty-ectxs-FillLeaf1 *) admit.
    * (* Ty-ectxs-FillLeaf2 *) admit.
    * (* Ty-ectxs-OpenAmpar *)
      rename D3 into D6, D2 into D3, DestOnlyD3 into DestOnlyD6, ValidOnlyhiD3 into ValidOnlyhiD6, DisjointD3h into DisjointD6h, DisjointD2D3 into DisjointD4D3, HDisjointCD3 into HDisjointCD3D6, DisjointD1D3 into DisjointD1D6, U into T, U1 into U, ValidOnlyhiD0 into ValidOnlyhiD3, DisjointD1D2 into DisjointD0D4, DisjointD1D0 into DisjointD0D3, DestOnlyD2 into DestOnlyD4, DestOnlyD4 into DestOnlyD3.
      assert ((¹↑ ᴳ· D0 ᴳ+ D3).(underlying) = (D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ n}).(underlying)). { unfold union, merge_with, merge, ctx_singleton. simpl. apply x. } clear x.
      assert ((¹↑ ᴳ· D0 ᴳ+ D3) = (D1 ᴳ+ m0 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ n})). { apply ext_eq. intros n'. rewrite H. reflexivity. }
      assert (LinOnly (D0 ᴳ+ D4) /\ FinAgeOnly (D0 ᴳ+ D4)) as (LinOnlyD & FinAgeOnlyD).
        { apply Ty_ectxs_LinOnly_FinAgeOnly with (C := C) (T := U ⧔ T') (U0 := U0). tauto. }
      clear H. rename H1 into ctx_eq.
      pose proof ValidOnlyhiD3 as ValidOnlyhiD3'. apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3'. destruct ValidOnlyhiD3' as (_ & ValidOnlyD3). pose proof ValidOnlyD3 as LinOnlyD3. pose proof ValidOnlyD3 as FinAgeOnlyD3. apply LinNuOnly_wk_LinOnly in LinOnlyD3, ValidOnlyD3. apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD3. apply LinOnly_wk_ValidOnly in ValidOnlyD3.
      assert (LinOnly (¹↑ ᴳ· D0 ᴳ+ D3) /\ FinAgeOnly (¹↑ ᴳ· D0 ᴳ+ D3)) as (LinOnlyD' & FinAgeOnlyD'). split.
        { supercrush. } { supercrush. }
      rewrite ctx_eq in LinOnlyD', FinAgeOnlyD'.
      destruct (ctx_split_union_union (¹↑ ᴳ· D0) D3 D1 (m0 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ n})) as (D10 & D13 & sing0 & sing3 & D1eq & singeq & D0eq & D3eq).
        { crush. } { crush. }
      assert (IsLin m0). { rewrite stimes_singleton_dest in LinOnlyD'. rewrite mode_times_linnu_l_eq in LinOnlyD'. assert (LinOnly ᴳ{- h : m0 ⌊ T ⌋ n}) by crush. assert (ᴳ{- h : m0 ⌊ T ⌋ n} (ʰ h) = Some (₋ m0 ⌊ T ⌋ n)). { unfold ctx_singleton; rewrite singleton_MapsTo_at_elt. reflexivity. } specialize (H (ʰ h) (₋ m0 ⌊ T ⌋ n) H1). simpl in H; assumption. }
      pose proof singeq as singeq'. rewrite singeq' in LinOnlyD'.
      rewrite stimes_singleton_dest, mode_times_linnu_l_eq in singeq. apply eq_sym, union_inv_singleton_dest_IsLin in singeq. 2:{ assumption. }
      rewrite D1eq, D0eq, D3eq in *.
      destruct (ctx_split_stimes_union ¹↑ D0 D10 sing0) as (D10' & sing0' & D10eq & singeq0 & D0eq'); trivial. { crush. }
      rewrite D10eq, singeq0, D0eq' in *.
      clear D1eq D1 D3eq D3 D10eq D10 singeq0 sing0 D0eq D0eq' D0 singeq'.
      assert (hnames©( C) ## hnamesᴳ( D6)). { simpl in HDisjointCD3D6. intros name contra. apply HNames.inter_spec in contra. destruct contra as (InC & InD6). contradiction (HDisjointCD3D6 name). apply HNames.inter_spec. split. apply HNames.union_spec. right. assumption. assumption. }
      destruct singeq as [(sing0peq & sing3eq) | (sing0peq & sing3eq)].
      + apply stimes_inv_singleton_dest in sing0peq.
        destruct sing0peq as (m1 & m1eq & sing0peq). rewrite m1eq, sing0peq, sing3eq in *. rewrite <- union_empty_r_eq in *. clear sing0peq sing0' sing3eq sing3.
        assert (~In (ʰ h) D13). { rewrite nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ n). crush. }
        apply nIn_impl_nHin in H2. rewrite <- HNames.mem_spec in H2. destruct (HNames.mem h hnamesᴳ( D13)). congruence.
        replace (¹↑ ᴳ· D10' ᴳ+ D13 ᴳ+ ¹↑ · m1 ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D6)) with (¹↑ ᴳ· (D10' ᴳ+ m1 ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D6)) ᴳ+ D13). 2:{ rewrite stimes_distrib_on_union. rewrite stimes_is_action. rewrite union_swap_2_3_l3. reflexivity. }
        assert ((D10' ᴳ+ ᴳ{- h : m1 ⌊ T ⌋ n} ᴳ+ D4) # D6). { apply HDisjoint_to_Disjoint. crush. apply HSubset_preserves_HDisjoint with (H2 := hnames©( C)). apply (hnames_C_wk_hnames_G _ _ _ _ TyC). assumption. }
        pose proof H3 as H4. apply Disjoint_commutative in H4.
        pose proof DisjointD1D6 as DisjointD1D6'. apply Disjoint_commutative in DisjointD1D6'.
        constructor 21 with (D1 := D10' ᴳ+ m1 ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D6)) (D3 := D13) (U := U) (D2 := D4); swap 8 9; swap 9 10.
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite (hnames_ectxs_fill _ _ _ _ _ _ _ TyC).
        apply HDisjoint_commutative. apply HDisjoint_union_iff; split.
        apply HDisjoint_commutative. apply HDisjoint_wk_remove. assumption.
        apply Disjoint_to_HDisjoint. crush.
        apply hnames_C_wk_hnames_G in TyC.
        repeat rewrite hnames_distrib_on_union in TyC. rewrite hnames_singleton_dest in TyC. repeat rewrite hnames_stimes_eq in TyC.
        assert (HNames.In h (hnamesᴳ( D10') ∪ ᴴ{ h} ∪ hnamesᴳ( D4))). { repeat rewrite HNames.union_spec. left. right. apply HNames.add_spec. left; reflexivity. } specialize (TyC h H5). assumption. }
        replace (ᴳ{- h : m1 ⌊ T ⌋ n}) with (m1 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ n}) in *.
        2:{ rewrite stimes_singleton_dest. rewrite mode_times_linnu_l_eq. reflexivity. }
        replace (D10' ᴳ+ m1 ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D6) ᴳ+ D4) with (D10' ᴳ+ D4 ᴳ+ m1 ᴳ· ᴳ- (n ᴳ· ᴳ-⁻¹ D6)). 2:{ rewrite union_swap_2_3_l3. reflexivity. }
        apply IHC with (m0 := m1).
        { crush. } { crush. } { crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. } rewrite union_swap_2_3_l3. assumption.
      + apply stimes_empty_iff in sing0peq. rewrite sing0peq, sing3eq in *. clear sing0peq sing0' sing3eq sing3.
        replace (m0) with (¹ν) in *. 2:{ rewrite union_commutative in ValidOnlyhiD3. apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & LinNuOnlysingh). specialize (LinNuOnlysingh (ʰ h) (₋ m0 ⌊ T ⌋ n)). unfold ctx_singleton in LinNuOnlysingh. rewrite singleton_MapsTo_at_elt in LinNuOnlysingh. specialize (LinNuOnlysingh eq_refl). simpl in LinNuOnlysingh. inversion LinNuOnlysingh. reflexivity. }
        rewrite <- stimes_linnu_eq in *.
        assert (HNames.mem h hnamesᴳ( D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n}) = true). { apply HNames.mem_spec. rewrite hnames_distrib_on_union. apply HNames.union_spec. right. rewrite hnames_singleton_dest. apply HNames.add_spec. left; reflexivity. }
        rewrite H2; clear H2.
        assert (~HNames.In h hnamesᴳ( D13)). { apply nIn_impl_nHin. apply nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ n). crush. }
        replace (HNames.remove h hnamesᴳ( D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n}) ∪ hnamesᴳ( D6)) with (hnamesᴳ(D13 ᴳ+ ᴳ- (n ᴳ· ᴳ-⁻¹ D6))).
        2:{
          apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros h'.
          repeat rewrite hnames_distrib_on_union. rewrite hnames_hminus_eq. rewrite hnames_stimes_eq. rewrite hnames_hminus_inv_eq. repeat rewrite HNames.union_spec. rewrite HNames.remove_spec. rewrite HNames.union_spec. split.
          { intros Hyp. destruct Hyp as [ InhpD13 | InhpD6 ]. { left. split. left. assumption. intros contra. subst. congruence. } { right. assumption. } }
          { intros Hyp. destruct Hyp as [([InhpD13 | Inhph] & hpneqh) | InhpD6]. { left. assumption. } { rewrite hnames_singleton_dest in Inhph. apply HNames.add_spec in Inhph. destruct Inhph. congruence. inversion H3. } { right. assumption. } }
        }
        rewrite stimes_empty_eq in *. rewrite <- union_empty_r_eq in *.
        rewrite <- union_associative.
        assert ((D10' ᴳ+ D4) # D6). { apply HDisjoint_to_Disjoint. crush. apply HSubset_preserves_HDisjoint with (H2 := hnames©( C)). apply (hnames_C_wk_hnames_G _ _ _ _ TyC). assumption. }
        constructor 21 with (D1 := D10') (D3 := D13 ᴳ+ ᴳ- (n ᴳ· ᴳ-⁻¹ D6)) (U := U) (D2 := (D4)); swap 9 10.
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. apply ValidOnly_hminus_inv_union. crush. apply ValidOnly_hminus. crush. crush. crush. } { assumption. } { rewrite hnames_distrib_on_union in H0. rewrite hnames_distrib_on_union. rewrite hnames_hminus_eq. rewrite hnames_stimes_eq. rewrite hnames_hminus_inv_eq. rewrite <- hnames_distrib_on_union. intros name contra. apply HNames.inter_spec in contra. destruct contra as (InC & InD13). specialize (H0 name). contradiction H0. apply HNames.inter_spec. split. assumption. apply HNames.union_spec. rewrite hnames_distrib_on_union in InD13. apply HNames.union_spec in InD13. specialize (H1 name). rewrite HNames.inter_spec in H1. destruct InD13. left. assumption. assert (HNames.In name hnames©( C) /\ HNames.In name hnamesᴳ( D6)). { split; assumption. } congruence. }
        rewrite hminus_inv_distrib_on_union. repeat rewrite union_associative.
        rewrite hminus_inv_hminus_eq. rewrite union_empty_l_eq with (G := ᴳ-⁻¹ D6).
        apply Ty_val_fill with (T := T); trivial.
        { rewrite <- union_empty_l_eq. assumption. }
        { apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. assumption. } { crush. } { crush. } { crush. } { crush. } { apply Disjoint_commutative. crush. } { crush. } { crush. } { crush. }
        { crush. } { apply ValidOnly_hminus. crush. crush. } { crush. }
Admitted.

Lemma ectxs_fillCtor_spec : forall (D1 D3: ctx) (h : hname) (C : ectxs) (n : mode) (T T' U0 : type) (v : val),
  IsValid n -> 
  DestOnly D1 ->
  DestOnly D3 ->
  D1 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  D3 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  ValidOnly (ᴳ-⁻¹ D3) ->
  D1 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n } ⊣ C : T' ↣ U0 ->
  (ᴳ-⁻¹ D3) ⫦ v : T ->
  D1 ᴳ+ (ᴳ- (n ᴳ· (ᴳ-⁻¹ D3))) ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T' ↣ U0.
Proof.
  intros * Validn DestOnlyD1 DestOnlyD3 DisjointD1D3 DisjointD1h DisjointD3h HDisjointCD3 ValidOnlyhiD3 TyC Tyv.
  rewrite stimes_linnu_eq with (G := ᴳ- (n ᴳ· ᴳ-⁻¹ D3)).
  apply ectxs_fillCtor_spec' with (D3 := D3) (U := T) (n := n); trivial.
  constructor. rewrite <- stimes_linnu_eq. assumption.
Qed.

(* ========================================================================= *)

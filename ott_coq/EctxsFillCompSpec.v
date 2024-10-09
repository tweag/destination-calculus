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

Ltac asserts_fillComp TyC D3 HDisjointCD3 :=
  match type of TyC with
  | (Ty_ectxs ?V ?W ?X ?Y) =>
    let LinOnlyD := fresh TyC "LinOnlyD" in
    let FinAgeOnlyD := fresh TyC "FinAgeOnlyD" in
    let HSubsetDC := fresh TyC "HSubsetDC" in
    let DisjointDD3 := fresh TyC "DisjointDD3" in
    assert (LinOnly V /\ FinAgeOnly V) as (LinOnlyD & FinAgeOnlyD) by
      (apply Ty_ectxs_LinOnly_FinAgeOnly with (C := W) (T := X) (U0 := Y); tauto);
    assert (HNames.Subset hnamesᴳ(V) hnames©(W)) as HSubsetDC by
      (apply hnames_C_wk_hnames_G with (T := X) (U0 := Y); trivial);
    assert (V # D3) as DisjointDD3 by
      (apply HDisjoint_to_Disjoint; [supercrush| apply HSubset_preserves_HDisjoint with (H2 := hnames©( W)); trivial]);
    simpl in HDisjointCD3; rewrite <- hunion_hempty_l_eq in HDisjointCD3
  | ?Z => fail 1 "TyC not of the right shape" Z
  end.

Lemma ectxs_fillComp_spec' : forall (C : ectxs) (h : hname) (v : val) (D2 D3: ctx) (U: type), DestOnly D2 -> DestOnly D3 -> D2 # D3 -> D2 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } -> D3 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  ValidOnly (ᴳ-⁻¹ D3) ->
  D2 ᴳ+ (ᴳ-⁻¹ D3) ⫦ v : U ->
  forall (m0 : mode) (T U0 : type) (D1: ctx),
  IsValid m0 ->
  DestOnly D1 ->
  D1 # D2 ->
  D1 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν }) ⊣ C : T ↣ U0 ->
  D1 ᴳ+ m0 ᴳ· D3 ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T ↣ U0.
Proof.
  intros * DestOnlyD2 DestOnlyD3 DisjointD2D3 DisjointD2h DisjointD3h HDisjointCD3 ValidOnlyhiD3 Tyv. induction C.
  - intros * Validm0 DestOnlyD1 DisjointD1D2 DisjointD1D3 DisjointD1h TyC.
    dependent destruction TyC.
    exfalso.
    assert (ᴳ{}.(underlying) = (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν })).(underlying) ). { unfold union, merge_with, merge, ctx_singleton.  simpl. apply x. } clear x.
    assert (ᴳ{} = (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν }))). { apply ext_eq. intros n'. rewrite H. reflexivity. }
    rewrite stimes_distrib_on_union, union_associative in *.
    apply eq_sym in H0.
    apply union_empty_iff in H0. destruct H0 as (_ & contra). rewrite stimes_empty_iff in contra. assert (ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν} (ʰ h) = None). { rewrite contra. simpl. reflexivity. } unfold ctx_singleton in H0. rewrite singleton_MapsTo_at_elt in H0. inversion H0.
  - intros * Validm0 DestOnlyD1 DisjointD1D2 DisjointD1D3 DisjointD1h TyC.
    destruct a; simpl; dependent destruction TyC.
    20:{ (* Ty-ectxs-OpenAmpar *)
      rename D3 into D6, D4 into D3, D5 into D4, DestOnlyD3 into DestOnlyD6, ValidOnlyhiD3 into ValidOnlyhiD6, DisjointD3h into DisjointD6h, DisjointD2D3 into DisjointD2D6, HDisjointCD3 into HDisjointCD3D6, DisjointD1D3 into DisjointD1D6, DestOnlyD5 into DestOnlyD3, U into T, U1 into U, ValidOnlyhiD0 into ValidOnlyhiD3.
      assert ((¹↑ ᴳ· D0 ᴳ+ D3).(underlying) = (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ ¹ν})).(underlying)). { unfold union, merge_with, merge, ctx_singleton. simpl. apply x. } clear x.
      assert ((¹↑ ᴳ· D0 ᴳ+ D3) = (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ ¹ν}))). { apply ext_eq. intros n'. rewrite H. reflexivity. }
      assert (LinOnly (D0 ᴳ+ D4) /\ FinAgeOnly (D0 ᴳ+ D4)) as (LinOnlyD & FinAgeOnlyD).
        { apply Ty_ectxs_LinOnly_FinAgeOnly with (C := C) (T := U ⧔ T') (U0 := U0). tauto. }
      clear H. rename H1 into ctx_eq.
      pose proof ValidOnlyhiD3 as ValidOnlyhiD3'. apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3'. destruct ValidOnlyhiD3' as (_ & ValidOnlyD3). pose proof ValidOnlyD3 as LinOnlyD3. pose proof ValidOnlyD3 as FinAgeOnlyD3. apply LinNuOnly_wk_LinOnly in LinOnlyD3, ValidOnlyD3. apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD3. apply LinOnly_wk_ValidOnly in ValidOnlyD3.
      assert (LinOnly (¹↑ ᴳ· D0 ᴳ+ D3) /\ FinAgeOnly (¹↑ ᴳ· D0 ᴳ+ D3)) as (LinOnlyD' & FinAgeOnlyD'). split.
        { supercrush. } { supercrush. }
      rewrite ctx_eq in LinOnlyD', FinAgeOnlyD'.
      rewrite stimes_distrib_on_union in ctx_eq. rewrite stimes_is_action in ctx_eq.
      destruct (ctx_split_union_union_3 (¹↑ ᴳ· D0) D3 D1 ((m0 · ¹↑) ᴳ· D2) (m0 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ ¹ν})) as (D10 & D13 & D20 & D23 & sing0 & sing3 & D1eq & D2eq & singeq & D0eq & D3eq).
        { crush. } { crush. } { crush. } { crush. }
      assert (IsLin m0). { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite stimes_singleton_dest in LinOnlyD'. rewrite mode_times_linnu_l_eq in LinOnlyD'. assert (LinOnly ᴳ{- h : m0 ⌊ T ⌋ ¹ν}) by crush. assert (ᴳ{- h : m0 ⌊ T ⌋ ¹ν} (ʰ h) = Some (₋ m0 ⌊ T ⌋ ¹ν)). { unfold ctx_singleton; rewrite singleton_MapsTo_at_elt. reflexivity. } specialize (H (ʰ h) (₋ m0 ⌊ T ⌋ ¹ν) H1). simpl in H; assumption. }
      pose proof singeq as singeq'.
      rewrite stimes_singleton_dest, mode_times_linnu_l_eq in singeq. apply eq_sym, union_inv_singleton_dest_IsLin in singeq. 2:{ assumption. }
      rewrite D1eq, D2eq, D0eq, D3eq in *.
      destruct (ctx_split_stimes_union (m0 · ¹↑) D2 D20 D23) as (D20' & D23' & D20eq & D23eq & D2eq'). { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite stimes_is_action in LinOnlyD'. rewrite D2eq in LinOnlyD'. crush. } { assumption. } rewrite D20eq, D23eq, D2eq' in *.
      destruct (ctx_split_stimes_union_3 ¹↑ D0 D10 (m0 · ¹↑ ᴳ· D20') sing0) as (D10' & D20'' & sing0' & D10eq & D20eq' & singeq0 & D0eq'); trivial. { crush. } { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite singeq' in LinOnlyD'. crush. } { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite singeq' in LinOnlyD'. crush. } rewrite D10eq, singeq0, D0eq' in *.
      rewrite mode_times_commutative with (m := m0) in D20eq'. rewrite <- stimes_is_action with (m := ¹↑) in D20eq'.
      rewrite stimes_linone_equal_iff in D20eq'. rewrite <- D20eq' in *.
      clear D20eq' D20''. clear D1eq D1 D2eq D2eq' D2 D3eq D3 D20eq D20 D23eq D23 D10eq D10 singeq0 sing0 D0eq D0eq' D0 singeq'.
      assert (D23' = ᴳ{}). { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & LinNuOnlyhiD3).
        apply LinNuOnly_union_iff in LinNuOnlyhiD3. destruct LinNuOnlyhiD3 as (_ & contra & _).
        apply LinNuOnly_union_iff in contra. destruct contra as (contra & _ & _).
        rewrite mode_times_commutative in contra. rewrite <- stimes_is_action in contra. apply LinNuOnly_stimes_linone_contra in contra. rewrite stimes_empty_iff in contra. assumption. } rewrite H1 in *. clear H1 D23'. rewrite stimes_empty_eq in *. rewrite <- union_empty_r_eq in *. rewrite <- union_empty_l_eq in *.
      assert (hnames©( C) ## hnamesᴳ( D6)). { simpl in HDisjointCD3D6. intros n contra. apply HNames.inter_spec in contra. destruct contra as (InC & InD6). contradiction (HDisjointCD3D6 n). apply HNames.inter_spec. split. apply HNames.union_spec. right. assumption. assumption. }
      destruct singeq as [(sing0peq & sing3eq) | (sing0peq & sing3eq)].
      + apply stimes_inv_singleton_dest in sing0peq.
        destruct sing0peq as (m1 & m1eq & sing0peq). rewrite m1eq, sing0peq, sing3eq in *. rewrite <- union_empty_r_eq in *.
        assert (~In (ʰ h) D13). { rewrite nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ ¹ν). crush. }
        apply nIn_impl_nHin in H2. rewrite <- HNames.mem_spec in H2. destruct (HNames.mem h hnamesᴳ( D13)). congruence.
        replace (¹↑ ᴳ· D10' ᴳ+ D13 ᴳ+ ¹↑ · m1 ᴳ· D6) with (¹↑ ᴳ· (D10' ᴳ+ m1 ᴳ· D6) ᴳ+ D13). 2:{ rewrite stimes_distrib_on_union. rewrite stimes_is_action. rewrite union_swap_2_3_l3. reflexivity. }
        assert ((D10' ᴳ+ (¹↑ · m1 ᴳ· D20' ᴳ+ ᴳ{- h : m1 ⌊ T ⌋ ¹ν}) ᴳ+ D4) # D6). { apply HDisjoint_to_Disjoint. crush. apply HSubset_preserves_HDisjoint with (H2 := hnames©( C)). apply (hnames_C_wk_hnames_G _ _ _ _ TyC). assumption. }
        pose proof H3 as H4. apply Disjoint_commutative in H4.
        pose proof DisjointD1D6 as DisjointD1D6'. apply Disjoint_commutative in DisjointD1D6'.
        constructor 21 with (D1 := D10' ᴳ+ m1 ᴳ· D6) (D3 := D13) (U := U) (D2 := D4); swap 8 9; swap 9 10.
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite (hnames_ectxs_fill _ _ _ _ _ _ _ TyC).
        apply HDisjoint_commutative. apply HDisjoint_union_iff; split.
        apply HDisjoint_commutative. apply HDisjoint_wk_remove. assumption.
        apply Disjoint_to_HDisjoint. crush.
        apply hnames_C_wk_hnames_G in TyC.
        repeat rewrite hnames_distrib_on_union in TyC. rewrite hnames_singleton_dest in TyC. repeat rewrite hnames_stimes_eq in TyC.
        assert (HNames.In h (hnamesᴳ( D10') ∪ (hnamesᴳ( D20') ∪ ᴴ{ h}) ∪ hnamesᴳ( D4))). { repeat rewrite HNames.union_spec. left. right. right. apply HNames.add_spec. left; reflexivity. } specialize (TyC h H5). assumption. }
        replace (ᴳ{- h : m1 ⌊ T ⌋ ¹ν}) with (m1 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ ¹ν}) in *.
        2:{ rewrite stimes_singleton_dest. rewrite mode_times_linnu_l_eq. reflexivity. }
        replace ((¹↑ · m1) ᴳ· D20') with (m1 ᴳ· (¹↑ ᴳ· D20')) in *.
        rewrite <- stimes_distrib_on_union with (m := m1) in *.
        2:{ rewrite stimes_is_action. rewrite mode_times_commutative with (n := m1). reflexivity. }
        replace (D10' ᴳ+ m1 ᴳ· D6 ᴳ+ D4) with (D10' ᴳ+ D4 ᴳ+ m1 ᴳ· D6). 2:{ rewrite union_swap_2_3_l3. reflexivity. }
        apply IHC with (m0 := m1).
        { crush. } { crush. } { crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. } { crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. } rewrite union_swap_2_3_l3. assumption.
      + apply stimes_empty_iff in sing0peq. rewrite sing0peq, sing3eq in *. clear sing0peq sing0' sing3eq sing3.
        replace (m0) with (¹ν) in *. 2:{ rewrite union_commutative in ValidOnlyhiD3. apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & LinNuOnlysingh). specialize (LinNuOnlysingh (ʰ h) (₋ m0 ⌊ T ⌋ ¹ν)). unfold ctx_singleton in LinNuOnlysingh. rewrite singleton_MapsTo_at_elt in LinNuOnlysingh. specialize (LinNuOnlysingh eq_refl). simpl in LinNuOnlysingh. inversion LinNuOnlysingh. reflexivity. }
        rewrite mode_times_linnu_l_eq in *. rewrite <- stimes_linnu_eq in *.
        assert (HNames.mem h hnamesᴳ( D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ ¹ν}) = true). { apply HNames.mem_spec. rewrite hnames_distrib_on_union. apply HNames.union_spec. right. rewrite hnames_singleton_dest. apply HNames.add_spec. left; reflexivity. }
        rewrite H2; clear H2.
        assert (~HNames.In h hnamesᴳ( D13)). { apply nIn_impl_nHin. apply nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ ¹ν). crush. }
        replace (HNames.remove h hnamesᴳ( D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ ¹ν}) ∪ hnamesᴳ( D6)) with (hnamesᴳ(D13 ᴳ+ D6)).
        2:{
          apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros h'.
          repeat rewrite hnames_distrib_on_union. repeat rewrite HNames.union_spec. rewrite HNames.remove_spec. rewrite HNames.union_spec. split.
          { intros Hyp. destruct Hyp as [ InhpD13 | InhpD6 ]. { left. split. left. assumption. intros contra. subst. congruence. } { right. assumption. } }
          { intros Hyp. destruct Hyp as [([InhpD13 | Inhph] & hpneqh) | InhpD6]. { left. assumption. } { rewrite hnames_singleton_dest in Inhph. apply HNames.add_spec in Inhph. destruct Inhph. congruence. inversion H3. } { right. assumption. } }
        }
        rewrite stimes_empty_eq in *. rewrite <- union_empty_r_eq in *.
        rewrite <- union_associative.
        assert ((D10' ᴳ+ D20' ᴳ+ D4) # D6). { apply HDisjoint_to_Disjoint. crush. apply HSubset_preserves_HDisjoint with (H2 := hnames©( C)). apply (hnames_C_wk_hnames_G _ _ _ _ TyC). assumption. }
        constructor 21 with (D1 := D10') (D3 := D13 ᴳ+ D6) (U := U) (D2 := (D20' ᴳ+ D4)); swap 9 10.
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. apply ValidOnly_hminus_inv_union; crush. } { rewrite union_associative. assumption. } { rewrite hnames_distrib_on_union in H0. intros name contra. apply HNames.inter_spec in contra. destruct contra as (InC & InD13). specialize (H0 name). contradiction H0. apply HNames.inter_spec. split. assumption. apply HNames.union_spec. rewrite hnames_distrib_on_union in InD13. apply HNames.union_spec in InD13. specialize (H1 name). rewrite HNames.inter_spec in H1. destruct InD13. left. assumption. assert (HNames.In name hnames©( C) /\ HNames.In name hnamesᴳ( D6)). { split; assumption. } congruence. }
        rewrite hminus_inv_distrib_on_union. repeat rewrite union_associative.
        rewrite union_swap_1_3_l4. rewrite union_swap_1_2_l4.
        rewrite <- union_associative. rewrite stimes_linnu_eq with (G := D20' ᴳ+ ᴳ-⁻¹ D6).
        apply Ty_val_fill with (T := T); trivial.
        { apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. assumption. }
        { crush. } { crush. } { apply Disjoint_commutative. crush. } { crush. } { apply Disjoint_commutative. crush. } { apply Disjoint_commutative. crush. } { crush. } { crush. } { crush. }
    }
    all: asserts_fillComp TyC D3 HDisjointCD3; rename TyCLinOnlyD into LinOnlyD, TyCFinAgeOnlyD into FinAgeOnlyD, TyCHSubsetDC into HSubsetDC, TyCDisjointDD3 into DisjointDD3.
    * (* Ty-ectxs-App1 *)
      constructor 2 with (7 := Tytp); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-App2 *)
      constructor 3 with (7 := Tyv0); first last.
      rewrite union_associative.
      rewrite union_associative in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatU *)
      constructor 4 with (6 := Tyu); first last.
      rewrite union_swap_2_3_l3.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatS *)
      constructor 5 with (7 := Tyu1) (8 := Tyu2); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatP *)
      constructor 6 with (8 := Tyu); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatE *)
      constructor 7 with (8 := Tyu); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-Map *)
      constructor 8 with (6 := Tytp); first last.
      rewrite union_swap_2_3_l3.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-ToA *)
      constructor 9; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FromA *)
      constructor 10; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FillU *)
      constructor 11; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FillL *)
      constructor 12; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FillR *)
      constructor 13; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FillE *)
      constructor 15; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FillP *)
      constructor 14; first last. apply IHC; first last. all: trivial.
    * (* Ty-ectxs-FillF *)
      constructor 16 with (8 := Tyu); first last.
      rewrite union_swap_2_3_l3.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-FillComp1 *)
      constructor 17 with (6 := Tytp); first last.
      rewrite union_swap_2_3_l3.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-FillComp2 *)
      constructor 18 with (6 := Tyt); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_associative, union_swap_1_2_l3.
      rewrite stimes_distrib_on_union, stimes_is_action, union_associative, union_swap_1_2_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-FillLeaf1 *)
      constructor 19 with (7 := Tytp); first last.
      rewrite union_swap_2_3_l3.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC; first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-FillLeaf2 *)
      constructor 20 with (7 := Tyt); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_associative, union_swap_1_2_l3.
      rewrite stimes_distrib_on_union, stimes_is_action, union_associative, union_swap_1_2_l3 in TyC.
      apply IHC; first last. all: trivial.
      all: replace (mode_times' ((cons ¹↑ nil) ++ (cons n nil) ++ nil)) with (¹↑ · n) in * by ( cbn; rewrite mode_times_linnu_r_eq; reflexivity).
      all: supercrush.
Qed.

Lemma ectxs_fillComp_spec : forall (D1 D2 D3: ctx) (h : hname) (C : ectxs) (T U U0 : type) (v : val),
  DestOnly D1 ->
  DestOnly D2 ->
  DestOnly D3 ->
  D1 # D2 ->
  D1 # D3 ->
  D2 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  D2 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  D3 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  ValidOnly (ᴳ-⁻¹ D3) ->
  D1 ᴳ+ ¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ⊣ C : T ↣ U0 ->
  D2 ᴳ+ (ᴳ-⁻¹ D3) ⫦ v : U ->
  D1 ᴳ+ D3 ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T ↣ U0.
Proof.
  intros * DestOnlyD1 DestOnlyD2 DestOnlyD3 DisjointD1D2 DisjointD1D3 DisjointD2D3 DisjointD1h DisjointD2h DisjointD3h HDisjointCD3 ValidOnlyhiD3 TyC Tyv. rewrite 1 stimes_linnu_eq with (G := D3). rewrite hnames_stimes_eq. apply ectxs_fillComp_spec' with (U := U) (D2 := D2); trivial. apply IsValid_linnu'. rewrite <- stimes_linnu_eq. rewrite union_associative. assumption.
Qed.

(* ========================================================================= *)

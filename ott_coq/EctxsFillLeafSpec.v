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

Ltac asserts_fillLeaf TyC :=
  match type of TyC with
  | (Ty_ectxs ?V ?W ?X ?Y) =>
    let LinOnlyD := fresh TyC "LinOnlyD" in
    let FinAgeOnlyD := fresh TyC "FinAgeOnlyD" in
    let HSubsetDC := fresh TyC "HSubsetDC" in
    assert (LinOnly V /\ FinAgeOnly V) as (LinOnlyD & FinAgeOnlyD) by
      (apply Ty_ectxs_LinOnly_FinAgeOnly with (C := W) (T := X) (U0 := Y); tauto);
    assert (HNames.Subset hnamesᴳ(V) hnames©(W)) as HSubsetDC by
      (apply hnames_C_wk_hnames_G with (T := X) (U0 := Y); trivial)
  | ?Z => fail 1 "TyC not of the right shape" Z
  end.

Lemma ectxs_fillLeaf_spec' : forall (C : ectxs) (h : hname) (v : val) (D2 : ctx) (T: type) (n : mode), IsValid n -> DestOnly D2 -> D2 # ᴳ{- h : ¹ν ⌊ T ⌋ n } -> D2 ⫦ v : T ->
  forall (m0 : mode) (U U0 : type) (D1: ctx),
  IsValid m0 ->
  DestOnly D1 ->
  D1 # D2 ->
  D1 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  D1 ᴳ+ m0 ᴳ· ((¹↑ · n) ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n }) ⊣ C : U ↣ U0 ->
  D1 ⊣ C ©️[ h ≔ HNames.empty ‗ v ] : U ↣ U0.
Proof.
  intros * Validn DestOnlyD2 DisjointD2h Tyv. induction C.
  - intros * Validm0 DestOnlyD1 DisjointD1D2 DisjointD1h TyC.
    assert (ᴳ{} = D1 ᴳ+ m0 ᴳ· (¹↑ · n ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n})). { dependent destruction TyC. unfold ctx_singleton, singleton, union, hminus_inv, merge_with, merge; cbn. apply ext_eq'. cbn. rewrite x. reflexivity. }
    assert (In (ʰ h) ᴳ{}). { rewrite H. apply In_union_iff. right. rewrite  stimes_distrib_on_union. apply In_union_iff. right. repeat rewrite In_stimes_iff. apply In_singleton_iff. reflexivity. }
    destruct H0 as (b & contra). simpl in contra. congruence.
  - intros * Validm0 DestOnlyD1 DisjointD1D2 DisjointD1h TyC.
    destruct a; simpl; dependent destruction TyC.
    20: { (* Ty-ectxs-OpenAmpar *)
      assert ((¹↑ ᴳ· D0 ᴳ+ D3).(underlying) = (D1 ᴳ+ m0 ᴳ· (¹↑ · n ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n})).(underlying)). { unfold union, merge_with, merge, ctx_singleton. simpl. apply x. } clear x.
      assert (¹↑ ᴳ· D0 ᴳ+ D3 = D1 ᴳ+ m0 ᴳ· (¹↑ · n ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n})). { apply ext_eq. intros n'. rewrite H. reflexivity. }
      assert (LinOnly (D0 ᴳ+ D4) /\ FinAgeOnly (D0 ᴳ+ D4)) as (LinOnlyD & FinAgeOnlyD).
        { apply Ty_ectxs_LinOnly_FinAgeOnly with (C := C) (T := U ⧔ T') (U0 := U0). tauto. }
      clear H. rename H1 into ctx_eq.
      pose proof ValidOnlyhiD3 as ValidOnlyhiD3'. apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3'. destruct ValidOnlyhiD3' as (_ & ValidOnlyD3). pose proof ValidOnlyD3 as LinOnlyD3. pose proof ValidOnlyD3 as FinAgeOnlyD3. apply LinNuOnly_wk_LinOnly in LinOnlyD3, ValidOnlyD3. apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD3. apply LinOnly_wk_ValidOnly in ValidOnlyD3.
      assert (LinOnly (¹↑ ᴳ· D0 ᴳ+ D3) /\ FinAgeOnly (¹↑ ᴳ· D0 ᴳ+ D3)) as (LinOnlyD' & FinAgeOnlyD'). split.
        { supercrush. } { supercrush. }
      rewrite ctx_eq in LinOnlyD', FinAgeOnlyD'.
      rewrite stimes_distrib_on_union in ctx_eq. rewrite stimes_is_action in ctx_eq.
      destruct (ctx_split_union_union_3 (¹↑ ᴳ· D0) D3 D1 (m0 · ¹↑ · n ᴳ· D2) (m0 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ n})) as (D10 & D13 & D20 & D23 & sing0 & sing3 & D1eq & D2eq & singeq & D0eq & D3eq).
        { crush. } { crush. } { crush. } { crush. }
      assert (IsLin m0). { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite stimes_singleton_dest in LinOnlyD'. rewrite mode_times_linnu_l_eq in LinOnlyD'. assert (LinOnly ᴳ{- h : m0 ⌊ T ⌋ n}) by crush. assert (ᴳ{- h : m0 ⌊ T ⌋ n} (ʰ h) = Some (₋ m0 ⌊ T ⌋ n)). { unfold ctx_singleton; rewrite singleton_MapsTo_at_elt. reflexivity. } specialize (H (ʰ h) (₋ m0 ⌊ T ⌋ n) H1). simpl in H; assumption. }
      pose proof singeq as singeq'.
      rewrite stimes_singleton_dest, mode_times_linnu_l_eq in singeq. apply eq_sym, union_inv_singleton_dest_IsLin in singeq. 2:{ assumption. }
      rewrite D1eq, D2eq, D0eq, D3eq in *.
      destruct (ctx_split_stimes_union (m0 · ¹↑ · n) D2 D20 D23) as (D20' & D23' & D20eq & D23eq & D2eq'). { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite stimes_is_action in LinOnlyD'. rewrite D2eq in LinOnlyD'. crush. } { assumption. } rewrite D20eq, D23eq, D2eq' in *.
      destruct (ctx_split_stimes_union_3 ¹↑ D0 D10 (m0 · ¹↑ · n ᴳ· D20') sing0) as (D10' & D20'' & sing0' & D10eq & D20eq' & singeq0 & D0eq'); trivial. { crush. } { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite singeq' in LinOnlyD'. crush. } { rewrite stimes_distrib_on_union in LinOnlyD'. rewrite singeq' in LinOnlyD'. crush. } rewrite D10eq, singeq0, D0eq' in *.
      rewrite mode_times_commutative with (m := m0) in D20eq'. rewrite <- mode_times_associative in D20eq'. rewrite mode_times_commutative with (m := n) in D20eq'. rewrite <- stimes_is_action with (m := ¹↑) in D20eq'.
      rewrite stimes_linone_equal_iff in D20eq'. rewrite <- D20eq' in *.
      clear D20eq' D20''. clear D1eq D1 D2eq D2eq' D2 D3eq D3 D20eq D20 D23eq D23 D10eq D10 singeq0 sing0 D0eq D0eq' D0 singeq'.
      assert (D23' = ᴳ{}). { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & LinNuOnlyhiD3).
        apply LinNuOnly_union_iff in LinNuOnlyhiD3. destruct LinNuOnlyhiD3 as (_ & contra & _).
        apply LinNuOnly_union_iff in contra. destruct contra as (contra & _ & _).
        rewrite mode_times_commutative in contra. rewrite <- mode_times_associative in contra. rewrite <- stimes_is_action in contra. apply LinNuOnly_stimes_linone_contra in contra. rewrite stimes_empty_iff in contra. assumption. } rewrite H1 in *. clear H1 D23'. rewrite stimes_empty_eq in *. rewrite <- union_empty_r_eq in *. rewrite <- union_empty_l_eq in *.
      destruct singeq as [(sing0peq & sing3eq) | (sing0peq & sing3eq)].
      + apply stimes_inv_singleton_dest in sing0peq.
        destruct sing0peq as (m1 & m1eq & sing0peq). rewrite m1eq, sing0peq, sing3eq in *. rewrite <- union_empty_r_eq in *.
        assert (~In (ʰ h) D13). { rewrite nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ n). crush. }
        apply nIn_impl_nHin in H1. rewrite <- HNames.mem_spec in H1. destruct (HNames.mem h hnamesᴳ( D13)). congruence.
        constructor 21 with (D1 := D10') (D3 := D13) (U := U) (D2 := D4); swap 8 9; swap 9 10.
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite (hnames_ectxs_fill _ _ _ _ _ _ _ TyC). rewrite <- hunion_hempty_r_eq. unfold HDisjoint. intros name contra. apply HNames.inter_spec in contra. destruct contra as (InrC & InD13). rewrite HNames.remove_spec in InrC. destruct InrC as (InC & _). specialize (H0 name). contradiction H0. apply HNames.inter_spec. split; assumption. apply hnames_C_wk_hnames_G in TyC. repeat rewrite hnames_distrib_on_union in TyC. repeat rewrite hnames_stimes_eq in TyC. rewrite hnames_singleton_dest in TyC. assert (HNames.In h (hnamesᴳ( D10') ∪ (hnamesᴳ( D20') ∪ ᴴ{ h}) ∪ hnamesᴳ( D4))). { repeat rewrite HNames.union_spec. left. right. right. apply HNames.add_spec. left; reflexivity. } specialize (TyC h H2). assumption. }
        assert (LinOnly (D10' ᴳ+ ((¹↑ · m1) · n ᴳ· D20' ᴳ+ ᴳ{- h : m1 ⌊ T ⌋ n}) ᴳ+ D4) /\ FinAgeOnly (D10' ᴳ+ ((¹↑ · m1) · n ᴳ· D20' ᴳ+ ᴳ{- h : m1 ⌊ T ⌋ n}) ᴳ+ D4)) as (LinOnlyD'' & FinAgeOnlyD'').
        { apply Ty_ectxs_LinOnly_FinAgeOnly with (C := C) (T := U ⧔ T') (U0 := U0). tauto. }
        replace (ᴳ{- h : m1 ⌊ T ⌋ n}) with (m1 ᴳ· ᴳ{- h : ¹ν ⌊ T ⌋ n}) in *.
        2:{ rewrite stimes_singleton_dest. rewrite mode_times_linnu_l_eq. reflexivity. }
        replace ((¹↑ · m1) · n ᴳ· D20') with (m1 ᴳ· ((¹↑ · n) ᴳ· D20')) in *.
        rewrite <- stimes_distrib_on_union with (m := m1) in *.
        2:{ rewrite stimes_is_action. rewrite mode_times_commutative with (n := m1). rewrite mode_times_associative. reflexivity. }
        apply IHC with (m0 := m1).
        { crush. } { crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. } { apply Disjoint_union_l_iff; split. crush. apply Disjoint_commutative. crush. } rewrite union_swap_2_3_l3. assumption.
      + apply stimes_empty_iff in sing0peq. rewrite sing0peq, sing3eq in *. clear sing0peq sing0' sing3eq sing3.
        replace (m0) with (¹ν) in *. 2:{ rewrite union_commutative in ValidOnlyhiD3. apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & LinNuOnlysingh). specialize (LinNuOnlysingh (ʰ h) (₋ m0 ⌊ T ⌋ n)). unfold ctx_singleton in LinNuOnlysingh. rewrite singleton_MapsTo_at_elt in LinNuOnlysingh. specialize (LinNuOnlysingh eq_refl). simpl in LinNuOnlysingh. inversion LinNuOnlysingh. reflexivity. }
        rewrite mode_times_linnu_l_eq in *. rewrite <- stimes_linnu_eq in *.
        assert (HNames.mem h hnamesᴳ( D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n}) = true). { apply HNames.mem_spec. rewrite hnames_distrib_on_union. apply HNames.union_spec. right. rewrite hnames_singleton_dest. apply HNames.add_spec. left; reflexivity. }
        rewrite H1; clear H1.
        assert (~HNames.In h hnamesᴳ( D13)). { apply nIn_impl_nHin. apply nIn_iff_Disjoint_singleton with (n := ʰ h) (binding := ₋ ¹ν ⌊ T ⌋ n). crush. }
        replace (HNames.remove h hnamesᴳ( D13 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n}) ∪ HNames.empty) with (hnamesᴳ(D13)).
        2:{
          apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros h'.
          rewrite hnames_distrib_on_union. repeat rewrite HNames.union_spec. rewrite HNames.remove_spec. rewrite HNames.union_spec. split.
          { intros InhpD13. left. split. left. assumption. intros contra. subst. congruence. }
          { intros Hyp. destruct Hyp as [([InhpD13 | Inhph] & hpneqh) | Inhpempty]. { assumption. } { rewrite hnames_singleton_dest in Inhph. apply HNames.add_spec in Inhph. destruct Inhph. congruence. inversion H2. } { inversion Inhpempty. } }
        }
        rewrite stimes_empty_eq in *. rewrite <- union_empty_r_eq in *.
        rewrite <- union_associative in TyC.
        constructor 21 with (D1 := D10') (D3 := D13) (U := U) (D2 := (n ᴳ· D20' ᴳ+ D4)); swap 9 10.
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. assumption. } { assumption. } { rewrite hnames_distrib_on_union in H0. intros name contra. apply HNames.inter_spec in contra. destruct contra as (InC & InD13). specialize (H0 name). contradiction H0. apply HNames.inter_spec. split. assumption. apply HNames.union_spec. left. assumption. }
        rewrite <- union_associative. rewrite union_commutative.
        replace (D20') with (D20' ᴳ+ ᴳ-⁻¹ ᴳ{}). 2:{ rewrite hminus_inv_empty_eq. rewrite union_empty_r_eq. reflexivity. }
        replace (HNames.empty) with (hnamesᴳ(ᴳ{})). 2:{ apply hnames_empty_is_hempty. }
        apply Ty_val_fill with (T := T).
        { rewrite hminus_inv_empty_eq. rewrite <- union_empty_r_eq. assumption. }
        { apply ValidOnly_hminus_inv_wk_l in ValidOnlyhiD3. assumption. }
        { crush. } { crush. } { crush. } { apply Disjoint_commutative. crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { assumption. }
    }
    all: asserts_fillLeaf TyC; rename TyCLinOnlyD into LinOnlyD, TyCFinAgeOnlyD into FinAgeOnlyD, TyCHSubsetDC into HSubsetDC.
    * (* Ty-ectxs-App1 *)
      constructor 2 with (7 := Tytp); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-App2 *)
      constructor 3 with (7 := Tyv0); first last.
      rewrite union_associative in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatU *)
      constructor 4 with (6 := Tyu); first last.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatS *)
      constructor 5 with (7 := Tyu1) (8 := Tyu2); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatP *)
      constructor 6 with (8 := Tyu); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-PatE *)
      constructor 7 with (8 := Tyu); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-UpdA *)
      constructor 8 with (6 := Tytp); first last.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-ToA *)
      constructor 9; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FromA *)
      constructor 10; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FillU *)
      constructor 11; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FillL *)
      constructor 12; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FillR *)
      constructor 13; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FillE *)
      constructor 15; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FillP *)
      constructor 14; first last. apply IHC with (5 := TyC); first last. all: trivial.
    * (* Ty-ectxs-FillF *)
      constructor 16 with (8 := Tyu); first last.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial.
      all: replace (mode_times' ((cons ¹↑ nil) ++ (cons n0 nil) ++ nil)) with (¹↑ · n0) in * by ( cbn; rewrite mode_times_linnu_r_eq; reflexivity).
      all: autorewrite with propagate_down in *; try repeat split.
      all: supercrush.
    * (* Ty-ectxs-FillComp1 *)
      constructor 17 with (6 := Tytp); first last.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-FillComp2 *)
      constructor 18 with (6 := Tyt); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_associative in TyC.
      apply IHC with (5 := TyC); first last. all: trivial. all: supercrush.
    * (* Ty-ectxs-FillLeaf1 *)
      constructor 19 with (7 := Tytp); first last.
      rewrite union_swap_2_3_l3 in TyC.
      apply IHC with (5 := TyC); first last. all: trivial.
      all: replace (mode_times' ((cons ¹↑ nil) ++ (cons n0 nil) ++ nil)) with (¹↑ · n0) in * by ( cbn; rewrite mode_times_linnu_r_eq; reflexivity).
      all: supercrush.
    * (* Ty-ectxs-FillLeaf2 *)
      constructor 20 with (7 := Tyt); first last.
      rewrite stimes_distrib_on_union, stimes_is_action, union_associative in TyC.
      apply IHC with (5 := TyC); first last. all: trivial.
      all: replace (mode_times' ((cons ¹↑ nil) ++ (cons n0 nil) ++ nil)) with (¹↑ · n0) in * by ( cbn; rewrite mode_times_linnu_r_eq; reflexivity).
      all: supercrush.
Qed.

Lemma ectxs_fillLeaf_spec : forall (D1 D2: ctx) (h : hname) (C : ectxs) (n : mode) (T U0 : type) (v : val),
  IsValid n ->
  DestOnly D1 ->
  DestOnly D2 ->
  D1 # D2 ->
  D1 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  D2 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  D1 ᴳ+ (¹↑ · n) ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n } ⊣ C : ① ↣ U0 ->
  D2 ⫦ v : T ->
  D1 ⊣ C ©️[ h ≔ HNames.empty ‗ v ] : ① ↣ U0.
Proof.
  intros * Validn DestOnlyD1 DestOnlyD2 DisjointD1D2 DisjointD1h DisjointD2h TyC Tyv.
  apply ectxs_fillLeaf_spec' with (D2 := D2) (T := T) (n := n) (m0 := ¹ν); trivial. crush. rewrite <- stimes_linnu_eq. rewrite union_associative. assumption.
Qed.

(* ========================================================================= *)

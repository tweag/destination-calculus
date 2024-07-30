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
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Dest.destination_calculus_proofs.

Ltac assert_LinOnly_FinAgeOnly_remove_Disposable G G' C T U0 P DisposP :=
  assert (LinOnly G /\ FinAgeOnly G) as (LinOnlyD & FinAgeOnlyD) by (apply (Ty_ectxs_LinOnly_FinAgeOnly (G) C T U0); tauto);
  assert (LinOnly (P ᴳ+ G')) as LinOnlyD' by (crush);
  rewrite (nDisposable_in_LinOnly P G' DisposP LinOnlyD') in *.

(* ⬇️ for the `impl` relation. *)

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & _Redj). destruct Tyj. destruct _Redj.
    - (* Focus-App1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := T) (t := t); swap 1 3. constructor 2 with (D2 := D2) (m := m) (t' := t') (U := U).
      all: crush.
    - (* Unfocus-App1 *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ D1) ᴳ+ D2) D1 C U U0 P DisposP.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ t' $ ᵥ₎ v : U) as TyApp.
        { apply (Ty_term_App m D1 D2 t' (ᵥ₎ v) U T); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := t' $ ᵥ₎ v).
      all: crush.
    - (* Focus-App2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
        constructor 1 with (D := D2) (T := T ⁔ m → U) (t := t'); swap 1 3. constructor 3 with (D1 := D1) (m := m) (v := v) (T := T) (U := U).
      all: crush.
    - (* Unfocus-App2 *)
      inversion Tyt; subst. rename Tyv into Tyvp, TyC into TyCc, D0 into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tytp, Tyv into Tyt, T0 into T.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· D1 ᴳ+ (P ᴳ+ D2)) D2 C U U0 P DisposP.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v' $ ᵥ₎ v : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v') (ᵥ₎ v) U T); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := (ᵥ₎ v') $ (ᵥ₎ v)).
      all: crush.
    - (* Red-App *)
      inversion Tyt; subst.
      assert (m = m0) as Eqmm0.
        { inversion_clear Tytp; inversion_clear Tyv; tauto. }
      rewrite <- Eqmm0 in *. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tytp; subst. clear H1. rename Tyv into Tyv', D into D2.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· D1 ᴳ+ (P ᴳ+ D2)) D2 C U U0 P DisposP.
      inversion Tyv'; subst. rename H1 into DestOnlyD2.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u ᵗ[ x ≔ v] : U) as Tyusub.
      { apply (term_sub_spec_1 D1 D2 m T U u x v). all: crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u ᵗ[ x ≔ v]).
      all: crush.
    - (* Focus-PatU *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (D1 ᴳ+ D2) C T2 U0); tauto. }
        constructor 1 with (D := D1) (T := ①) (t := t); swap 1 3. constructor 4 with (D2 := D2) (U := T2) (u := u). all: crush.
    - (* Unfocus-PatU *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename U into T2.
      assert_LinOnly_FinAgeOnly_remove_Disposable ((P ᴳ+ D1) ᴳ+ D2) D1 C T2 U0 P DisposP.
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ v ᵗ; u : T2) as TyPat.
        { apply (Ty_term_PatU D1 D2 (ᵥ₎ v) u T2); tauto. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := T2) (t := ᵥ₎ v ᵗ; u). all: crush.
    - (* Red-PatU *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into T2.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion Tyv; subst.
      assert_LinOnly_FinAgeOnly_remove_Disposable ((P ᴳ+ ᴳ{}) ᴳ+ D2) ᴳ{} C T2 U0 P DisposP.
      constructor 1 with (D := D2) (T := T2) (t := u). all: crush.
    - (* Focus-PatS *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨁ T2)) (t := t) ; swap 1 3. constructor 5 with (D1 := D1) (D2 := D2) (m := m) (u1 := u1) (x1 := x1) (u2 := u2) (x2 := x2) (U := U). all: crush.
    - (* Unfocus-PatS *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ D1) ᴳ+ D2) D1 C U U0 P DisposP.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ►caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2} : U) as TyPat.
        { apply (Ty_term_PatS m D1 D2 (ᵥ₎ v) x1 u1 x2 u2 U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ►caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). all: crush.
    - (* Red-PatL *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, Tyv into TyInlv1, D into D1.
      inversion TyInlv1; subst.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ D1) ᴳ+ D2) D1 C U U0 P DisposP.
      assert (D1 ⊢ ᵥ₎ v1 : T1) as Tyt'.
        { term_Val_no_dispose D1. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u1 ᵗ[ x1 ≔ v1] : U) as Tyusub.
        { apply (term_sub_spec_1 D1 D2 m T1 U u1 x1 v1); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u1 ᵗ[ x1 ≔ v1]). all: crush.
    - (* Red-PatR *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, Tyv into TyInlv2, D into D1.
      inversion TyInlv2; subst.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ D1) ᴳ+ D2) D1 C U U0 P DisposP.
      assert (D1 ⊢ ᵥ₎ v2 : T2) as Tyt'.
        { term_Val_no_dispose D1. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u2 ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (term_sub_spec_1 D1 D2 m T2 U u2 x2 v2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u2 ᵗ[ x2 ≔ v2]). all: crush.
    - (* Focus-PatP *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨂ T2)) (t := t) ; swap 1 3. constructor 6 with (D1 := D1) (D2 := D2) (u := u) (x1 := x1) (x2 := x2) (U := U). all: crush.
    - (* Unfocus-PatP *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ D1) ᴳ+ D2) D1 C U U0 P DisposP.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ►caseᵖ m ᵗ(x1 , x2) ⟼ u : U) as TyPat.
        { apply (Ty_term_PatP m D1 D2 (ᵥ₎ v) x1 x2 u U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ►caseᵖ m ᵗ(x1 , x2) ⟼ u). all: crush.
    - (* Red-PatP *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, D into D1.
      inversion Tyv; subst. rename G1 into D11, G2 into D12.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ (D11 ᴳ+ D12)) ᴳ+ D2) (D11 ᴳ+ D12) C U U0 P DisposP.
      assert (D11 ⊢ ᵥ₎ v1 : T1) as Tyt1.
        { term_Val_no_dispose D11. crush. }
      assert (D12 ⊢ ᵥ₎ v2 : T2) as Tyt2.
        { term_Val_no_dispose D12. crush. }
      assert (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2 ⊢ u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (term_sub_spec_2 D11 D12 D2 m T1 T2 U u x1 x2 v1 v2); crush. }
      constructor 1 with (D := (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2)) (T := U) (t := u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2]). all: crush.
    - (* Focus-PatE *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (! n ⁔ T)) (t := t) ; swap 1 3. constructor 7 with (D1 := D1) (D2 := D2) (u := u) (x := x) (U := U). all: crush.
    - (* Unfocus-PatE *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ D1) ᴳ+ D2) D1 C U U0 P DisposP.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ►caseᵉ m ᴇ n ⁔ x ⟼ u : U) as TyPat.
        { apply (Ty_term_PatE m D1 D2 (ᵥ₎ v) n x u U T); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ►caseᵉ m ᴇ n ⁔ x ⟼ u). all: crush.
    - (* Red-PatE *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion Tyv; subst. rename G into D1.
      (* cannot use assert_LinOnly_FinAgeOnly_remove_Disposable because the crush takes infinite amount of time; TODO debug that *)
      assert (LinOnly (m ᴳ· (P ᴳ+ (n ᴳ· D1)) ᴳ+ D2) /\ FinAgeOnly (m ᴳ· (P ᴳ+ (n ᴳ· D1)) ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD) by (apply (Ty_ectxs_LinOnly_FinAgeOnly ((m ᴳ· (P ᴳ+ (n ᴳ· D1)) ᴳ+ D2)) C U U0); tauto).
      assert (LinOnly (P ᴳ+ (n ᴳ· D1))) as LinOnlyD'. { apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD & _ & _). apply LinOnly_stimes_backward in LinOnlyD. assumption. }
      rewrite (nDisposable_in_LinOnly P (n ᴳ· D1) DisposP LinOnlyD') in *.
      (* assert_LinOnly_FinAgeOnly_remove_Disposable (m ᴳ· (P ᴳ+ (n ᴳ· D1)) ᴳ+ D2) (n ᴳ· D1) C U U0 P DisposP. *)
      assert (D1 ⊢ ᵥ₎ v' : T) as Tyt'.
        { term_Val_no_dispose D1. crush. }
      assert ((m · n) ᴳ· D1 ᴳ+ D2 ⊢ u ᵗ[ x ≔ v'] : U) as Tyusub.
        { apply (term_sub_spec_1 D1 D2 (m · n) T U u x v'). all: crush. }
      constructor 1 with (D := (m ᴳ· (n ᴳ· D1) ᴳ+ D2)) (T := U) (t := u ᵗ[ x ≔ v']). all: crush.
    - (* Focus-Map *)
      inversion Tyt; subst. rename T0 into T.
      rename Tyt into TyMap, Tyt0 into Tyt, P1 into D1, P2 into D2.
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (D1 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
      constructor 1 with (D := D1) (T := U ⧔ T) (t := t); swap 1 3. constructor 8 with (D1 := D1) (D2 := D2) (t' := t') (x := x) (T := T) (T' := T') (U := U). all: crush.
    - (* Unfocus-Map *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D1 ᴳ+ D2) D1 C (U ⧔ T') U0 P DisposP.
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ v ►map x ⟼ t' : U ⧔ T') as TyMap.
        { apply (Ty_term_Map D1 D2 (ᵥ₎ v) x t' U T' T); crush. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := U ⧔ T') (t := ᵥ₎ v ►map x ⟼ t'). all: crush.
    - (* Focus-Red_Map_OpenAmpar *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyMap, Tyt0 into Tyt, T0 into T.
      inversion Tyt; subst. rename H2 into DestOnlyD1.
      inversion Tyv; subst. rename D1 into D11, D0 into D12, D3 into D13, DestOnlyD0 into DestOnlyD11, DestOnlyD2 into DestOnlyD12, DestOnlyD3 into DestOnlyD13, DisjointD1D2 into DisjointD11D12, DisjointD1D3 into DisjointD11D13, DisjointD2D3 into DisjointD12D13, ValidOnlyhmD3 into ValidOnlyhmD13.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ (D11 ᴳ+ D12) ᴳ+ D2) (D11 ᴳ+ D12) C (U ⧔ T') U0 P DisposP.
      assert (maxᴴ( hnamesᴳ( D13)) < maxᴴ( hnamesᴳ( D13) ∪ hnames©( C)) + 1) as total_cshift_cond.
        { rewrite Nat.add_comm; unfold lt, plus; apply le_n_S. apply HSubset_impl_lt_max. apply HSubset_weaken_l. sfirstorder. }
      assert (HNames.Subset hnamesᴳ(D11 ᴳ+ D12 ᴳ+ D2) hnames©(C)).
              { apply hnames_C_wk_hnames_G with (U0 := U0) (T := U ⧔ T'). tauto. }
      assert (HNames.Subset hnamesᴳ(D2) hnames©(C)).
              { apply HSubset_union_backward with (G := D11 ᴳ+ D12) (G' := D2) (H := hnames©(C)). tauto. }
      assert (maxᴴ(hnamesᴳ(D2)) <= maxᴴ(hnames©(C))).
              { apply HSubset_impl_lt_max. tauto. }
      assert (hnamesᴳ(D2) ## (hnamesᴳ(D13) ᴴ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1))).
              { apply shift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S. apply HSubset_impl_lt_max. apply HSubset_weaken_r. assumption. }
      assert (hnamesᴳ(D2) ## hnamesᴳ( D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])).
              { unfold HDisjoint. rewrite total_cshift_eq; tauto. }
      assert (HNames.Subset hnamesᴳ(D11) hnames©(C)).
              { apply HSubset_union_backward in H. destruct H. apply HSubset_union_backward in H. tauto. }
      assert (HNames.Subset hnamesᴳ(D12) hnames©(C)).
              { apply HSubset_union_backward in H. destruct H. apply HSubset_union_backward in H. tauto. }
      assert (maxᴴ(hnamesᴳ(D11)) <= maxᴴ(hnames©(C))).
              { apply HSubset_impl_lt_max. tauto. }
      assert (maxᴴ(hnamesᴳ(D12)) <= maxᴴ(hnames©(C))).
              { apply HSubset_impl_lt_max. tauto. }
      assert (maxᴴ( hnamesᴳ( D11)) < maxᴴ( hnamesᴳ( D13) ∪ hnames©( C)) + 1).
        { rewrite Nat.add_comm; unfold lt, plus; apply le_n_S. apply HSubset_impl_lt_max. apply HSubset_weaken_r. assumption. }
      assert (maxᴴ( hnamesᴳ( D12)) < maxᴴ( hnamesᴳ( D13) ∪ hnames©( C)) + 1).
        { rewrite Nat.add_comm; unfold lt, plus; apply le_n_S. apply HSubset_impl_lt_max. apply HSubset_weaken_r. assumption. }
      assert (hnamesᴳ(D11) ## (hnamesᴳ(D13) ᴴ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1))).
              { apply shift_by_max_impl_HDisjoint. assumption. }
      assert (hnamesᴳ(D11) ## hnamesᴳ( D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])).
              { rewrite total_cshift_eq; tauto. }
      assert (hnamesᴳ(D12) ## (hnamesᴳ(D13) ᴴ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1))).
              { apply shift_by_max_impl_HDisjoint. assumption. }
      assert (hnamesᴳ(D12) ## hnamesᴳ( D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])).
              { rewrite total_cshift_eq; tauto. }
      assert ((D2 ᴳ+ D11) # (D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])) as DisjointD2uD11D13.
              { apply Disjoint_union_l_iff. split. apply HDisjoint_to_Disjoint. crush. assumption. apply HDisjoint_to_Disjoint. crush. assumption. }
      assert ((¹↑ ᴳ· (D2 ᴳ+ D11)) # (D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])).
              { apply Disjoint_stimes_l_iff. assumption. }
      assert ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)] ⊢ ᵥ₎ v1 ᵛ[hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)] : T) as Tyt1.
        { term_Val_no_dispose ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]). apply Ty_val_cshift; trivial. apply DestOnly_cshift_iff; apply DestOnly_union_iff; split; try apply DestOnly_stimes_iff. crush. crush. }
      assert (D11 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)] = D11) as D11Eq. { apply cshift_by_Disjoint_eq; crush. }
      assert (D12 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)] = D12) as D12Eq. { apply cshift_by_Disjoint_eq; crush. }
      assert (ValidOnly D13) as ValidOnlyD13. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD13. destruct ValidOnlyhmD13 as (_ & ValidOnlyD13). apply LinNuOnly_wk_LinOnly in ValidOnlyD13. apply LinOnly_wk_ValidOnly in ValidOnlyD13. assumption. }
      assert (LinOnly D13) as LinOnlyD13. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD13. destruct ValidOnlyhmD13 as (_ & LinOnlyD13). apply LinNuOnly_wk_LinOnly in LinOnlyD13. assumption. }
      assert (FinAgeOnly D13) as FinAgeOnlyD13. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD13. destruct ValidOnlyhmD13 as (_ & FinAgeOnlyD13). apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD13. assumption. }
      assert (ValidOnly (D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])).
          { apply ValidOnly_cshift_iff. assumption. }
      assert (ValidOnly (¹↑ ᴳ· (D2 ᴳ+ D11))).
          { apply ValidOnly_stimes_forward. split.
            - rewrite (union_commutative (D11 ᴳ+ D12) D2) in ValidOnlyD.
              rewrite union_associative in ValidOnlyD.
              apply ValidOnly_union_backward in ValidOnlyD.
              tauto.
            - exact (IsValidProof (Lin, Fin 1)).
          }
      assert (ValidOnly ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ( hnames©( C)) + 1)])).
            { apply ValidOnly_cshift_iff. apply ValidOnly_union_forward; trivial.
             { apply ValidOnly_stimes_forward; split; crush. }
             { crush. }
            }
      assert (LinOnly ((¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2)).
            { apply LinOnly_union_iff; repeat split.
              { apply LinOnly_stimes_forward. exact (IsLinProof (Fin 0)). apply LinOnly_cshift_iff. apply LinOnly_union_iff; repeat split. apply LinOnly_stimes_forward. exact (IsLinProof (Fin 1)). crush.
              assumption. crush. }
              { apply LinOnly_stimes_forward. exact (IsLinProof (Fin 1)). crush. }
              { apply Disjoint_stimes_l_iff. rewrite cshift_distrib_on_union. apply Disjoint_union_l_iff. split. rewrite cshift_distrib_on_stimes. rewrite cshift_by_Disjoint_eq. rewrite Disjoint_stimes_l_iff, Disjoint_stimes_r_iff. crush. crush. lia. apply Disjoint_commutative. crush. }
            }
      assert (FinAgeOnly ((¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2)).
            { apply FinAgeOnly_union_forward; repeat split.
              { apply FinAgeOnly_stimes_forward. exact (IsFinAgeProof Lin 0). apply FinAgeOnly_cshift_iff. apply FinAgeOnly_union_forward; repeat split. apply FinAgeOnly_stimes_forward. exact (IsFinAgeProof Lin 1). crush.
              assumption. crush. }
              { apply FinAgeOnly_stimes_forward. exact (IsFinAgeProof Lin 1). crush. }
              { apply Disjoint_stimes_l_iff. rewrite cshift_distrib_on_union. apply Disjoint_union_l_iff. split. rewrite cshift_distrib_on_stimes. rewrite cshift_by_Disjoint_eq. rewrite Disjoint_stimes_l_iff, Disjoint_stimes_r_iff. crush. crush. lia. apply Disjoint_commutative. crush. }
            }
      assert (¹↑ ᴳ· (D2 ᴳ+ D11) ᴳ+ D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)] = (¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2) as ctxEq.
            { rewrite <- stimes_linnu_eq.
              rewrite cshift_distrib_on_union.
              rewrite cshift_distrib_on_stimes.
              rewrite D11Eq.
              rewrite union_commutative with (G2 := ¹↑ ᴳ· D2).
              rewrite union_associative.
              rewrite stimes_distrib_on_union. tauto. }
      assert (hnames©( C) ## hnamesᴳ( D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)])) as hnamesDisjoint.
            { rewrite total_cshift_eq. apply shift_by_max_impl_HDisjoint with (h' := maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1); rewrite Nat.add_comm; unfold lt, plus; apply le_n_S. apply HSubset_impl_lt_max. apply HSubset_weaken_r. sfirstorder. assumption. }
      constructor 1 with (D := ¹↑ ᴳ· (D2 ᴳ+ D11 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) ᴳ+ D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) (T := T') (t := t' ᵗ[ x ≔ v1 ᵛ[hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)] ]); swap 3 4; rewrite D11Eq. { crush. } { crush. } { rewrite ctxEq. apply term_sub_spec_1 with (T' := T) (D2 := ¹↑ ᴳ· D2). all: crush. }
      rewrite <- total_cshift_eq.
      constructor 21 with (D1 := D2 ᴳ+ D11) (D3 := D13 ᴳ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) (C := C) (v2 := v2 ᵛ[ hnamesᴳ( D13) ⩲ (maxᴴ(hnamesᴳ( D13) ∪ hnames©(C)) + 1)]) (T' := T') (U0 := U0) (U := U) (D2 :=
      D12); trivial.
        { rewrite Disjoint_union_l_iff. supercrush. } { apply HDisjoint_to_Disjoint. crush. crush. } { crush. } { crush. } { rewrite <- cshift_distrib_on_hminus_inv. rewrite <- ValidOnly_cshift_iff; assumption. } { rewrite union_commutative in TyC. rewrite union_associative in TyC. tauto. }
        { rewrite <- D12Eq. rewrite <- cshift_distrib_on_hminus_inv. rewrite <- cshift_distrib_on_union. apply Ty_val_cshift. tauto. } { assumption. }
    - (* Close-Ampar *)
      inversion Tyt; subst. rename TyC into TyCc, Tyv into Tyv1. clear H2.
      inversion TyCc; subst. rename H6 into hnamesDisjoint, D0 into D.
      assert (ValidOnly D3) as ValidOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & ValidOnlyD3). apply LinNuOnly_wk_LinOnly in ValidOnlyD3. apply LinOnly_wk_ValidOnly in ValidOnlyD3. assumption. }
      assert (LinOnly D3) as LinOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & LinOnlyD3). apply LinNuOnly_wk_LinOnly in LinOnlyD3. assumption. }
      assert (FinAgeOnly D3) as FinAgeOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & FinAgeOnlyD3). apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD3. assumption. }
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = P ᴳ+ D) as eqD1uD3PuD.
        { unfold union, merge_with, merge. apply ext_eq. intros n. all:simpl. rewrite H0. reflexivity. }
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (D1 ᴳ+ D2) C (U ⧔ T) U0). tauto. }
      assert (LinOnly (¹↑ ᴳ· D1 ᴳ+ D3)) as LinOnlyD'. { apply LinOnly_union_iff; repeat split. { crush. } { assumption. } { crush. } } rewrite eqD1uD3PuD in LinOnlyD'.
      rewrite (nDisposable_in_LinOnly P D DisposP LinOnlyD') in *.
      rewrite <- eqD1uD3PuD in *. clear H0. clear eqD1uD3PuD. clear D.
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ hnamesᴳ( D3) ⟨ v2 ❟ v1 ⟩ : U ⧔ T) as TyA.
        { term_Val_no_dispose (D1 ᴳ+ D2). apply Ty_ectxs_HDisjoint_to_Disjoint with (D := D1 ᴳ+ D2) (D' := D3) (C := C) (T := U ⧔ T) (U0 := U0) in hnamesDisjoint. apply Ty_val_Ampar. all: trivial. crush.
         }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := U ⧔ T) (t := ᵥ₎ hnamesᴳ( D3) ⟨ v2 ❟ v1 ⟩). all: crush.
    - (* Focus-ToA *)
      inversion Tyt; subst.
      rename Tyt into TyToA.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C (U ⧔ ①) U0). tauto. }
      constructor 1 with (D := D) (t := u) (T := U); swap 1 3. constructor 9. all: crush.
    - (* Unfocus-ToA *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (U ⧔ ①) U0 P DisposP.
      assert (D ⊢ to⧔ ᵥ₎ v2 : U ⧔ ①) as TyToA.
        { apply (Ty_term_ToA D (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D) (T := U ⧔ ①) (t := to⧔ ᵥ₎ v2). all: crush.
    - (* Red-ToA *)
      inversion Tyt; subst.
      rename Tyt into TyToA, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      inversion Tyu; subst. rename D into D2.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D2) D2 C (U ⧔ ①) U0 P DisposP.
      assert (ᴳ{} ᴳ+ D2 ⊢ ᵥ₎ hnames_ nil ⟨ v2 ❟ ᵛ() ⟩ : U ⧔ ①).
        { term_Val_no_dispose (ᴳ{} ᴳ+ D2). assert (hnamesᴳ( ᴳ{}) = hnames_ nil). { crush. } rewrite <- H. apply Ty_val_Ampar; swap 1 9; swap 2 8.
          rewrite hminus_inv_empty_eq, <- union_empty_r_eq; tauto.
          rewrite stimes_empty_eq. rewrite <- union_empty_r_eq. constructor.
          all:crush. }
      rewrite <- union_empty_l_eq in H.
      constructor 1 with (D := D2) (T := U ⧔ ①) (t := ᵥ₎ hnames_ nil ⟨ v2 ❟ ᵛ() ⟩). all: crush.
    - (* Focus-FromA *)
      inversion Tyt; subst.
      rename Tyt into TyFromA, T0 into T.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C (U ⨂ ! ¹∞ ⁔ T) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := U ⧔ ! ¹∞ ⁔ T); swap 1 3. constructor 10. all: crush.
    - (* Unfocus-FromA *)
      inversion Tyt; subst. rename TyC into TyCc, T into U, D0 into D. clear H1.
      inversion TyCc; subst. rename U1 into U, v into v2, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D2) D2 C (U ⨂ ! ¹∞ ⁔ T) U0 P DisposP.
      assert (D2 ⊢ from⧔ ᵥ₎ v2 : U ⨂ ! ¹∞ ⁔ T) as TyFromA.
        { apply (Ty_term_FromA D2 (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D2) (T := (U ⨂ ! ¹∞ ⁔ T)) (t := from⧔ ᵥ₎ v2). all: crush.
    - (* Red-FromA *)
      inversion Tyt; subst.
      rename Tyt0 into Tytp, D into D2, ValidOnlyD into ValidOnlyD2 , DestOnlyD into DestOnlyD2, T0 into T.
      inversion Tytp; subst.
      inversion Tyv; subst. rename DestOnlyD2 into DestOnlyPuD1uD2, DestOnlyD0 into DestOnlyD2.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ (D1 ᴳ+ D2)) (D1 ᴳ+ D2) C (U ⨂ ! ¹∞ ⁔ T) U0 P DisposP.
      inversion Tyv1. subst.
      assert (ValidOnly D3) as ValidOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & ValidOnlyD3). apply LinNuOnly_wk_LinOnly in ValidOnlyD3. apply LinOnly_wk_ValidOnly in ValidOnlyD3. assumption. }
      assert (LinOnly D3) as LinOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & LinOnlyD3). apply LinNuOnly_wk_LinOnly in LinOnlyD3. assumption. }
      assert (FinAgeOnly D3) as FinAgeOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & FinAgeOnlyD3). apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD3. assumption. }
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = ᴳ{}) as empty.
      { assert (¹↑ ᴳ· D1 ᴳ+ D3 = ¹∞ ᴳ· G) as intermediary.
        { apply ext_eq'. symmetry. exact H0. }
        assert (¹∞ ᴳ· G = ᴳ{}).
        2:{ congruence. }
        assert (FinAgeOnly (¹∞ ᴳ· G)) as h_lin.
        2:{ apply FinAgeOnly_stimes_dec in h_lin.
            2:{ trivial. }
            destruct h_lin as [h_lin|h_lin].
            - inversion h_lin.
            - apply stimes_empty_iff. tauto. }
        rewrite <- intermediary.
        apply FinAgeOnly_union_forward. repeat split.
        - apply FinAgeOnly_stimes_forward.
          { constructor. }
          crush.
        - assumption.
        - crush. }
      apply union_empty_iff in empty. destruct empty as [empty_D1 empty_D3].
      apply stimes_empty_iff in empty_D1.
      rewrite empty_D3, hminus_inv_empty_eq, <- union_empty_r_eq in Tyv2.
      assert (D2 ⊢ ᵥ₎ ᵛ( v2, ᴇ ¹∞ ⁔ v1) : U ⨂ ! ¹∞ ⁔ T).
      { subst. rewrite union_empty_r_eq with (G:=D2).
        term_Val_no_dispose (D2 ᴳ+ ᴳ{}). apply Ty_val_Prod.
        - assumption.
        - rewrite stimes_empty_eq, <- union_empty_l_eq in Tyv1. assumption. }
      constructor 1 with (D := D2) (T := U ⨂ ! ¹∞ ⁔ T) (t := ᵥ₎ ᵛ( v2, ᴇ ¹∞ ⁔ v1)). all: crush.
    - (* Red-Alloc *)
      inversion Tyt; subst.
      rename T0 into T.
      rewrite (union_empty_r_eq D) in *.
      rewrite <- union_empty_r_eq in DisposP.
      assert_LinOnly_FinAgeOnly_remove_Disposable (D ᴳ+ ᴳ{}) ᴳ{} C (T ⧔ ⌊ T ⌋ ¹ν) U0 D DisposP.
      constructor 1 with (D := ᴳ{}) (T := T ⧔ ⌊ T ⌋ ¹ν) (t := ᵥ₎ ᴴ{ 1} ⟨ ᵛ+ 1 ❟ ᵛ- 1 ⟩); swap 1 4.
      term_Val_no_dispose ᴳ{}. rewrite union_empty_r_eq with (G := ᴳ{}).
    assert (hnamesᴳ( ᴳ{- 1 : ¹ν ⌊ T ⌋ ¹ν }) = ᴴ{ 1}) as hnamesD3Eq.
      { unfold hnames_ctx, hnames_dom, ctx_singleton, hminus_inv. rewrite dom_singleton_eq. cbn. reflexivity. }
      rewrite <- hnamesD3Eq. apply Ty_val_Ampar; swap 1 8; swap 2 9.
      + rewrite stimes_empty_eq, <- union_empty_l_eq. apply Ty_val_Dest. repeat constructor.
      + rewrite <- union_empty_l_eq. rewrite hminus_inv_singleton. apply Ty_val_Hole.
      + apply DestOnly_singleton_dest.
      + rewrite hminus_inv_singleton. apply ValidOnly_singleton_iff. cbn. constructor.
      + apply Disjoint_empty_l.
      + apply Disjoint_empty_l.
      + apply Disjoint_empty_l.
      + apply DestOnly_empty.
      + apply DestOnly_empty.
      + apply DestOnly_empty.
      + assumption.
      + crush.
    - (* Focus-FillU *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tyt.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C ① U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ ① ⌋ n); swap 1 3. constructor 11. all: crush.
    - (* Unfocus-FillU *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C ① U0 P DisposP.
      assert (D ⊢ ᵥ₎ v⨞() : ①) as TyFillU.
        { apply (Ty_term_FillU D (ᵥ₎ v) n). tauto. }
      constructor 1 with (D := D) (T := ①) (t := ᵥ₎ v⨞()). all: crush.
    - (* Red-FillU *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tytp.
      inversion Tytp; subst. clear H1.
      inversion Tyv; subst.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ (ᴳ{- h : m ⌊ ① ⌋ n})) (ᴳ{- h : m ⌊ ① ⌋ n}) C ① U0 P DisposP.
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m ① n LinOnlyD FinAgeOnlyD Subtypem) in *.
      assert (ᴳ{} ⊣ C ©️[ h ≔ hnames_ nil ‗ ᵛ()] : ① ↣ U0).
        { assert (ᴳ{} ᴳ+ ᴳ- (n ᴳ· (ᴳ-⁻¹ ᴳ{})) = ᴳ{}) as e1. { crush. }
          rewrite <- e1.
          assert (hnamesᴳ( ᴳ{}) = hnames_ nil) as e2. { crush. }
          rewrite <- e2.
          apply ectxs_fillCtor_spec with (D1 := ᴳ{}) (T := ①); swap 1 11.
          { rewrite hminus_inv_empty_eq. apply Ty_val_Unit. }
          all: crush. }
      constructor 1 with (D := ᴳ{}) (T := ①) (t := ᵥ₎ ᵛ()); swap 1 4.
      term_Val_no_dispose (ᴳ{}). apply Ty_val_Unit. all: crush.
    - (* Focus-FillL *)
      inversion Tyt; subst.
      rename Tyt into TyFillL, Tyt0 into Tyt.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ T1 ⨁ T2 ⌋ n); swap 1 3. constructor 12. all: crush.
    - (* Unfocus-FillL *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T1 ⌋ n) U0 P DisposP.
      assert (D ⊢ ᵥ₎ v ⨞Inl : ⌊ T1 ⌋ n) as TyFillL.
        { apply (Ty_term_FillL D (ᵥ₎ v) T1 n T2). tauto. }
      constructor 1 with (D := D) (T := ⌊ T1 ⌋ n) (t := ᵥ₎ v ⨞Inl). all: crush.
    - (* Red-FillL *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillL, Tyt0 into Tytp.
      inversion Tytp; subst. clear H1. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T1 ⌋ n) U0 P DisposP.
      inversion Tyv; subst; intros hpMaxCh.
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m (T1 ⨁ T2) n LinOnlyD FinAgeOnlyD Subtypem) in *.
      assert (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1} ‗ Inl ᵛ+ (h' + 1)] : ⌊ T1 ⌋ n ↣ U0).
        { assert (ᴳ{} ᴳ+ ᴳ- (n ᴳ· (ᴳ-⁻¹ ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν })) = ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n }) as e1.
            { rewrite <- union_empty_l_eq. rewrite hminus_inv_singleton. rewrite stimes_singleton_hole. rewrite hminus_singleton. rewrite mode_times_linnu_l_eq. tauto. }
          rewrite <- e1.
          assert (hnamesᴳ( ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) = ᴴ{ h' + 1}) as e2. { crush. }
          rewrite <- e2.
          apply ectxs_fillCtor_spec with (D3 := ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) (T := T1 ⨁ T2); swap 1 11.
          { rewrite hminus_inv_singleton. apply Ty_val_Left. constructor. }
          { crush. } { crush. } { crush. }
          { rewrite hpMaxCh. apply Disjoint_singletons_iff. apply different_than_gt_max. lia. apply HNames.add_spec. tauto. }
          { rewrite e2. rewrite hpMaxCh. apply HDisjoint_gt_max. lia. }
          { crush. } { crush. } { crush. } { crush. } { crush. }
        }
      constructor 1 with (D := ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n}) (T := ⌊ T1 ⌋ n) (t := ᵥ₎ ᵛ- (h' + 1)); swap 1 4.
      term_Val_no_dispose (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n}). apply Ty_val_Dest. all: crush.
    - (* Focus-FillR *)
      inversion Tyt; subst.
      rename Tyt into TyFillR, Tyt0 into Tyt.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C (⌊ T2 ⌋ n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ T1 ⨁ T2 ⌋ n); swap 1 3. constructor 13. all: crush.
    - (* Unfocus-FillR *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T2 ⌋ n) U0 P DisposP.
      assert (D ⊢ ᵥ₎ v ⨞Inr : ⌊ T2 ⌋ n) as TyFillR.
        { apply (Ty_term_FillR D (ᵥ₎ v) T2 n T1). tauto. }
      constructor 1 with (D := D) (T := ⌊ T2 ⌋ n) (t := ᵥ₎ v ⨞Inr). all: crush.
    - (* Red-FillR *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillR, Tyt0 into Tytp.
      inversion Tytp; subst. clear H1. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T2 ⌋ n) U0 P DisposP.
      inversion Tyv; subst; intros hpMaxCh.
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m (T1 ⨁ T2) n LinOnlyD FinAgeOnlyD Subtypem) in *.
      assert (ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1} ‗ Inr ᵛ+ (h' + 1)] : ⌊ T2 ⌋ n ↣ U0).
        { assert (ᴳ{} ᴳ+ ᴳ- (n ᴳ· (ᴳ-⁻¹ ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ ¹ν })) = ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ n }) as e1.
            { rewrite <- union_empty_l_eq. rewrite hminus_inv_singleton. rewrite stimes_singleton_hole. rewrite hminus_singleton. rewrite mode_times_linnu_l_eq. tauto. }
          rewrite <- e1.
          assert (hnamesᴳ( ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ ¹ν}) = ᴴ{ h' + 1}) as e2. { crush. }
          rewrite <- e2.
          apply ectxs_fillCtor_spec with (D3 := ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ ¹ν}) (T := T1 ⨁ T2); swap 1 11.
          { rewrite hminus_inv_singleton. apply Ty_val_Right. constructor. }
          { crush. } { crush. } { crush. }
          { rewrite hpMaxCh. apply Disjoint_singletons_iff. apply different_than_gt_max. lia. apply HNames.add_spec. tauto. }
          { rewrite e2. rewrite hpMaxCh. apply HDisjoint_gt_max. lia. }
          { crush. } { crush. } { crush. } { crush. } { crush. }
        }
      constructor 1 with (D := ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ n}) (T := ⌊ T2 ⌋ n) (t := ᵥ₎ ᵛ- (h' + 1)); swap 1 4.
      term_Val_no_dispose (ᴳ{- (h' + 1) : ¹ν ⌊ T2 ⌋ n}). apply Ty_val_Dest. all: crush.
    - (* Focus-FillE *)
      inversion Tyt; subst.
      rename Tyt into TyFillE, Tyt0 into Tyt, T0 into T.
      assert (mode_times' ((cons m nil) ++ (cons n nil) ++ nil) = mode_times m n) as SimplMode.
        { cbn. rewrite mode_times_linnu_r_eq. reflexivity. }
      rewrite SimplMode in *.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C (⌊ T ⌋ m · n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ ! m ⁔ T ⌋ n); swap 1 3. constructor 15; rewrite? SimplMode in *. all: crush.
    - (* Unfocus-FillE *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      assert (mode_times' ((cons m nil) ++ (cons n nil) ++ nil) = mode_times m n) as SimplMode.
        { cbn. rewrite mode_times_linnu_r_eq. reflexivity. }
      rewrite SimplMode in *.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T ⌋ m · n) U0 P DisposP.
      assert (D ⊢ ᵥ₎ v ⨞ᴇ m : ⌊ T ⌋ mode_times' ((cons m nil) ++ (cons n nil) ++ nil)) as TyFillE.
        { apply (Ty_term_FillE D (ᵥ₎ v) m T n). assumption. tauto. }
      constructor 1 with (D := D) (T := ⌊ T ⌋ m · n) (t := ᵥ₎ v ⨞ᴇ m); rewrite SimplMode in *. all: crush.
    - (* Red-FillE *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillE, Tyt0 into Tytp, T0 into T.
      assert (mode_times' ((cons m nil) ++ (cons n nil) ++ nil) = mode_times m n) as SimplMode.
        { cbn. rewrite mode_times_linnu_r_eq. reflexivity. }
      rewrite SimplMode in *.
      inversion Tytp; subst. clear H1. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T ⌋ m · n) U0 P DisposP.
      inversion Tyv; subst; intros hpMaxCh.
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m0 (! m ⁔ T) n LinOnlyD FinAgeOnlyD Subtypem) in *.
      assert (ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m · n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1} ‗ ᴇ m ⁔ ᵛ+ (h' + 1)] : ⌊ T ⌋ m · n ↣ U0).
        { assert (ᴳ{} ᴳ+ ᴳ- (n ᴳ· (ᴳ-⁻¹ ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m })) = ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m · n }) as e1.
            { rewrite <- union_empty_l_eq. rewrite hminus_inv_singleton. rewrite stimes_singleton_hole. rewrite hminus_singleton. tauto. }
          rewrite <- e1.
          assert (hnamesᴳ( ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m}) = ᴴ{ h' + 1}) as e2. { crush. }
          rewrite <- e2.
          apply ectxs_fillCtor_spec with (D3 := ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m}) (T := ! m ⁔ T); swap 1 11.
          { rewrite hminus_inv_singleton. assert (m ᴳ· ᴳ{+ (h' + 1) : T ‗ ¹ν} = ᴳ{+ (h' + 1) : T ‗ m}). { rewrite  <- mode_times_linnu_l_eq at 2. apply stimes_singleton_hole. } rewrite <- H. apply Ty_val_Exp. constructor. assumption. }
          { crush. } { crush. } { crush. }
          { rewrite hpMaxCh. apply Disjoint_singletons_iff. apply different_than_gt_max. lia. apply HNames.add_spec. tauto. }
          { rewrite e2. rewrite hpMaxCh. apply HDisjoint_gt_max. lia. }
          { crush. } { crush. } { crush. } { crush. } { crush. }
        }
      constructor 1 with (D := ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m · n}) (T := ⌊ T ⌋ m · n) (t := ᵥ₎ ᵛ- (h' + 1)); swap 1 4.
      term_Val_no_dispose (ᴳ{- (h' + 1) : ¹ν ⌊ T ⌋ m · n}). apply Ty_val_Dest. all: crush.
    - (* Focus-FillP *)
      inversion Tyt; subst.
      rename Tyt into TyFillP, Tyt0 into Tyt.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly D C (⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ T1 ⨂ T2 ⌋ n); swap 1 3. constructor 14. all: crush.
    - (* Unfocus-FillP *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n) U0 P DisposP.
      assert (D ⊢ ᵥ₎ v ⨞(,) : ⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n) as TyFillP.
        { apply (Ty_term_FillP D (ᵥ₎ v) T1 n T2). tauto. }
      constructor 1 with (D := D) (T := ⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n) (t := ᵥ₎ v ⨞(,)). all: crush.
    - (* Red-FillP *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillP, Tyt0 into Tytp.
      inversion Tytp; subst. clear H1. rename D0 into D.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D) D C (⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n) U0 P DisposP.
      inversion Tyv; subst; intros hpMaxCh.
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m (T1 ⨂ T2) n LinOnlyD FinAgeOnlyD Subtypem) in *.
      assert (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν} # ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ ¹ν}) as NewHolesDisjoint. { apply Disjoint_singletons_iff. injection. lia. }
      assert (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1, h' + 2} ‗ ᵛ(ᵛ+ (h' + 1), ᵛ+ (h' + 2))] : ⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n ↣ U0).
        { assert (ᴳ{} ᴳ+ ᴳ- (n ᴳ· (ᴳ-⁻¹ (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ ¹ν}))) = (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ n})) as e1.
            { rewrite <- union_empty_l_eq. rewrite hminus_inv_distrib_on_union. rewrite stimes_distrib_on_union. rewrite hminus_distrib_on_union. rewrite 2 hminus_inv_singleton. rewrite 2 stimes_singleton_hole. rewrite 2 hminus_singleton. rewrite * mode_times_linnu_l_eq. tauto. rewrite 2 hminus_inv_singleton; rewrite 2 stimes_singleton_hole. all: apply Disjoint_singletons_iff. injection. lia. injection. lia. }
          rewrite <- e1.
          assert (hnamesᴳ( (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ ¹ν}) ) = ᴴ{ h' + 1, h' + 2}) as e2. { rewrite hnames_distrib_on_union. rewrite 2 hnames_singleton_dest. apply hnames_singleton_union_eq. }
          rewrite <- e2.
          apply ectxs_fillCtor_spec with (D3 := (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ ¹ν}) ) (T := T1 ⨂ T2); swap 1 11.
          { rewrite hminus_inv_distrib_on_union. rewrite 2 hminus_inv_singleton. apply Ty_val_Prod. apply Ty_val_Hole. apply Ty_val_Hole. assumption. }
          { apply DestOnly_union_iff. crush. } { crush. } { crush. }
          { apply Disjoint_union_l_iff. split; rewrite hpMaxCh; apply Disjoint_singletons_iff. { apply different_than_gt_max. lia. apply HNames.add_spec. tauto. } { apply different_than_gt_max. lia. apply HNames.add_spec. tauto. } }
          { rewrite e2. rewrite hpMaxCh. rewrite <- hnames_singleton_union_eq. apply HDisjoint_union_iff; repeat split. apply HDisjoint_gt_max. lia. apply HDisjoint_gt_max. lia. }
          { apply LinOnly_union_iff. repeat split. crush. crush. assumption. }
          { apply FinAgeOnly_union_forward. repeat split. crush. crush. assumption. }
          { apply ValidOnly_union_forward. crush. crush. assumption. }
          { crush. } { crush. }
        }
      constructor 1 with (D := ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ n}) (T := ⌊ T1 ⌋ n ⨂ ⌊ T2 ⌋ n) (t := ᵥ₎ ᵛ(ᵛ- (h' + 1), ᵛ- (h' + 2))); swap 1 4. term_Val_no_dispose (ᴳ{- (h' + 1) : ¹ν ⌊ T1 ⌋ n} ᴳ+ ᴳ{- (h' + 2) : ¹ν ⌊ T2 ⌋ n}). apply Ty_val_Prod. apply Ty_val_Dest. apply IsSubtype_refl. apply Ty_val_Dest. { apply IsSubtype_refl. } { apply DestOnly_union_iff. crush. } { apply DestOnly_union_iff. crush. } { assert (hnames_ ((©️⬜ ∘ h' + 1) ++ (©️⬜ ∘ h' + 2) ++ ©️⬜) = ᴴ{ h' + 1, h' + 2}). cbn. reflexivity. assumption. } { apply ValidOnly_union_forward. crush. crush. apply Disjoint_singletons_iff. injection. lia. }
    - (* Focus-FillF *)
      inversion Tyt; subst.
      rename Tyt into TyFillF, Tyt0 into Tyt, T0 into T.
      assert (LinOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) C ① U0). tauto. }
      constructor 1 with (D := P1) (t := t) (T := ⌊ T ⁔ m → U ⌋ n); swap 1 3. constructor 16 with (D2 := P2). apply LinOnly_union_iff. all: crush.
    - (* Unfocus-FillF *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D1, U1 into U.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2) D1 C ① U0 P DisposP.
      assert (D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2 ⊢ ᵥ₎ v ⨞(λ x ⁔ m ⟼ u) : ①) as TyFillF.
        { apply (Ty_term_FillF D1 n D2 (ᵥ₎ v) x m u T U). all:trivial. apply DestOnly_Disjoint_singleton_var; trivial. }
      constructor 1 with (D := D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2) (T := ①) (t := ᵥ₎ v ⨞(λ x ⁔ m ⟼ u)). replace (mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜)) with (¹↑ · n) in *.
      apply ValidOnly_union_forward. assumption. apply ValidOnly_stimes_forward; split. assumption. apply IsValid_times_iff; split. constructor. all:trivial. apply Disjoint_stimes_r_iff. assumption. unfold mode_times'. simpl. rewrite mode_times_linnu_r_eq. reflexivity. apply DestOnly_union_iff; split. assumption. crush.
    - (* Red-FillF *)
      inversion Tyt; subst.
      rename Tyt into TyFillF, Tyt0 into Tytp, T0 into T.
      inversion Tytp; subst. clear H1. rename D into D1, P2 into D2.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2) D1 C ① U0 P DisposP.
      inversion Tyv; subst.
      assert (LinOnly ᴳ{- h : m0 ⌊ T ⁔ m → U ⌋ n}) as LinOnlySingl. { crush. }
      assert (FinAgeOnly ᴳ{- h : m0 ⌊ T ⁔ m → U ⌋ n}) as FinAgeOnlySingl. { crush. }
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m0 (T ⁔ m → U) n LinOnlySingl FinAgeOnlySingl Subtypem) in *.
      assert (ᴳ{} ⊣ C ©️[ h ≔ hnames_ ©️⬜ ‗ ᵛλ x ⁔ m ⟼ u] : ① ↣ U0).
        { replace (mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜)) with (¹↑ · n) in *.
          apply ectxs_fillLeaf_spec with (D2 := D2) (n := n) (T := T ⁔ m → U); swap 1 8.
          { crush. } { crush. }  { crush. } { crush. }
          { apply Disjoint_commutative. apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (_ & _ & Dis). crush. }
          { rewrite <- union_empty_l_eq. rewrite union_commutative. assumption. }
          { apply Ty_val_Fun. assumption. assumption. crush. }
          { cbn. rewrite mode_times_linnu_r_eq. reflexivity. } }
        constructor 1 with (D := ᴳ{}) (T := ①) (t := ᵥ₎ ᵛ()); swap 1 4. term_Val_no_dispose ᴳ{}.
        apply Ty_val_Unit. all:crush.
    - (* Focus-FillComp1 *)
      inversion Tyt; subst.
      rename Tyt into TyFillComp1, Tyt0 into Tyt.
      assert (LinOnly (P1 ᴳ+ ¹↑ ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ ¹↑ ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ ¹↑ ᴳ· P2) C (T) U0). tauto. }
      constructor 1 with (D := P1) (t := t) (T := ⌊ U ⌋ ¹ν); swap 1 3. constructor 17 with (D2 := P2) (T := T). all: crush.
    - (* Unfocus-FillComp1 *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D1, U1 into U.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D1 ᴳ+ ¹↑ ᴳ· D2) D1 C (T) U0 P DisposP.
      assert (D1 ᴳ+ ¹↑ ᴳ· D2 ⊢ ᵥ₎ v ⨞· t' : T) as TyFillComp1.
        { apply (Ty_term_FillComp D1 D2 (ᵥ₎ v) t' T U). all:trivial. }
      constructor 1 with (D := D1 ᴳ+ ¹↑ ᴳ· D2) (T := T) (t := ᵥ₎ v ⨞· t'). apply ValidOnly_union_forward; repeat split. assumption. apply ValidOnly_stimes_forward; repeat split. assumption. crush. crush. assumption. assumption.
    - (* Focus-FillComp2 *)
      inversion Tyt; subst.
      rename Tyt into TyFillComp2, Tyt0 into Tyt.
      assert (LinOnly (P1 ᴳ+ ¹↑ ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ ¹↑ ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ ¹↑ ᴳ· P2) C (T) U0). tauto. }
      constructor 1 with (D := P2) (T := U ⧔ T); swap 1 3. constructor 18 with (D1 := P1)  (D2 := P2). all: crush.
    - (* Unfocus-FillComp2 *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D2, U1 into U.
      assert_LinOnly_FinAgeOnly_remove_Disposable (D1 ᴳ+ ¹↑ ᴳ· (P ᴳ+ D2)) D2 C (T) U0 P DisposP.
      assert (D1 ᴳ+ ¹↑ ᴳ· D2 ⊢ ᵥ₎ v ⨞· ᵥ₎ v' : T) as TyFillComp2.
        { apply (Ty_term_FillComp D1 D2 (ᵥ₎ v) (ᵥ₎ v') T U). all:trivial. }
      constructor 1 with (D := D1 ᴳ+ ¹↑ ᴳ· D2) (T := T) (t := ᵥ₎ v ⨞· ᵥ₎ v'). apply ValidOnly_union_forward; repeat split. assumption. crush. crush. crush. assumption. assumption.
    - (* Red-FillComp *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillComp, Tyt0 into Tyt.
      assert (LinOnly (P1 ᴳ+ ¹↑ ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ ¹↑ ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ ¹↑ ᴳ· P2) C (T) U0). tauto. }
      inversion Tyt; subst. inversion Tytp; subst. rename Tyv0 into Tyvp, D into D1, D0 into D2, P into P1, P0 into P2, H2 into DestOnlyD1, H3 into DestOnlyD2, DisposP into DisposP1, DisposP0 into DisposP2.
      assert (LinOnly (P1 ᴳ+ D1)) as LinOnlyP1D1. { crush. }
      assert (LinOnly (P2 ᴳ+ D2)) as LinOnlyP2D2. { crush. }
      rewrite (nDisposable_in_LinOnly P1 D1 DisposP1 LinOnlyP1D1) in *.
      rewrite (nDisposable_in_LinOnly P2 D2 DisposP2 LinOnlyP2D2) in *.
      inversion Tyv; subst. inversion Tyvp; subst. intros hpMaxCh. rename D0 into D2, DestOnlyD1 into DestOnlyDest, DestOnlyD2 into DestOnlyD1D2, DestOnlyD0 into DestOnlyD1, DestOnlyD3 into DestOnlyD2, DestOnlyD4 into DestOnlyD3.
      assert (LinOnly ᴳ{- h : m ⌊ U ⌋ ¹ν}) as LinOnlySingl. { crush. }
      assert (FinAgeOnly ᴳ{- h : m ⌊ U ⌋ ¹ν}) as FinAgeOnlySingl. { crush. }
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m U ¹ν LinOnlySingl FinAgeOnlySingl Subtypem) in *.
      assert (maxᴴ(hnames©( C)) < h'').
        { rewrite hpMaxCh. assert (maxᴴ( hnames©( C)) <= maxᴴ( hnamesᴳ( D3) ∪ (hnames©( C) ∪ ᴴ{ h}))). { apply HSubset_impl_lt_max. unfold HNames.Subset. intros a H. apply HNames.union_spec. right. apply HNames.union_spec. left. assumption. } lia. }
      assert (maxᴴ( hnamesᴳ( D3)) < h'') as total_cshift_cond.
        { rewrite hpMaxCh. rewrite Nat.add_comm; unfold lt, plus; apply le_n_S. apply HSubset_impl_lt_max. apply HSubset_weaken_l. sfirstorder. }
      assert ((ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν} ᴳ+ ¹↑ ᴳ· (D1 ᴳ+ D2)) # (D3 ᴳ[ hnamesᴳ( D3) ⩲ h''])).
        { apply Ty_ectxs_HDisjoint_to_Disjoint with (C := C) (T := T) (U0 := U0). assumption. rewrite total_cshift_eq. apply shift_by_max_impl_HDisjoint. assumption. assumption.
        }
      assert (HNames.Subset hnamesᴳ( D2) hnames©( C)).
        { apply hnames_C_wk_hnames_G in TyC. apply HSubset_union_backward in TyC. destruct TyC as (_ & TyC). rewrite stimes_distrib_on_union in TyC. apply HSubset_union_backward in TyC. destruct TyC as (_ & TyC). apply HSubset_stimes_backward in TyC. assumption. }
      assert (HNames.Subset hnamesᴳ( D1) hnames©( C)).
        { apply hnames_C_wk_hnames_G in TyC. apply HSubset_union_backward in TyC. destruct TyC as (_ & TyC). rewrite stimes_distrib_on_union in TyC. apply HSubset_union_backward in TyC. destruct TyC as (TyC & _). apply HSubset_stimes_backward in TyC. assumption. }
      assert (ValidOnly D3) as ValidOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & ValidOnlyD3). apply LinNuOnly_wk_LinOnly in ValidOnlyD3. apply LinOnly_wk_ValidOnly in ValidOnlyD3. assumption. }
      assert (LinOnly D3) as LinOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & LinOnlyD3). apply LinNuOnly_wk_LinOnly in LinOnlyD3. assumption. }
      assert (FinAgeOnly D3) as FinAgeOnlyD3. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhmD3. destruct ValidOnlyhmD3 as (_ & FinAgeOnlyD3). apply LinNuOnly_wk_FinAgeOnly in FinAgeOnlyD3. assumption. }
      assert ((¹↑ ᴳ· D1 ᴳ+ D3) ᴳ[ hnamesᴳ( D3) ⩲ h''] ⊣ C ©️[ h ≔ hnamesᴳ( D3) ᴴ⩲ h'' ‗ v2 ᵛ[ hnamesᴳ( D3) ⩲ h'']] : T ↣ U0). {
        rewrite cshift_distrib_on_union. rewrite cshift_by_Disjoint_eq. rewrite <- total_cshift_eq.
        apply ectxs_fillComp_spec with (D1 := ¹↑ ᴳ· D1) (D2 := D2) (D3 := D3 ᴳ[ hnamesᴳ( D3) ⩲ h'']) (T := T) (U := U).
        { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite Disjoint_commutative. apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (_ & _ & Dis). crush. } { rewrite Disjoint_commutative. apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (_ & _ & Dis). crush. } { rewrite Disjoint_commutative. crush. } { rewrite total_cshift_eq. apply shift_by_max_impl_HDisjoint. assumption. assumption. } { crush. } { crush. } { crush. }
        { rewrite <- stimes_distrib_on_union. rewrite union_commutative. assumption. }
        { rewrite <- cshift_by_Disjoint_eq with (D := D2) (D' := D3) (h' := h''). rewrite <- cshift_distrib_on_hminus_inv. rewrite <- cshift_distrib_on_union. apply Ty_val_cshift. assumption. assumption. rewrite hpMaxCh. rewrite Nat.add_comm. rewrite Nat.lt_succ_r. apply HSubset_impl_lt_max. apply HSubset_weaken_r. apply HSubset_weaken_l. assumption. } { assumption. } { crush. } { rewrite hnames_stimes_eq. rewrite hpMaxCh. rewrite Nat.add_comm. rewrite Nat.lt_succ_r. apply HSubset_impl_lt_max. apply HSubset_weaken_r. apply HSubset_weaken_l. assumption. }
      }
      constructor 1 with (D := (¹↑ ᴳ· D1 ᴳ+ D3) ᴳ[ hnamesᴳ( D3) ⩲ h'']) (T := T) (t := ᵥ₎ v1 ᵛ[ hnamesᴳ( D3) ⩲ h'']); swap 1 4. term_Val_no_dispose ((¹↑ ᴳ· D1 ᴳ+ D3) ᴳ[ hnamesᴳ( D3) ⩲ h'']). apply Ty_val_cshift. assumption. crush. crush. assumption. { rewrite cshift_distrib_on_union. apply ValidOnly_union_forward. rewrite cshift_distrib_on_stimes. rewrite cshift_by_Disjoint_eq. apply ValidOnly_union_backward in ValidOnlyD. destruct ValidOnlyD as (ValidOnlyH & ValidOnlyD). rewrite stimes_distrib_on_union in ValidOnlyD. crush. assumption. rewrite hpMaxCh. rewrite Nat.add_comm. rewrite Nat.lt_succ_r. apply HSubset_impl_lt_max. apply HSubset_weaken_r. apply HSubset_weaken_l. assumption. apply ValidOnly_cshift_iff. assumption. apply Disjoint_union_l_iff in H0. destruct H0 as (H21 & H22). rewrite stimes_distrib_on_union in H22. apply Disjoint_union_l_iff in H22. destruct H22 as (H22 & H23). rewrite cshift_by_Disjoint_eq. assumption. crush. rewrite hnames_stimes_eq. rewrite hpMaxCh. rewrite Nat.add_comm. rewrite Nat.lt_succ_r. apply HSubset_impl_lt_max. apply HSubset_weaken_r. apply HSubset_weaken_l. assumption. }
    - (* Focus-FillLeaf1 *)
      inversion Tyt; subst.
      rename Tyt into TyFillLeaf1, Tyt0 into Tyt, T0 into T.
      assert (LinOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) C ① U0). tauto. }
      constructor 1 with (D := P1) (t := t) (T := ⌊ T ⌋ n); swap 1 3. constructor 19 with (D2 := P2). all: crush.
    - (* Unfocus-FillLeaf1 *)
      inversion Tyt; subst. rename TyC into TyCc.
      inversion TyCc; subst. rename D0 into D1, T0 into T.
      assert_LinOnly_FinAgeOnly_remove_Disposable (P ᴳ+ D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2) D1 C ① U0 P DisposP.
      assert (D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2 ⊢ ᵥ₎ v ◀ t' : ①) as TyFillLeaf1.
        { apply (Ty_term_FillLeaf D1 n D2 (ᵥ₎ v) t' T). all:trivial. }
      constructor 1 with (D := D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2) (T := ①) (t := ᵥ₎ v ◀ t'). apply ValidOnly_union_forward. assumption. apply ValidOnly_stimes_forward; repeat split. assumption. replace (mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜)) with (¹↑ · n). apply IsValid_times_iff; repeat split. 2:{ simpl. rewrite mode_times_linnu_r_eq. reflexivity. } all:crush.
    - (* Focus-FillLeaf2 *)
      inversion Tyt; subst.
      rename Tyt into TyFillLeaf2, Tyt0 into Tyt, T0 into T.
      assert (LinOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) C ① U0). tauto. }
      constructor 1 with (D := P2) (t := t') (T := T); swap 1 3. constructor 20 with (n := n) (D1 := P1). all: crush.
    - (* Unfocus-FillLeaf2 *)
      inversion Tyt; subst. rename TyC into TyCc.
      inversion TyCc; subst. rename D0 into D2.
      assert_LinOnly_FinAgeOnly_remove_Disposable (D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· (P ᴳ+ D2)) D2 C ① U0 P DisposP.
      assert (D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2 ⊢ ᵥ₎ v ◀ ᵥ₎ v' : ①) as TyFillLeaf2.
        { apply (Ty_term_FillLeaf D1 n D2 (ᵥ₎ v) (ᵥ₎ v') T). all:trivial. }
      constructor 1 with (D := D1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· D2) (T := ①) (t := ᵥ₎ v ◀ ᵥ₎ v'). apply ValidOnly_union_forward. assumption. apply ValidOnly_stimes_forward; repeat split. assumption. replace (mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜)) with (¹↑ · n). apply IsValid_times_iff; repeat split. 2:{ simpl. rewrite mode_times_linnu_r_eq. reflexivity. } all:crush.
    - (* Red-FillLeaf *)
      inversion Tyt; subst.
      rename Tyt into TyFillLeaf, Tyt0 into Tyt, T0 into T.
      assert (LinOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) /\ FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinOnly_FinAgeOnly (P1 ᴳ+ mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜) ᴳ· P2) C ① U0). tauto. }
      inversion Tyt; subst. inversion Tytp; subst. rename Tyv0 into Tyvp, D into D1, D0 into D2, P into P1, P0 into P2, H1 into DestOnlyD1, H2 into DestOnlyD2, DisposP into DisposP1, DisposP0 into DisposP2.
      assert (LinOnly (P1 ᴳ+ D1)) as LinOnlyP1D1. { crush. }
      assert (LinOnly (P2 ᴳ+ D2)) as LinOnlyP2D2. { crush. }
      rewrite (nDisposable_in_LinOnly P1 D1 DisposP1 LinOnlyP1D1) in *.
      rewrite (nDisposable_in_LinOnly P2 D2 DisposP2 LinOnlyP2D2) in *.
      inversion Tyv; subst.
      assert (LinOnly ᴳ{- h : m ⌊ T ⌋ n}) as LinOnlySingl. { crush. }
      assert (FinAgeOnly ᴳ{- h : m ⌊ T ⌋ n}) as FinAgeOnlySingl. { crush. }
      rewrite <- (LinOnly_FinAgeOnly_no_derelict h ¹ν m T n LinOnlySingl FinAgeOnlySingl Subtypem) in *.
      assert (ᴳ{} ⊣ C ©️[ h ≔ hnames_ ©️⬜ ‗ v] : ① ↣ U0). {
        apply ectxs_fillLeaf_spec with (D2 := D2) (n := n) (T := T).
        { crush. } { crush. } { crush. } { crush. } { rewrite Disjoint_commutative. apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (_ & _ & Dis). crush. } { rewrite <- union_empty_l_eq. rewrite union_commutative. replace (mode_times' ((©️⬜ ∘ ¹↑) ++ (©️⬜ ∘ n) ++ ©️⬜)) with (¹↑ · n) in *. 2:{ simpl. rewrite mode_times_linnu_r_eq. reflexivity. } assumption. } { assumption. }
      }
      constructor 1 with (D := ᴳ{}) (T := ①) (t := ᵥ₎ ᵛ()); swap 1 4. term_Val_no_dispose ᴳ{}. apply Ty_val_Unit. all:crush.
Qed.

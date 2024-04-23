Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.
Require Import Coq.Program.Equality.
Require Import Ott.Finitely.
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
Require Import Ott.destination_calculus_proofs.


Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - (* Sem-eterm-AppFoc1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := T) (t := t); swap 1 3. constructor 2 with (D2 := D2) (m := m) (t' := t') (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc1 *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻ t' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) t' U T); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻ t').
      all: crush.
    - (* Sem-eterm-AppFoc2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
        constructor 1 with (D := D2) (T := T ⁔ m → U) (t := t'); swap 1 3. constructor 3 with (D1 := D1) (m := m) (v := v) (T := T) (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc2 *)
      inversion Tyt; subst. rename TyRv into TyRvp, TyC into TyCc, D0 into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tytp, Tyv into Tyt, T0 into T.
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyD2) in *.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻ ᵥ₎ v' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) (ᵥ₎ v') U T); tauto. }
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := (ᵥ₎ v) ≻ (ᵥ₎ v')).
      all: crush.
    - (* Sem-eterm-AppRed *)
      inversion Tyt; subst.
      assert (m = m0) as Eqmm0.
        { inversion_clear Tytp; inversion_clear TyRv; tauto. }
      rewrite <- Eqmm0 in *. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tytp; subst. clear H1. rename TyRv into TyRv', D into D2.
      assert (DestOnly (P ᴳ+ D2)) as DestOnlyPuD2. { crush. }
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyPuD2) in *.
      inversion TyRv'; subst. rename H1 into DestOnlyD2.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u ᵗ[ x ≔ v] : U) as Tyusub.
      { apply (term_sub_spec_1 D1 D2 m T U u x v). all: crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u ᵗ[ x ≔ v]).
      all: crush.
    - (* Sem-eterm-PatUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C T2 U0); tauto. }
        constructor 1 with (D := D1) (T := ①) (t := t); swap 1 3. constructor 4 with (D2 := D2) (U := T2) (u := u). all: crush.
    - (* Sem-eterm-PatUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename U into T2.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C T2 U0); tauto. }
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ v ᵗ; u : T2) as TyPat.
        { apply (Ty_term_PatU D1 D2 (ᵥ₎ v) u T2); tauto. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := T2) (t := ᵥ₎ v ᵗ; u). all: crush.
    - (* Sem-eterm-PatURed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into T2.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst.
      constructor 1 with (D := D2) (T := T2) (t := u). all: crush.
    - (* Sem-eterm-PatSFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨁ T2)) (t := t) ; swap 1 3. constructor 5 with (D1 := D1) (D2 := D2) (m := m) (u1 := u1) (x1 := x1) (u2 := u2) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatSUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2} : U) as TyPat.
        { apply (Ty_term_PatS m D1 D2 (ᵥ₎ v) x1 u1 x2 u2 U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). all: crush.
    - (* Sem-eterm-PatLRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, TyRv into TyRInlv1, D into D1.
      inversion TyRInlv1; subst.
      assert (DestOnly (P ᴳ+ D1)) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyPuD1) in *.
      assert (D1 ⊢ ᵥ₎ v1 : T1) as Tyt'.
        { term_Val_no_dispose D1. }
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u1 ᵗ[ x1 ≔ v1] : U) as Tyusub.
        { apply (term_sub_spec_1 D1 D2 m T1 U u1 x1 v1); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u1 ᵗ[ x1 ≔ v1]). all: crush.
    - (* Sem-eterm-PatRRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, TyRv into TyRInlv2, D into D1.
      inversion TyRInlv2; subst.
      assert (DestOnly (P ᴳ+ D1)) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyPuD1) in *.
      assert (D1 ⊢ ᵥ₎ v2 : T2) as Tyt'.
        { term_Val_no_dispose D1. }
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u2 ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (term_sub_spec_1 D1 D2 m T2 U u2 x2 v2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u2 ᵗ[ x2 ≔ v2]). all: crush.
    - (* Sem-eterm-PatPFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨂ T2)) (t := t) ; swap 1 3. constructor 6 with (D1 := D1) (D2 := D2) (u := u) (x1 := x1) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatPUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u : U) as TyPat.
        { apply (Ty_term_PatP m D1 D2 (ᵥ₎ v) x1 x2 u U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u). all: crush.
    - (* Sem-eterm-PatPRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, D into D1.
      inversion TyRv; subst. rename G1 into D11, G2 into D12.
      assert (DestOnly (P ᴳ+ (D11 ᴳ+ D12))) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P (D11 ᴳ+ D12) DisposP DestOnlyPuD1) in *.
      assert (D11 ⊢ ᵥ₎ v1 : T1) as Tyt1.
        { term_Val_no_dispose D11. crush. }
      assert (D12 ⊢ ᵥ₎ v2 : T2) as Tyt2.
        { term_Val_no_dispose D12. crush. }
      assert (LinOnly (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2) /\ FinAgeOnly (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2 ⊢ u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (term_sub_spec_2 D11 D12 D2 m T1 T2 U u x1 x2 v1 v2); crush. }
      constructor 1 with (D := (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2)) (T := U) (t := u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2]). all: crush.
    - (* Sem-eterm-PatEFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (! n ⁔ T)) (t := t) ; swap 1 3. constructor 7 with (D1 := D1) (D2 := D2) (u := u) (x := x) (U := U). all: crush.
    - (* Sem-eterm-PatEUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2) /\ FinAgeOnly (m ᴳ· D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻caseᵉ m ᴇ n ⁔ x ⟼ u : U) as TyPat.
        { apply (Ty_term_PatE m D1 D2 (ᵥ₎ v) n x u U T); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻caseᵉ m ᴇ n ⁔ x ⟼ u). all: crush.
    - (* Sem-eterm-PatERed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst. rename G into D1.
      assert (DestOnly (P ᴳ+ (n ᴳ· D1))) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P (n ᴳ· D1) DisposP DestOnlyPuD1) in *.
      assert (D1 ⊢ ᵥ₎ v' : T) as Tyt'.
        { term_Val_no_dispose D1. crush. }
      assert (LinOnly (m ᴳ· (n ᴳ· D1) ᴳ+ D2) /\ FinAgeOnly (m ᴳ· (n ᴳ· D1) ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· (n ᴳ· D1) ᴳ+ D2) C U U0); tauto. }
      assert ((m · n) ᴳ· D1 ᴳ+ D2 ⊢ u ᵗ[ x ≔ v'] : U) as Tyusub.
        { apply (term_sub_spec_1 D1 D2 (m · n) T U u x v'). all: crush. }
      constructor 1 with (D := (m ᴳ· (n ᴳ· D1) ᴳ+ D2)) (T := U) (t := u ᵗ[ x ≔ v']). all: crush.
    - (* Sem-eterm-MapFoc *)
      inversion Tyt; subst. rename T0 into T.
      rename Tyt into TyMap, Tyt0 into Tyt, P1 into D1, P2 into D2.
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
      constructor 1 with (D := D1) (T := U ⧔ T) (t := t); swap 1 3. constructor 8 with (D1 := D1) (D2 := D2) (t' := t') (x := x) (T := T) (T' := T') (U := U). all: crush.
    - (* Sem-eterm-MapUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻map x ⟼ t' : U ⧔ T') as TyMap.
        { apply (Ty_term_Map D1 D2 (ᵥ₎ v) x t' U T' T); crush. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := U ⧔ T') (t := ᵥ₎ v ≻map x ⟼ t'). all: crush.
    - (* Sem-eterm-MapRedAOpenFoc *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyMap, Tyt0 into Tyt, T0 into T.
      inversion Tyt; subst. rename H2 into DestOnlyD1.
      inversion TyRv; subst. rename D1 into D11, D0 into D12, D3 into D13, DestOnlyD0 into DestOnlyD11, DestOnlyD2 into DestOnlyD12, DestOnlyD3 into DestOnlyD13, LinOnlyD3 into LinOnlyD13, ValidOnlyD3 into ValidOnlyD13, DisjointD1D2 into DisjointD11D12, DisjointD1D3 into DisjointD11D13, DisjointD2D3 into DisjointD12D13, FinAgeOnlyD3 into FinAgeOnlyD13.
      assert (DestOnly (P ᴳ+ (D11 ᴳ+ D12))) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P (D11 ᴳ+ D12) DisposP DestOnlyPuD1) in *.
      assert ((D2 ᴳ+ D11) # (D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])) as DisjointD2uD11D13. {
          {  apply Disjoint_union_l_iff. assert (HVars.Subset hvarsᴳ(D11 ᴳ+ D12 ᴳ+ D2) hvars©(C)).
              { apply hvars_C_wk_hvars_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HVars.Subset hvarsᴳ(D2) hvars©(C)).
              { apply HSubset_union_backward with (G := D11 ᴳ+ D12) (G' := D2) (H := hvars©(C)). tauto. }
              assert (maxᴴ(hvarsᴳ(D2)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D2) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D2) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { unfold HDisjoint. rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
            { assert (HVars.Subset hvarsᴳ(D11) hvars©(C)).
              { apply HSubset_union_backward in H. destruct H. apply HSubset_union_backward in H. tauto. }
              assert (maxᴴ(hvarsᴳ(D11)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D11) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D11) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
          } }
      assert ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] ⊢ ᵥ₎ v1 ᵛ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] : T) as Tyt1.
        { term_Val_no_dispose ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]). apply TyR_val_cshift; trivial. apply DestOnly_cshift_iff; apply DestOnly_union_iff; split; try apply DestOnly_stimes_iff. crush. crush. }
          assert ((¹↑ ᴳ· (D2 ᴳ+ D11)) # (D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
          { apply Disjoint_stimes_l_iff. assumption. }
      constructor 1 with (D := ¹↑ ᴳ· (D2 ᴳ+ D11 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) (T := T') (t := t' ᵗ[ x ≔ v1 ᵛ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] ]); swap 3 4;
        assert (D11 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] = D11) as D11Eq by ( apply cshift_by_Disjoint_eq; crush );
        assert (D12 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] = D12) as D12Eq by ( apply cshift_by_Disjoint_eq; crush );
        rewrite D11Eq.
        { assert (ValidOnly (¹↑ ᴳ· (D2 ᴳ+ D11))).
          { apply ValidOnly_stimes_forward. split.
            - rewrite (union_commutative (D11 ᴳ+ D12) D2) in ValidOnlyD.
              rewrite union_associative in ValidOnlyD.
              apply ValidOnly_union_backward in ValidOnlyD.
              tauto.
            - exact (IsValidProof (Lin, Fin 1)).
          }
          assert (ValidOnly (D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
          { apply ValidOnly_cshift_iff; tauto. }

          apply ValidOnly_union_forward; crush.
        }
        { rewrite (union_commutative D2 D11). apply DestOnly_union_iff. split.
          { crush. }
          { crush. }
        }
        { assert (¹↑ ᴳ· (D2 ᴳ+ D11) ᴳ+ D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] = (¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2) as ctxEq.
          { rewrite <- stimes_linnu_eq.
            rewrite cshift_distrib_on_union.
            rewrite cshift_distrib_on_stimes.
            rewrite D11Eq.
            rewrite union_commutative with (G2 := ¹↑ ᴳ· D2).
            rewrite union_associative.
            rewrite stimes_distrib_union. tauto. }
          rewrite ctxEq.
          assert (ValidOnly ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ( hvars©( C)) + 1)])).
            { apply ValidOnly_cshift_iff. apply ValidOnly_union_forward; trivial.
             { apply ValidOnly_stimes_forward; split; crush. }
             { crush. }
            }
          assert (LinOnly (D11 ᴳ+ D12 ᴳ+ D2) /\ FinAgeOnly (D11 ᴳ+ D12 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
            { apply (Ty_ectxs_LinFinOnly (D11 ᴳ+ D12 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
          assert (LinOnly ((¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2)).
            { apply LinOnly_union_iff; repeat split.
              { apply LinOnly_stimes_forward. exact (IsLinProof (Fin 0)). apply LinOnly_cshift_iff. apply LinOnly_union_iff; repeat split. apply LinOnly_stimes_forward. exact (IsLinProof (Fin 1)). crush.
              assumption. crush. }
              { apply LinOnly_stimes_forward. exact (IsLinProof (Fin 1)). crush. }
              { apply Disjoint_stimes_l_iff. rewrite cshift_distrib_on_union. apply Disjoint_union_l_iff. split. rewrite cshift_distrib_on_stimes. rewrite cshift_by_Disjoint_eq. rewrite Disjoint_stimes_l_iff, Disjoint_stimes_r_iff. crush. crush. apply Disjoint_commutative. rewrite stimes_distrib_union, Disjoint_union_l_iff in H. destruct H as (H & H'). assumption. }
            }
          assert (FinAgeOnly ((¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2)).
            { apply FinAgeOnly_union_forward; repeat split.
              { apply FinAgeOnly_stimes_forward. exact (IsFinAgeProof Lin 0). apply FinAgeOnly_cshift_iff. apply FinAgeOnly_union_forward; repeat split. apply FinAgeOnly_stimes_forward. exact (IsFinAgeProof Lin 1). crush.
              assumption. crush. }
              { apply FinAgeOnly_stimes_forward. exact (IsFinAgeProof Lin 1). crush. }
              { apply Disjoint_stimes_l_iff. rewrite cshift_distrib_on_union. apply Disjoint_union_l_iff. split. rewrite cshift_distrib_on_stimes. rewrite cshift_by_Disjoint_eq. rewrite Disjoint_stimes_l_iff, Disjoint_stimes_r_iff. crush. crush. apply Disjoint_commutative. rewrite stimes_distrib_union, Disjoint_union_l_iff in H. destruct H as (H & H'). assumption. }
            }
          apply term_sub_spec_1 with (T' := T) (D2 := ¹↑ ᴳ· D2).
          all: crush.
        }
      rewrite <- total_cshift_eq.
      rewrite cshift_distrib_on_hminus.
      assert (LinOnly (D11 ᴳ+ D12 ᴳ+ D2)) as LinOnlyD. { apply (Ty_ectxs_LinFinOnly (D11 ᴳ+ D12 ᴳ+ D2) C (U ⧔ T') U0). tauto. }
      assert (hvars©( C) ## hvarsᴳ( ᴳ- D13 ᴳ[ hvarsᴳ( ᴳ- D13) ⩲ (maxᴴ( hvars©( C)) + 1)])) as hvarsDisjoint.
        { rewrite <- cshift_distrib_on_hminus. rewrite total_cshift_eq. apply cshift_by_max_impl_HDisjoint with (h' := maxᴴ(hvars©(C)) + 1); rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; reflexivity. }
      constructor 19 with (D1 := D2 ᴳ+ D11) (D3 := D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) (C := C) (v2 := v2 ᵛ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) (T' := T') (U0 := U0) (U := U) (D2 :=
      D12).
        { apply LinOnly_union_iff. rewrite <- union_associative. rewrite union_commutative. tauto. }
        {
          {  apply Disjoint_union_l_iff. assert (HVars.Subset hvarsᴳ(D11 ᴳ+ D12 ᴳ+ D2) hvars©(C)).
              { apply hvars_C_wk_hvars_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HVars.Subset hvarsᴳ(D2) hvars©(C)).
              { apply HSubset_union_backward with (G := D11 ᴳ+ D12) (G' := D2) (H := hvars©(C)). tauto. }
              assert (maxᴴ(hvarsᴳ(D2)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D2) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D2) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
            { assert (HVars.Subset hvarsᴳ(D11) hvars©(C)).
              { apply HSubset_union_backward in H0. destruct H0. apply HSubset_union_backward in H0. tauto. }
              assert (maxᴴ(hvarsᴳ(D11)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D11) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D11) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
          } } { assert (HVars.Subset hvarsᴳ(D11 ᴳ+ D12 ᴳ+ D2) hvars©(C)).
              { apply hvars_C_wk_hvars_G with (U0 := U0) (T := U ⧔ T'). tauto. }
            { assert (HVars.Subset hvarsᴳ(D12) hvars©(C)).
              { apply HSubset_union_backward with (G := D12) (G' := D2) (H := hvars©(C)). apply HSubset_union_backward with (G := D11). rewrite union_associative. assumption. }
              assert (maxᴴ(hvarsᴳ(D12)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D12) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D12) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { unfold HDisjoint. rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint. crush. assumption.
            } } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite union_commutative in TyC. rewrite union_associative in TyC. tauto. }
          { rewrite <- D12Eq. rewrite <- cshift_distrib_on_hminus. rewrite <- cshift_distrib_on_union. apply TyR_val_cshift. tauto.  } { assumption. }
    - (* Sem-eterm-AOpenUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, TyRv into TyRv1. clear H2.
      inversion TyCc; subst. rename H6 into hvarsDisjoint, D0 into D.
      rewrite <- (nDisposable_in_DestOnly P D DisposP DestOnlyD) in TyRv1.
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = P ᴳ+ D) as eqD1uD3PuD.
        { unfold union, merge_with, merge. apply ext_eq. intros n. all:simpl. rewrite H0. reflexivity. }
      rewrite <- eqD1uD3PuD in *. clear H0. clear eqD1uD3PuD. clear D.
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ hvarsᴳ(ᴳ- D3) ⟨ v2 ❟ v1 ⟩ : U ⧔ T) as TyA.
        { term_Val_no_dispose (D1 ᴳ+ D2). apply Ty_ectxs_HDisjoint_to_Disjoint with (D := D1 ᴳ+ D2) (D' := (ᴳ- D3)) (C := C) (T := U ⧔ T) (U0 := U0) in hvarsDisjoint. apply TyR_val_A. all: trivial. crush.
         }
      assert (LinOnly (D1 ᴳ+ D2) /\ FinAgeOnly (D1 ᴳ+ D2)) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C (U ⧔ T) U0). tauto. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := U ⧔ T) (t := ᵥ₎ hvarsᴳ(ᴳ- D3) ⟨ v2 ❟ v1 ⟩). all: crush.
(*     - (* Sem-eterm-AllocRed *)
      inversion Tyt; subst.
      assert (hvarsᴳ(ᴳ- ᴳ{+ 1 : ¹ν ⌊ U ⌋ ¹ν }) = ᴴ{ 1}) as hvarsD3Eq.
        { cbn. reflexivity. }
      assert (ᴳ{} ⊢ ᵥ₎ ᴴ{ 1} ⟨ ᵛ- 1 ❟ ᵛ+ 1 ⟩ : U ⧔ ⌊ U ⌋ ¹ν) as Tytp.
        { rewrite <- hvarsD3Eq. apply Ty_term_Val. rewrite (union_empty_l_eq ᴳ{}). apply TyR_val_A.
          - crush.
          - crush.
          - intros n b. unfold ctx_singleton. rewrite singleton_MapsTo_iff. rewrite eq_sigT_iff_eq_dep.
            intros []. cbv. tauto.
          - intros n binding. unfold ctx_singleton. rewrite singleton_MapsTo_iff. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (binding = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n binding. unfold ctx_singleton. rewrite singleton_MapsTo_iff. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (binding = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n binding. unfold ctx_singleton. rewrite singleton_MapsTo_iff. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (binding = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - crush.
          - crush.
          - crush.
          - rewrite stimes_empty_eq. rewrite <- union_empty_l_eq. constructor. crush.
          - rewrite <- union_empty_l_eq. rewrite hminus_singleton. constructor.
          - crush.
        }
      constructor 1 with (D := ᴳ{}) (T := U ⧔ ⌊ U ⌋ ¹ν) (t := ᵥ₎ ᴴ{ 1} ⟨ ᵛ- 1 ❟ ᵛ+ 1 ⟩). all: crush. *)
    - (* Sem-eterm-ToAFoc *)
      inversion Tyt; subst.
      rename Tyt into TyToA.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (U ⧔ ①) U0). tauto. }
      constructor 1 with (D := D) (t := u) (T := U); swap 1 3. constructor 9. all: crush.
    - (* Sem-eterm-ToAUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (U ⧔ ①) U0). tauto. }
      assert (D ⊢ to⧔ ᵥ₎ v2 : U ⧔ ①) as TyToA.
        { apply (Ty_term_ToA D (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D) (T := U ⧔ ①) (t := to⧔ ᵥ₎ v2). all: crush.
    - (* Sem-eterm-ToARed *)
      inversion Tyt; subst.
      rename Tyt into TyToA, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      inversion Tyu; subst. rename D into D2.
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyD2) in *.
      assert (ᴳ{} ᴳ+ D2 ⊢ ᵥ₎ hvars_ nil ⟨ v2 ❟ ᵛ() ⟩ : U ⧔ ①).
        { term_Val_no_dispose (ᴳ{} ᴳ+ D2). assert (hvarsᴳ( (ᴳ- ᴳ{})) = hvars_ nil). { crush. } rewrite <- H. apply TyR_val_A; swap 1 11; swap 2 10.
          rewrite hminus_empty_eq. rewrite <- union_empty_r_eq; tauto.
          rewrite stimes_empty_eq. rewrite <- union_empty_r_eq. constructor.
          all:crush. }
      rewrite <- union_empty_l_eq in H.
      constructor 1 with (D := D2) (T := U ⧔ ①) (t := ᵥ₎ hvars_ nil ⟨ v2 ❟ ᵛ() ⟩). all: crush.
    - (* Sem-eterm-FromAFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFromA, T0 into T.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (U ⨂ ! ων ⁔ T) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := U ⧔ ! ων ⁔ T); swap 1 3. constructor 10. all: crush.
    - (* Sem-eterm-FromAUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U, D0 into D. clear H1.
      inversion TyCc; subst. rename U1 into U, v into v2, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyD2) in *.
      assert (LinOnly D2) as LinOnlyD2.
        { apply (Ty_ectxs_LinFinOnly D2 C (U ⨂ ! ων ⁔ T) U0). tauto. }
      assert (D2 ⊢ from⧔ ᵥ₎ v2 : U ⨂ ! ων ⁔ T) as TyFromA.
        { apply (Ty_term_FromA D2 (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D2) (T := (U ⨂ ! ων ⁔ T)) (t := from⧔ ᵥ₎ v2). all: crush.
    - (* Sem-eterm-FromARed *)
      inversion Tyt; subst.
      rename Tyt0 into Tytp, D into D2, ValidOnlyD into ValidOnlyD2 , DestOnlyD into DestOnlyD2, T0 into T.
      inversion Tytp; subst.
      inversion TyRv; subst. rename DestOnlyD2 into DestOnlyPuD1uD2, DestOnlyD0 into DestOnlyD2.
      rewrite (nDisposable_in_DestOnly P (D1 ᴳ+ D2) DisposP DestOnlyPuD1uD2) in *.
      inversion TyRv1. subst.
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = ᴳ{}) as empty.
      { assert (¹↑ ᴳ· D1 ᴳ+ D3 = ων ᴳ· G) as intermediary.
        { apply ext_eq'. symmetry. exact H0. }
        assert (ων ᴳ· G = ᴳ{}).
        2:{ congruence. }
        assert (LinOnly (ων ᴳ· G)) as h_lin.
        2:{ apply LinOnly_stimes_dec in h_lin.
            2:{ trivial. }
            destruct h_lin as [h_lin|h_lin].
            - inversion h_lin.
            - apply stimes_empty_iff. tauto. }
        rewrite <- intermediary.
        rewrite LinOnly_union_iff. repeat split.
        - apply LinOnly_stimes_forward.
          { constructor. }
          apply Ty_ectxs_LinFinOnly in TyC.
          crush.
        - assumption.
        - crush. }
      apply union_empty_iff in empty. destruct empty as [empty_D1 empty_D3].
      apply stimes_empty_iff in empty_D1.
      rewrite empty_D3, hminus_empty_eq, <- union_empty_r_eq in TyRv2.
      assert (D2 ⊢ ᵥ₎ ᵛ( v2, ᴇ ων ⁔ v1) : U ⨂ ! ων ⁔ T).
      { subst. rewrite union_empty_r_eq with (G:=D2).
        term_Val_no_dispose (D2 ᴳ+ ᴳ{}). apply TyR_val_P.
        - assumption.
        - rewrite stimes_empty_eq, <- union_empty_l_eq in TyRv1. assumption. }
      constructor 1 with (D := D2) (T := U ⨂ ! ων ⁔ T) (t := ᵥ₎ ᵛ( v2, ᴇ ων ⁔ v1)). all: crush.
    - (* Sem-eterm-FillUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tyt.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C ① U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ ① ⌋ n); swap 1 3. constructor 11. all: crush.
    - (* Sem-eterm-FillUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C ① U0). tauto. }
      assert (D ⊢ ᵥ₎ v⨞() : ①) as TyFillU.
        { apply (Ty_term_FillU D (ᵥ₎ v) n). tauto. }
      constructor 1 with (D := D) (T := ①) (t := ᵥ₎ v⨞()). all: crush.
    - (* Sem-eterm-FillURed *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tytp.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C ① U0). tauto. }
      inversion Tytp; subst. clear H1.
      inversion TyRv; subst.
      rewrite (nDisposable_in_DestOnly P ᴳ{+ h : ¹ν ⌊ ① ⌋ n} DisposP DestOnlyD) in *.
      assert (ᴳ{} ⊣ C ©️[ h ≔ hvars_ nil ‗ ᵛ()] : ① ↣ U0).
        { assert (ᴳ{} ᴳ+ ¹ν ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- ᴳ{}))) = ᴳ{}) as e1. { crush. }
          rewrite <- e1.
          assert (hvarsᴳ(ᴳ- ᴳ{}) = hvars_ nil) as e2. { crush. }
          rewrite <- e2.
          assert (ᴳ{} ᴳ+ (¹ν · n) ᴳ· ᴳ{} ᴳ+ ᴳ{+ h : ¹ν ⌊ ① ⌋ n} = ᴳ{+ h : ¹ν ⌊ ① ⌋ n}) as e3. { crush. }
          rewrite <- e3 in TyC.
          apply ectxs_fill_spec with (D2 := ᴳ{}) (U := ①); swap 1 14.
          { rewrite <- union_empty_l_eq. rewrite hminus_empty_eq. apply TyR_val_U. }
          all: crush. }
      constructor 1 with (D := ᴳ{}) (T := ①) (t := ᵥ₎ ᵛ()); swap 1 4.
      term_Val_no_dispose (ᴳ{}). apply TyR_val_U. all: crush.
    - (* Sem-eterm-FillLFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFillL, Tyt0 into Tyt.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ T1 ⨁ T2 ⌋ n); swap 1 3. constructor 12. all: crush.
    - (* Sem-eterm-FillLUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      assert (D ⊢ ᵥ₎ v ⨞Inl : ⌊ T1 ⌋ n) as TyFillL.
        { apply (Ty_term_FillL D (ᵥ₎ v) T1 n T2). tauto. }
      constructor 1 with (D := D) (T := ⌊ T1 ⌋ n) (t := ᵥ₎ v ⨞Inl). all: crush.
    - (* Sem-eterm-FillLRed *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillL, Tyt0 into Tytp.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      inversion Tytp; subst. clear H1. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      inversion TyRv; subst; intros hpMaxCh.
      assert (ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1} ‗ Inl ᵛ- (h' + 1)] : ⌊ T1 ⌋ n ↣ U0).
        { assert (ᴳ{} ᴳ+ ¹ν ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν }))) = ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ n }) as e1.
            { rewrite <- union_empty_l_eq. rewrite <- stimes_linnu_eq. rewrite hminus_singleton. rewrite stimes_singleton_hole. rewrite hminus_inv_singleton. rewrite mode_times_linnu_l_eq. tauto. }
          rewrite <- e1.
          assert (hvarsᴳ(ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) = ᴴ{ h' + 1}) as e2. { crush. }
          rewrite <- e2.
          assert (ᴳ{} ᴳ+ (¹ν · n) ᴳ· ᴳ{} ᴳ+ ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n} = ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n}) as e3. { crush. } rewrite <- e3 in TyC.
          apply ectxs_fill_spec with (D2 := ᴳ{}) (D3 := ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) (U := T1 ⨁ T2); swap 1 14.
          { rewrite <- union_empty_l_eq. rewrite hminus_singleton. apply TyR_val_L. constructor. }
          give_up.
    - give_up.
Admitted.

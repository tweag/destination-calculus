Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.Notations.
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
Require Import Arith.
Require Import Dest.Lemmas.

Theorem Progress : forall (C : ectxs) (t : term) (U0 : type), ⊢ C ʲ[t] : U0 -> ((exists v, t = ᵥ₎ v) -> C <> ©️⬜) -> exists (C' : ectxs) (t' : term), C ʲ[t] ⟶ C' ʲ[t'].
Proof.
  intros C t U0 Tyj CNilOrNotValt. inversion Tyj; subst. assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD). { apply (Ty_ectxs_LinOnly_FinAgeOnly D C T U0); tauto. } inversion Tyt; subst.
  inversion TyC; subst. all: try rename TyC into TyCc. all: try rename C0 into C. all: try rename TyC0 into TyC. all: try rename T0 into T. all: try rename D0 into D; try rewrite (nDisposable_in_LinOnly P D DisposP LinOnlyD) in *.
  - exfalso. apply CNilOrNotValt. exists v. all: reflexivity.
  - exists C, ( t' $ ᵥ₎ v). constructor.
  - rename v into v', v0 into v, D into D2, ValidOnlyD into ValidOnlyD2. clear DestOnlyD. exists C, (ᵥ₎ v' $ ᵥ₎ v). constructor.
  - exists C, (ᵥ₎ v ᵗ; u). constructor.
  - exists C, (ᵥ₎ v ►caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). constructor.
  - exists C, (ᵥ₎ v ►caseᵖ m ᵗ( x1, x2) ⟼ u). constructor.
  - exists C, (ᵥ₎ v ►caseᵉ m ᴇ m' ⁔ x ⟼ u). constructor.
  - exists C, (ᵥ₎ v ►map x ⟼ t'). constructor.
  - exists C, (to⧔ (ᵥ₎ v)). constructor.
  - exists C, (from⧔ (ᵥ₎ v)). constructor.
  - exists C, (ᵥ₎ v ⨞()). constructor.
  - exists C, (ᵥ₎ v ⨞Inl). constructor.
  - exists C, (ᵥ₎ v ⨞Inr). constructor.
  - exists C, (ᵥ₎ v ⨞(,)). constructor.
  - exists C, (ᵥ₎ v ⨞ᴇ m). constructor.
  - exists C, (ᵥ₎ v ⨞(λ x ⁔ m ⟼ u)). constructor.
  - exists C, (ᵥ₎ v ⨞· t'). constructor.
  - rename v into v', v0 into v, D into D2, ValidOnlyD into ValidOnlyD2. clear DestOnlyD. exists C, (ᵥ₎ v ⨞· ᵥ₎ v'). constructor.
  - exists C, (ᵥ₎ v ◀ t'). constructor.
  - rename v into v', v0 into v, D into D2, ValidOnlyD into ValidOnlyD2. clear DestOnlyD. exists C, (ᵥ₎ v ◀ ᵥ₎ v'). constructor.
  - rename v into v1, Tyv into Tyv1. exists C, (ᵥ₎ hnamesᴳ(D3) ⟨ v2 ❟ v1 ⟩). constructor.
  - assert (P ᴳ+ ᴳ{ x : m ‗ T} = ᴳ{ x : m ‗ T}) as elimP. { apply nDisposable_in_LinOnly; tauto. } rewrite elimP in *.
    exfalso. unfold DestOnly in DestOnlyD. specialize (DestOnlyD (ˣ x) (ₓ m ‗ T)). unfold ctx_singleton in DestOnlyD. rewrite singleton_MapsTo_at_elt in DestOnlyD. specialize (DestOnlyD eq_refl). unfold IsDest in DestOnlyD. contradiction.
  - rename Tyt into TyApp, T into U, T0 into T, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2.
    destruct (NotVal_dec t). all: try destruct e; subst. all: try rename x into v.
    * destruct (NotVal_dec t'). all: try destruct e; subst. all: try rename x into v'.
      + inversion Tytp; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : T ⁔ m → U ‗ ¹ν}) (h := h) (T := T ⁔ m → U); tauto. }
      exists C, (u ᵗ[x ≔ v]). constructor.
      + exists (C ∘ (v ►⬜)), t'. constructor; tauto.
    * exists (C ∘ ⬜► t'), t. constructor; tauto.
  - rename Tyt into TyPatU, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ① ‗ ¹ν}) (h := h) (T := ①); tauto. } exists C, u. constructor.
    * exists (C ∘ ⬜; u), t. constructor; tauto.
  - rename Tyt into TyPatS, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : T1 ⨁ T2 ‗ ¹ν}) (h := h) (T := T1 ⨁ T2); tauto. }
      { exists C, (u1 ᵗ[x1 ≔ v1]). constructor. }
      { exists C, (u2 ᵗ[x2 ≔ v2]). constructor. }
    * exists (C ∘ (⬜►caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2})), t. constructor; tauto.
  - rename Tyt into TyPatP, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : T1 ⨂ T2 ‗ ¹ν}) (h := h) (T := T1 ⨂ T2); tauto. }
      { exists C, (u ᵗ[x1 ≔ v1] ᵗ[x2 ≔ v2]). constructor. }
    * exists (C ∘ ⬜►caseᵖ m ᵗ( x1, x2)⟼ u), t. constructor; tauto.
  - rename Tyt into TyPatE, T into U, T0 into T, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ! n ⁔ T ‗ ¹ν}) (h := h) (T := ! n ⁔ T); tauto. }
      { exists C, (u ᵗ[x ≔ v']). constructor. }
    * exists (C ∘ ⬜►caseᵉ m ᴇ n ⁔ x ⟼ u), t. constructor; tauto.
  - rename Tyt into TyMap, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : U ⧔ T ‗ ¹ν}) (h := h) (T := U ⧔ T); tauto. }
      rename D2 into D', D0 into D2. assert (LinOnly (P ᴳ+ (D1 ᴳ+ D2))) as LinOnlyPuD1uD2. { crush. } rewrite (nDisposable_in_LinOnly P (D1 ᴳ+ D2) DisposP LinOnlyPuD1uD2) in *.
      exists (C ∘ hnamesᴳ(D3) ᴴ⩲ (maxᴴ(hnamesᴳ( D3) ∪ hnames©(C)) + 1) ᵒᵖ⟨ v2 ᵛ[hnamesᴳ( D3) ⩲ (maxᴴ(hnamesᴳ( D3) ∪ hnames©(C)) + 1)] ❟⬜⟩), (t' ᵗ[x ≔ v1 ᵛ[hnamesᴳ( D3) ⩲ (maxᴴ(hnamesᴳ( D3) ∪ hnames©(C)) + 1)]]). constructor; tauto.
    * exists (C ∘ ⬜►map x ⟼ t'), t. constructor; tauto.
  - rename Tyt into TyToA. destruct (NotVal_dec u).
    * destruct e; subst. rename x into v2. exists C, (ᵥ₎ HNames.empty ⟨ v2 ❟ ᵛ() ⟩ ). constructor.
    * exists (C ∘ to⧔⬜), u. constructor; tauto.
  - rename Tyt into TyToA, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : U ⧔ ! ¹∞ ⁔ T ‗ ¹ν}) (h := h) (T := U ⧔ ! ¹∞ ⁔ T); tauto. }
      inversion Tyv1; subst. { assert (DestOnly (¹↑ ᴳ· D1 ᴳ+ D3)). { crush. } exfalso. apply Ty_val_Hole_DestOnly_contra with (D := (¹↑ ᴳ· D1 ᴳ+ D3)) (h := h) (T := ! ¹∞ ⁔ T). all:tauto. }
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = ᴳ{}) as Empty.
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
          apply Ty_ectxs_LinOnly_FinAgeOnly in TyCc.
          crush.
        - apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & ValidOnlyhiD3). apply LinNuOnly_wk_FinAgeOnly in ValidOnlyhiD3; tauto.
        - crush. }
      apply union_empty_iff in Empty. destruct Empty as [_ EmptyD3].
      subst. rewrite hnames_empty_is_hempty.
      exists C, (ᵥ₎ ᵛ( v2 , ᴇ ¹∞ ⁔ v' )). constructor.
    * exists (C ∘ from⧔⬜), t. constructor; tauto.
  - exists C, (ᵥ₎ ᴴ{ 1 } ⟨ ᵛ+ 1 ❟ ᵛ- 1 ⟩). constructor.
  - rename Tyt into TyFillU, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ ① ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ① ⌋ n); tauto. }
      exists (C ©️[ h ≔ HNames.empty ‗ ᵛ()]), (ᵥ₎ ᵛ()). constructor.
    * exists (C ∘ ⬜⨞()), t. constructor; tauto.
  - rename Tyt into TyFillL, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ Inl ᵛ+ (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ- (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inl), t. constructor; tauto.
  - rename Tyt into TyFillR, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ Inr ᵛ+ (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ- (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inr), t. constructor; tauto.
  - rename Tyt into TyFillP, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ T1 ⨂ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨂ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1 , maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 2} ‗ ᵛ( ᵛ+ (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1), ᵛ+ (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 2))]), (ᵥ₎ ᵛ( ᵛ- (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1), ᵛ- (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 2))). constructor; tauto.
    * exists (C ∘ ⬜⨞(,)), t. constructor; tauto.
  - rename Tyt into TyFillE, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ ! n' ⁔ T ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ! n' ⁔ T ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ ᴇ n' ⁔ ᵛ+ (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ- (maxᴴ( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞ᴇ n'), t. constructor; tauto.
  - rename Tyt into TyFillF, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ T ⁔ m → U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T ⁔ m → U ⌋ n); tauto. }
    exists (C ©️[ h ≔ HNames.empty ‗ ᵛλ x ⁔ m ⟼ u ]), (ᵥ₎ ᵛ()). constructor; tauto.
    * exists (C ∘ ⬜⨞(λ x ⁔ m ⟼ u)), t. constructor; tauto.
  - rename Tyt into TyFillComp, Tyt0 into Tyt, t0 into t, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. destruct (NotVal_dec t').
      + destruct e; subst. rename x into v'. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ U ⌋ ¹ν ‗ ¹ν}) (h := h) (T := ⌊ U ⌋ ¹ν); tauto. } rename H1 into DestOnlyD'. inversion Tytp; subst. rename Tyv0 into Tyvp. inversion Tyvp; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h0 : U ⧔ T ‗ ¹ν}) (h := h0) (T := U ⧔ T); tauto. } assert (LinOnly (P0 ᴳ+ (D1 ᴳ+ D2))) as LinOnlyP0uD1uD2. { crush. } rewrite (nDisposable_in_LinOnly P0 (D1 ᴳ+ D2) DisposP0 LinOnlyP0uD1uD2) in *.
      exists
        ( C ©️[ h ≔ hnamesᴳ( D3) ᴴ⩲ (maxᴴ(hnamesᴳ( D3) ∪ (hnames©(C) ∪ ᴴ{ h})) + 1) ‗  v2 ᵛ[hnamesᴳ( D3) ⩲ (maxᴴ(hnamesᴳ( D3) ∪ (hnames©(C) ∪ ᴴ{ h})) + 1)] ] ),
        (ᵥ₎ v1 ᵛ[hnamesᴳ( D3) ⩲ (maxᴴ(hnamesᴳ( D3) ∪ (hnames©(C) ∪ ᴴ{ h})) + 1)]).
      constructor; tauto.
      + exists (C ∘ v ⨞·⬜), t'. constructor; tauto.
    * exists (C ∘ ⬜⨞· t'), t. constructor; tauto.
  - rename Tyt into TyFillLeft, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. destruct (NotVal_dec t').
      + destruct e; subst. rename x into v'. inversion Tyt; subst. inversion Tyv; subst. { exfalso. apply Ty_val_Hole_DestOnly_contra with (D := ᴳ{+ h : ⌊ T ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T ⌋ n); tauto. } rename H1 into DestOnlyD'. rewrite <- union_associative in *. rewrite (nDisposable_in_LinOnly P (ᴳ{- h : m ⌊ T ⌋ n} ᴳ+ mode_times' ((cons ¹↑ nil) ++ (cons n nil) ++ nil) ᴳ· P2) DisposP LinOnlyD) in *.
      exists
        ( C ©️[ h ≔ HNames.empty ‗  v' ] ),
        (ᵥ₎ ᵛ() ).
      constructor.
      + exists (C ∘ v ◀⬜), t'. constructor; tauto.
    * exists (C ∘ ⬜◀ t'), t. constructor; tauto.
Qed.

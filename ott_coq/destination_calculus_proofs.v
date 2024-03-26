Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.
Require Import Coq.Program.Equality.
Require Import Ott.Finitely.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.

Lemma ValidOnlyUnionBackward : forall (G1 G2 : ctx), ctx_ValidOnly (G1 ⨄ G2) -> ctx_ValidOnly G1 /\ ctx_ValidOnly G2.
Proof. Admitted.
Lemma ValidOnlyUnionForward : forall (G1 G2 : ctx), ctx_ValidOnly G1 -> ctx_ValidOnly G2 -> ctx_Disjoint G1 G2 -> ctx_ValidOnly (G1 ⨄ G2).
Proof. Admitted.
Lemma ValidOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_ValidOnly (m ᴳ· G) <-> ctx_ValidOnly G /\ mode_IsValid m.
Proof. Admitted.
Lemma ValidOnlyMinusEquiv : forall (G : ctx), ctx_ValidOnly (ᴳ-G) <-> ctx_LinNuOnly G /\ ctx_DestOnly G.
Proof. Admitted.
Lemma DestOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_DestOnly (G1 ⨄ G2) <-> ctx_DestOnly G1 /\ ctx_DestOnly G2.
Proof. Admitted.
Lemma DestOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_DestOnly G <-> ctx_DestOnly (m ᴳ· G).
Proof. Admitted.

Lemma LinNuOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinNuOnly (G1 ⨄ G2) <-> ctx_LinNuOnly G1 /\ ctx_LinNuOnly G2 /\ ctx_Disjoint G1 G2.
Proof. Admitted.
Lemma LinNuOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_LinNuOnly (m ᴳ· G) <-> ctx_LinNuOnly G /\ mode_IsLinNu m.
Proof. Admitted.

Lemma LinOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinOnly (G1 ⨄ G2) <-> ctx_LinOnly G1 /\ ctx_LinOnly G2 /\ ctx_Disjoint G1 G2.
Proof. Admitted.
Lemma LinOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_LinOnly (m ᴳ· G) <-> ctx_LinOnly G /\ mode_IsLin m.
Proof. Admitted.

Lemma LinNuOnlyWkLinOnly : forall (G : ctx), ctx_LinNuOnly G -> ctx_LinOnly G.
Proof. Admitted.
Lemma LinOnlyWkValidOnly : forall (G : ctx), ctx_LinOnly G -> ctx_ValidOnly G.
Proof. Admitted.

Lemma IsLinNuWkIsLin : forall (m : mode), mode_IsLinNu m -> mode_IsLin m.
Proof. Admitted.
Lemma IsLinWkIsValid : forall (m : mode), mode_IsLin m -> mode_IsValid m. Proof.
  intros m H. destruct H. apply (mode_IsValidProof (Lin, a)).
Qed.

Lemma DisjointStimesLeftEquiv : forall (m : mode) (D D' : ctx), ctx_Disjoint (m ᴳ· D) D' <-> ctx_Disjoint D D'.
Proof. Admitted.
Lemma DisjointStimesRightEquiv : forall (m : mode) (D D' : ctx), ctx_Disjoint D (m ᴳ· D') <-> ctx_Disjoint D D'.
Proof. Admitted.
Lemma DisjointMinusLeftEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint (ᴳ-D) D'.
Proof. Admitted.
Lemma DisjointMinusRightEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint D (ᴳ-D').
Proof. Admitted.
Lemma DisjointNestedLeftEquiv : forall (D D' D'' : ctx), ctx_Disjoint (D ⨄ D') D'' <-> ctx_Disjoint D D'' /\ ctx_Disjoint D' D''.
Proof. Admitted.
Lemma DisjointNestedRightEquiv : forall (D D' D'' : ctx), ctx_Disjoint D  (D' ⨄ D'') <-> ctx_Disjoint D D' /\ ctx_Disjoint D D''.
Proof. Admitted.

Lemma hdns_DisjointImpliesDisjoint : forall (D D' : ctx) (C : ectxs) (T U0: type) (TyC: D ⊣ C : T ↣ U0) (DisjointCD': hdns_Disjoint hnamesꟲ( C) hnamesᴳ(D')), ctx_Disjoint D D'.
Proof. Admitted.

Lemma EmptyIsLinOnly : ctx_LinOnly ᴳ{}. (* TODO remove when we have actual definition of ctx_ValidOnly *)
Proof. Admitted.

Lemma EmptyUnionLeft : forall (G : ctx), G = G ⨄ ᴳ{}.
Proof. Admitted.
Lemma EmptyUnionRight : forall (G : ctx), G = ᴳ{} ⨄ G.
Proof. Admitted.

Lemma DisjointDestOnlyVar : forall (G : ctx) (x : var) (m : mode) (T : type), ctx_DestOnly G -> ctx_Disjoint G (ᴳ{ x : m ‗ T}).
Proof. Admitted.

Ltac hauto_ctx :=
  hauto
    depth: 3
    use: ValidOnlyUnionBackward, ValidOnlyUnionForward, ValidOnlyStimesEquiv, ValidOnlyMinusEquiv, DestOnlyUnionEquiv, DestOnlyStimesEquiv, LinNuOnlyUnionEquiv, LinNuOnlyStimesEquiv, LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinNuOnlyWkLinOnly, LinOnlyWkValidOnly, IsLinNuWkIsLin, IsLinWkIsValid, DisjointStimesLeftEquiv, DisjointStimesRightEquiv, DisjointMinusLeftEquiv, DisjointMinusRightEquiv, DisjointNestedLeftEquiv, DisjointNestedRightEquiv, hdns_DisjointImpliesDisjoint, EmptyIsLinOnly, EmptyUnionLeft, EmptyUnionRight, DisjointDestOnlyVar.

Lemma Ty_ectxs_LinOnlyD : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), ctx_LinOnly D.
Proof.
  intros D C T U0 H. induction H.
  - apply EmptyIsLinOnly.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - hauto_ctx.
  - assert (ctx_LinOnly (¹↑ ᴳ· D2)) by (hauto l: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, (mode_IsLinProof (Fin 1))).
    assert (ctx_Disjoint (D1 ⨄ D2) (ᴳ-D3)) by (apply (hdns_DisjointImpliesDisjoint (D1 ⨄ D2) (ᴳ-D3) C (T1 ⧔ U) U0); tauto).
    assert (ctx_Disjoint (¹↑ ᴳ· D2) D3) by (sblast use: DisjointNestedLeftEquiv, DisjointMinusRightEquiv, DisjointStimesLeftEquiv).
    rewrite (LinOnlyUnionEquiv (¹↑ ᴳ· D2) D3). split; tauto.
Qed.

Lemma tSubLemma : forall (D1 D2 : ctx) (m : mode) (T1 T2 : type) (t' : term) (x : var) (v : val), ctx_DestOnly D2 -> (D2 ⨄ ᴳ{ x : m ‗ T1} ⊢ t' : T2) -> (D1 ⊢ ᵥ₎ v : T1) -> (m ᴳ· D1 ⨄ D2 ⊢ t' ᵗ[ x ≔ v] : T2). Proof. Admitted.

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - (* Sem-eterm-AppFoc1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C T2 U0); tauto).
      constructor 1 with (D := D1) (T := T1) (t := t); swap 1 3. constructor 2 with (D2 := D2) (m := m) (u := u) (T2 := T2).
      all: hauto_ctx.
    - (* Sem-eterm-AppUnfoc1 *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H0.
      inversion TyCc; subst. clear DestOnlyD0. rename T into T1.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C T2 U0); tauto).
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ u : T2) as TyApp by (apply (Ty_term_App m D1 D2 (ᵥ₎ v) u T2 T1); tauto).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := T2) (t := ᵥ₎ v ≻ u). all: hauto_ctx.
    - (* Sem-eterm-AppFoc2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C T2 U0); tauto).
      constructor 1 with (D := D2) (T := T1 ⁔ m → T2) (t := u); swap 1 3. constructor 3 with (D1 := D1) (m := m) (v := v) (T1 := T1) (T2 := T2). all: hauto_ctx.
    - (* Sem-eterm-AppUnfoc2 *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2. clear H0.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tyu, Tyv into Tyt.
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ ᵥ₎ v' : T2) as TyApp by (apply (Ty_term_App m D1 D2 (ᵥ₎ v) (ᵥ₎ v') T2 T1); tauto).
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C T2 U0); tauto).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := T2) (t := (ᵥ₎ v) ≻ (ᵥ₎ v')). all: hauto_ctx.
    - (* Sem-eterm-AppRed *)
      inversion Tyt; subst.
      assert (m = m0) as Eqmm0 by (inversion_clear Tyu; inversion_clear H0; tauto).
      rewrite <- Eqmm0 in Tyu, Tyt, TyC, DestOnlyD, ValidOnlyD. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into T2, t into t'.
      inversion Tyu; subst. clear H0. rename H2 into TyRv'.
      inversion TyRv'; subst. rename Tyt0 into Tyt'. rename H1 into DestOnlyD2.
      assert (m ᴳ· D1 ⨄ D2 ⊢ t' ᵗ[ x ≔ v] : T2) as Tytpsub by (apply (tSubLemma D1 D2 m T1 T2 t' x v); tauto).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := T2) (t := t' ᵗ[ x ≔ v]). all: hauto_ctx.
    - (* Sem-eterm-PatUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (D1 ⨄ D2) C T2 U0); tauto).
      constructor 1 with (D := D1) (T := 𝟏) (t := t); swap 1 3. constructor 4 with (D2 := D2) (U := T2) (u := u). all: hauto_ctx.
    - (* Sem-eterm-PatUUnfoc *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H0.
      inversion TyCc; subst. clear DestOnlyD0. rename U into T2.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (D1 ⨄ D2) C T2 U0); tauto).
      assert (D1 ⨄ D2 ⊢ ᵥ₎ v ᵗ; u : T2) as TyPat by (apply (Ty_term_PatU D1 D2 (ᵥ₎ v) u T2); tauto).
      constructor 1 with (D := (D1 ⨄ D2)) (T := T2) (t := ᵥ₎ v ᵗ; u). all: hauto_ctx.
    - (* Sem-eterm-PatURed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into T2.
      inversion Tyt; subst. rename H0 into DestOnlyD1, H2 into TyRv.
      inversion TyRv; subst.
      constructor 1 with (D := D2) (T := T2) (t := u). all: hauto_ctx.
    - (* Sem-eterm-PatSFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto).
      constructor 1 with (D := D1) (T := (T1 ⨁ T2)) (t := t) ; swap 1 3. constructor 5 with (D1 := D1) (D2 := D2) (m := m) (u1 := u1) (x1 := x1) (u2 := u2) (x2 := x2) (U := U). all: hauto_ctx.
    - (* Sem-eterm-PatSUnfoc *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H0.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto).
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2} : U) as TyPat by (apply (Ty_term_PatS m D1 D2 (ᵥ₎ v) x1 u1 x2 u2 U T1 T2); hauto_ctx).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). all: hauto_ctx.
    - (* Sem-eterm-PatLRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H0 into DestOnlyD1, H2 into TyRInlv.
      inversion TyRInlv; subst.
      assert (D1 ⊢ ᵥ₎ v : T1) as Tyt' by (apply Ty_term_Val; tauto).
      assert (m ᴳ· D1 ⨄ D2 ⊢ u1 ᵗ[ x1 ≔ v] : U) as Tyusub by (apply (tSubLemma D1 D2 m T1 U u1 x1 v); hauto_ctx).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := u1 ᵗ[ x1 ≔ v]). all: hauto_ctx.
    - (* Sem-eterm-PatRRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H0 into DestOnlyD1, H2 into TyRInlv.
      inversion TyRInlv; subst.
      assert (D1 ⊢ ᵥ₎ v : T2) as Tyt' by (apply Ty_term_Val; tauto).
      assert (m ᴳ· D1 ⨄ D2 ⊢ u2 ᵗ[ x2 ≔ v] : U) as Tyusub by (apply (tSubLemma D1 D2 m T2 U u2 x2 v); hauto_ctx).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := u2 ᵗ[ x2 ≔ v]). all: hauto_ctx.
    - (* Sem-eterm-PatPFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto).
      constructor 1 with (D := D1) (T := (T1 ⨂ T2)) (t := t) ; swap 1 3. constructor 6 with (D1 := D1) (D2 := D2) (u := u) (x1 := x1) (x2 := x2) (U := U). all: hauto_ctx.
    - (* Sem-eterm-PatPUnfoc *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H0.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD by (apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto).
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u : U) as TyPat by (apply (Ty_term_PatP m D1 D2 (ᵥ₎ v) x1 x2 u U T1 T2); hauto_ctx).
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u). all: hauto_ctx.
    - give_up.
Admitted.



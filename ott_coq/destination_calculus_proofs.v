Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.
Require Import Coq.Program.Equality.

Lemma UnionPreservesNames : forall (G1 G2: ctx), (forall (n : name), CtxM.In n G1 -> CtxM.In n (G1 ⨄ G2)) /\ (forall (n : name), CtxM.In n G1 -> CtxM.In n (G1 ⨄ G2)).
Proof. Admitted.
Lemma UnionPreservesNoHole : forall (G1 G2: ctx), ctx_NoHole G1 -> ctx_NoHole G2 -> ctx_NoHole (G1 ⨄ G2).
Proof. Admitted.
Lemma UnionPropagatesInvalidity : forall (G1 G2: ctx), ctx_Valid (G1 ⨄ G2) -> ctx_Valid G1 /\ ctx_Valid G2.
Proof. Admitted.
Lemma UnionPropagatesNoHole : forall (G1 G2: ctx), ctx_NoHole (G1 ⨄ G2) -> ctx_NoHole G1 /\ ctx_NoHole G2.
Proof. Admitted.
Lemma UnionDOVSingVarIsValid : forall (G : ctx) (x : tmv) (m : mode) (T : type), ctx_Valid G -> ctx_DestOnly G -> mode_Valid m -> ctx_Valid (G ⨄ ᶜ{ᵛ x ː m ‗ T}).
Proof. Admitted.

Lemma InteractPropagatesDestOnlyRight : forall (G1 G2: ctx), ctx_DestOnly (G1 ⁻⨄⁺ G2) -> ctx_DestOnly G2.
Proof. Admitted.

Lemma StimesPropagatesNoHole : forall (m : mode) (G : ctx), ctx_NoHole (m ᶜ· G) -> ctx_NoHole G.
Proof. Admitted.
Lemma StimesPreservesValidity : forall (m : mode) (G : ctx), mode_Valid m -> ctx_Valid G -> ctx_Valid (m ᶜ· G).
Proof. Admitted.
Lemma StimesPropagatesInvalidity : forall (m : mode) (G : ctx), ctx_Valid (m ᶜ· G) -> mode_Valid m /\ ctx_Valid G.
Proof. Admitted.

Lemma SubLemma : forall (G1 G2 : ctx) (x : tmv) (m : mode) (T1 T2 : type) (t : term) (v : val), (G1 ⨄ ᶜ{ᵛ x ː m ‗ T2} ᵗ⊢ t ː T1) -> (G2 ᵗ⊢ term_Val v ː T2) -> mode_Valid m -> ctx_Valid (G1 ⨄ (m ᶜ· G2)) -> ((G1 ⨄ (m ᶜ· G2)) ᵗ⊢ t ᵗ[ x ≔ v ] ː T1).
Proof. Admitted.

Lemma BndrInSingleton : forall (b : bndr), CtxM.MapsTo (bndr_name b) b (ᶜ{b}).
Proof.
    intros b. simpl. apply CtxM.add_1. reflexivity.
Qed.

Lemma VarSingletonNoHole : forall (x : tmv) (m : mode) (T : type), ctx_NoHole (ᶜ{ᵛ x ː m ‗ T}).
Proof.
    intros x m T. unfold ctx_NoHole. simpl. intros n b H. unfold ctx_add in H. apply CtxM.find_1 in H. assert (b = ᵛ x ː m ‗ T). admit.
Admitted.

Theorem TypeSafety : forall (G : ctx) (t : term) (T : type), (G ᵗ⊢ t ː T) -> (forall (d : hddyn), exists (v : val) (e : eff), (t ‿ d ⇓ v ⋄ e) /\ (G ᶜ⊢ v ⋄ e ː T)).
Proof.
    intros G t T TYt. destruct TYt as [G t T TYRt ValidG NoHoleG]. induction TYRt.
    - (* TyR_term_H *) admit.
    - (* TyR_term_D *) admit.
    - (* TyR_term_U *) admit.
    - (* TyR_term_L *) admit.
    - (* TyR_term_R *) admit.
    - (* TyR_term_P *) admit.
    - (* TyR_term_E *) admit.
    - (* TyR_term_A *) admit.
    - (* TyR_term_F *) admit.
    - (* TyR_term_Var *) admit.
    - (* TyR_term_App *)
        intros d. rename H into Validm.
        (* Get ctx_Valid G1, ctx_Valid G2 from ctx_Valid (m ᶜ· G1 ⨄ G2) *)
        assert (ctx_Valid (m ᶜ· G1) /\ ctx_Valid G2) as ValidSG1G2. exact (UnionPropagatesInvalidity (m ᶜ· G1) G2 ValidG).
        destruct ValidSG1G2 as [ValidSG1 ValidG2].
        destruct (StimesPropagatesInvalidity m G1) as [Validm' ValidG1].
        exact ValidSG1.
        clear Validm'.
        (* Get ctx_NoHole G1, ctx_noHole G2 from ctx_Valid (m ᶜ· G1 ⨄ G2) *)
        assert (ctx_NoHole (m ᶜ· G1) /\ ctx_NoHole G2) as NoHoleSG1G2. exact (UnionPropagatesNoHole (m ᶜ· G1) G2 NoHoleG).
        destruct NoHoleSG1G2 as [NoHoleSG1 NoHoleG2].
        assert (ctx_NoHole G1) as NoHoleG1. exact (StimesPropagatesNoHole m G1 NoHoleSG1).
        (* Get induction hypothesis and introduce v1 ⋄ e1 for t *)
        assert (forall (d : hddyn), exists (v : val) (e : eff), (t ‿ d ⇓ v ⋄ e /\ G1 ᶜ⊢ v ⋄ e ː T1)) as TSt. exact (IHTYRt1 ValidG1 NoHoleG1).
        destruct (TSt (d.1)) as [v1 TSt'].
        destruct TSt' as [e1 TSt''].
        destruct TSt'' as [REDt TYcmd1].
        (* Get induction hypothesis and introduce v2 ⋄ e2 for u *)
        assert (forall (d : hddyn), exists (v : val) (e : eff), u ‿ d ⇓ v ⋄ e /\ G2 ᶜ⊢ v ⋄ e ː T1 ⁔ m → T2) as TSu. exact (IHTYRt2 ValidG2 NoHoleG2).
        destruct (TSu (d.2)) as [v2 TSu'].
        destruct TSu' as [e2 TSu''].
        destruct TSu'' as [REDu TYcmd2].
        destruct TYcmd1 as [Ge1 Gv1 v1 e1 T1 TYe1 TYv1 DestOnlyGe1v1].
        destruct TYe1 as [Ge1 e1 TYRe1 ValidGe1].
        dependent destruction TYv1. rename G into Gv1, T into T1, TYRt into TYRv1, H into ValidGv1, H0 into NoHoleGv1.
        dependent destruction TYcmd2. rename G1 into Ge2, G2 into Gv2, v into v2, e into e2, TYe into TYe2, TYv into TYv2, H into DestOnlyGe2v2.
        destruct TYe2 as [Ge2 e2 TYRe2 ValidGe2].
        dependent destruction TYv2. rename G into Gv2, TYRt into TYRv2, H into ValidGv2, H0 into NoHoleGv2.
        clear IHTYRt1. clear IHTYRt2. clear TSt. clear TSu.
        (* Canonical form on u *)
        inversion TYRv2.
            (* Prove that u : T1 ⁔ m → T2 cannot be a hole because its context is DestOnly *)
            * rename T into Tf, H into Gv2IsHoleCtx, H1 into v2IsHole, H0 into TfEqT1toT2. rewrite TfEqT1toT2 in Gv2IsHoleCtx. clear TfEqT1toT2. rewrite (eq_sym v2IsHole) in TYRv2, REDu.
              clear Tf. clear v2IsHole. clear v2.
              assert (ctx_DestOnly Gv2) as DestOnlyGv2. exact (InteractPropagatesDestOnlyRight Ge2 Gv2 DestOnlyGe2v2).
              rewrite (eq_sym Gv2IsHoleCtx) in DestOnlyGv2.
              unfold ctx_DestOnly in DestOnlyGv2.
              assert (CtxM.MapsTo (name_HD h) (⁻ h ː ¹ν ‗ T1 ⁔ m → T2) ᶜ{ ⁻ h ː ¹ν ‗ T1 ⁔ m → T2} -> bndr_IsDest (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)). exact (DestOnlyGv2 (name_HD h) (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)).
              assert (CtxM.MapsTo (name_HD h) (⁻ h ː ¹ν ‗ T1 ⁔ m → T2) ᶜ{ ⁻ h ː ¹ν ‗ T1 ⁔ m → T2}). exact (BndrInSingleton (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)).
              assert (bndr_IsDest (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)). exact (H H0). destruct H1.
            (* Case where u is indeed a lambda value *)
            * rename G into Gv2d, t0 into tb, T0 into T1d, m0 into md, T3 into T2d, TYRt into TYRtb, H2 into Validmd, H0 into Gv2dEqGv2, H into LamxtbEqv2, H1 into T1dEqT1, H3 into mdEqm, H4 into T2dEqT2.
              rewrite (eq_sym LamxtbEqv2) in TYRv2, REDu.
              clear mdEqm. clear Validmd. clear T1dEqT1. clear T2dEqT2. clear Gv2dEqGv2. clear md. clear Gv2d. clear T1d. clear T2d.  clear LamxtbEqv2. clear v2.
              assert (ctx_NoHole (ᶜ{ ᵛ x ː m ‗ T1})). unfold ctx_NoHole. intros n H.
              assert (ctx_Valid (m ᶜ· Gv1)) as ValidSGv1. exact (StimesPreservesValidity m Gv1 Validm ValidGv1).
              assert (ctx_Valid (Gv2 ⨄ (m ᶜ· Gv1))) as ValidGv2SGv1. admit. (* TODO: Really not easy *)
              (* Apply SubLemma on u[x := v1] *)
              assert ((Gv2 ⨄ (m ᶜ· Gv1)) ᵗ⊢ tb ᵗ[ x ≔ v1 ] ː T2). exact (SubLemma Gv2 Gv1 x m T2 T1 tb v1 (Ty_term_T (Gv2 ⨄ ᶜ{ ᵛ x ː m ‗ T1}) tb T2 TYRtb (UnionDOVSingVarIsValid Gv2 x m T1 ValidGv2 (InteractPropagatesDestOnlyRight Ge2 Gv2 DestOnlyGe2v2) Validm) (UnionPreservesNoHole Gv2 (ᶜ{ ᵛ x ː m ‗ T1}) NoHoleGv2 (VarSingletonNoHole x m T1))) (Ty_term_T Gv1 (term_Val v1) T1 TYRv1 ValidGv1 NoHoleGv1) Validm ValidGv2SGv1).
              admit.
    - (* TyR_term_PatU *) admit.
    - (* TyR_term_PatS *) admit.
    - (* TyR_term_PatP *) admit.
    - (* TyR_term_PatE *) admit.
    - (* TyR_term_Map *) admit.
    - (* TyR_term_FillC *) admit.
    - (* TyR_term_FillU *) admit.
    - (* TyR_term_FillL *) admit.
    - (* TyR_term_FillR *) admit.
    - (* TyR_term_FillP *) admit.
    - (* TyR_term_FillE *) admit.
    - (* TyR_term_Alloc *) admit.
    - (* TyR_term_ToA *) admit.
    - (* TyR_term_FromA *) admit.
Admitted.

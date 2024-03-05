Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.
Require Import Coq.Program.Equality.
From Hammer Require Import Tactics.

Lemma UnionPreservesNames : forall (G1 G2: ctx), (forall (n : name), CtxM.In n G1 -> CtxM.In n (G1 ⨄ G2)) /\ (forall (n : name), CtxM.In n G2 -> CtxM.In n (G1 ⨄ G2)). Proof. Admitted.
Lemma UnionBackpropagatesNames : forall (G1 G2: ctx), (forall (n : name), CtxM.In n (G1 ⨄ G2) -> CtxM.In n G1 \/ CtxM.In n G2). Proof. Admitted.
Lemma UnionPreservesNoVar : forall (G1 G2: ctx), ctx_NoVar G1 -> ctx_NoVar G2 -> ctx_NoVar (G1 ⨄ G2). Proof. Admitted.
Lemma UnionBackpropagatesNoVar : forall (G1 G2: ctx), ctx_NoVar (G1 ⨄ G2) -> ctx_NoVar G1 * ctx_NoVar G2. Proof. Admitted.
Lemma UnionPreservesNoHole : forall (G1 G2: ctx), ctx_NoHole G1 -> ctx_NoHole G2 -> ctx_NoHole (G1 ⨄ G2). Proof. Admitted.
Lemma UnionBackpropagatesNoHole : forall (G1 G2: ctx), ctx_NoHole (G1 ⨄ G2) -> ctx_NoHole G1 * ctx_NoHole G2. Proof. Admitted.
Lemma UnionPreservesNoDest : forall (G1 G2: ctx), ctx_NoDest G1 -> ctx_NoDest G2 -> ctx_NoDest (G1 ⨄ G2). Proof. Admitted.
Lemma UnionBackpropagatesNoDest : forall (G1 G2: ctx), ctx_NoDest (G1 ⨄ G2) -> ctx_NoDest G1 * ctx_NoDest G2. Proof. Admitted.
Lemma UnionBackpropagatesValidity : forall (G1 G2: ctx), ctx_IsValid (G1 ⨄ G2) -> ctx_IsValid G1 * ctx_IsValid G2. Proof. Admitted.
Lemma UnionPreservesDestOnly : forall (G1 G2: ctx), ctx_DestOnly G1 -> ctx_DestOnly G2 -> ctx_DestOnly (G1 ⨄ G2). Proof. Admitted.
Lemma UnionBackpropagatesDestOnly : forall (G1 G2: ctx), ctx_DestOnly (G1 ⨄ G2) -> ctx_DestOnly G1 * ctx_DestOnly G2. Proof. Admitted.
Lemma UnionPreservesVarOnly : forall (G1 G2: ctx), ctx_VarOnly G1 -> ctx_VarOnly G2 -> ctx_VarOnly (G1 ⨄ G2). Proof. Admitted.
Lemma UnionBackpropagatesVarOnly : forall (G1 G2: ctx), ctx_VarOnly (G1 ⨄ G2) -> ctx_VarOnly G1 * ctx_VarOnly G2. Proof. Admitted.
Lemma UnionPreservesHoleOnly : forall (G1 G2: ctx), ctx_HoleOnly G1 -> ctx_HoleOnly G2 -> ctx_HoleOnly (G1 ⨄ G2). Proof. Admitted.
Lemma UnionBackpropagatesHoleOnly : forall (G1 G2: ctx), ctx_HoleOnly (G1 ⨄ G2) -> ctx_HoleOnly G1 * ctx_HoleOnly G2. Proof. Admitted.
Lemma UnionCommutative : forall (G1 G2: ctx), ctx_IsValid (G1 ⨄ G2) -> G1 ⨄ G2 = G2 ⨄ G1. Proof. Admitted.

Lemma UnionPreservesValidityHole : forall (G1 G2: ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_HoleOnly G1 -> ctx_NoHole G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.
Lemma UnionPreservesValidityVar : forall (G1 G2: ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_VarOnly G1 -> ctx_NoVar G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.
Lemma UnionPreservesValidityDest : forall (G1 G2: ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_DestOnly G1 -> ctx_NoDest G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.

Definition equivT (A B : Type) : Type := (A -> B) * (B -> A).

Lemma VarOnlyNoHoleNoDestEquiv : forall (G : ctx), equivT (ctx_VarOnly G) (ctx_NoHole G * ctx_NoDest G). Proof. Admitted.
Lemma DestOnlyNoVarNoHoleEquiv : forall (G : ctx), equivT (ctx_DestOnly G) (ctx_NoVar G * ctx_NoHole G). Proof. Admitted.
Lemma HoleOnlyNoVarNoDestEquiv : forall (G : ctx), equivT (ctx_HoleOnly G) (ctx_NoVar G * ctx_NoDest G). Proof. Admitted.

Lemma InteractPreservesNames : forall (G1 G2: ctx),
    (
        forall (n : name) (b:bndr),
        CtxM.MapsTo n b G1 ->
            CtxM.In n (G1 ⁻⨄⁺ G2) +
            (sigT2 (fun b' => CtxM.MapsTo n b' G2) (fun b' => (bndr_Interact b b')))
    ) * (
        forall (n : name) (b':bndr),
        CtxM.MapsTo n b' G2 ->
            CtxM.In n (G1 ⁻⨄⁺ G2) +
            (sigT2 (fun b => CtxM.MapsTo n b G1) (fun b => (bndr_Interact b b')))
    ).
Proof. Admitted.
Lemma InteractIsUnion : forall (G1 G2: ctx), ((ctx_NoHole G1) + (ctx_NoDest G2)) -> G1 ⁻⨄⁺ G2 = G1 ⨄ G2. Proof. Admitted.
Lemma InteractBackpropagatesNames : forall (G1 G2: ctx), (forall (n : name), CtxM.In n (G1 ⁻⨄⁺ G2) -> CtxM.In n G1 \/ CtxM.In n G2). Proof. Admitted.
Lemma InteractPreservesNoVar : forall (G1 G2: ctx), ctx_NoVar G1 -> ctx_NoVar G2 -> ctx_NoVar (G1 ⁻⨄⁺ G2). Proof. Admitted.
Lemma InteractBackpropagatesNoVar : forall (G1 G2: ctx), ctx_NoVar (G1 ⁻⨄⁺ G2) -> ctx_NoVar G1 * ctx_NoVar G2. Proof. Admitted.
Lemma InteractPreservesNoHole : forall (G1 G2: ctx), ctx_NoHole G1 -> ctx_NoHole G2 -> ctx_NoHole (G1 ⁻⨄⁺ G2). Proof. Admitted.
Lemma InteractBackpropagatesNoHole : forall (G1 G2: ctx), ctx_NoHole (G1 ⁻⨄⁺ G2) -> ctx_NoHole G2. Proof. Admitted.
Lemma InteractPreservesNoDest : forall (G1 G2: ctx), ctx_NoDest G1 -> ctx_NoDest G2 -> ctx_NoDest (G1 ⁻⨄⁺ G2). Proof. Admitted.
Lemma InteractBackpropagatesNoDest : forall (G1 G2: ctx), ctx_NoDest (G1 ⁻⨄⁺ G2) -> ctx_NoDest G1. Proof. Admitted.
Lemma InteractBackpropagatesValidity : forall (G1 G2: ctx), ctx_IsValid (G1 ⁻⨄⁺ G2) -> ctx_IsValid G1 * ctx_IsValid G2. Proof. Admitted.
Lemma InteractPreservesDestOnly : forall (G1 G2: ctx), ctx_DestOnly G1 -> ctx_DestOnly G2 -> ctx_DestOnly (G1 ⁻⨄⁺ G2). Proof. Admitted.
Lemma InteractBackpropagatesDestOnly : forall (G1 G2: ctx), ctx_DestOnly (G1 ⁻⨄⁺ G2) -> ctx_DestOnly G2. Proof. Admitted.
Lemma InteractPreservesVarOnly : forall (G1 G2: ctx), ctx_VarOnly G1 -> ctx_VarOnly G2 -> ctx_VarOnly (G1 ⁻⨄⁺ G2). Proof. Admitted.
Lemma InteractBackpropagatesVarOnly : forall (G1 G2: ctx), ctx_VarOnly (G1 ⁻⨄⁺ G2) -> ctx_VarOnly G1 * ctx_VarOnly G2. Proof. Admitted.
Lemma InteractPreservesHoleOnly : forall (G1 G2: ctx), ctx_HoleOnly G1 -> ctx_HoleOnly G2 -> ctx_HoleOnly (G1 ⁻⨄⁺ G2). Proof. Admitted.
Lemma InteractBackpropagatesHoleOnly : forall (G1 G2: ctx), ctx_HoleOnly (G1 ⁻⨄⁺ G2) -> ctx_HoleOnly G1. Proof. Admitted.

Lemma InteractBackpropagatesDestOnlyRight : forall (G1 G2: ctx), ctx_DestOnly (G1 ⁻⨄⁺ G2) -> ctx_DestOnly G2.
Proof. Admitted.

Lemma StimesPreservesNames : forall (m : mode) (G : ctx), (forall (n : name), CtxM.In n G -> CtxM.In n (m ᶜ· G)). Proof. Admitted.
Lemma StimesBackpropagatesNames : forall (m : mode) (G : ctx), (forall (n : name), CtxM.In n (m ᶜ· G) -> CtxM.In n G). Proof. Admitted.
Lemma StimesPreservesNoVar : forall (m : mode) (G : ctx), ctx_NoVar G -> ctx_NoVar (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesNoVar : forall (m : mode) (G : ctx), ctx_NoVar (m ᶜ· G) -> ctx_NoVar G. Proof. Admitted.
Lemma StimesPreservesNoHole : forall (m : mode) (G : ctx), ctx_NoHole G -> ctx_NoHole (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesNoHole : forall (m : mode) (G : ctx), ctx_NoHole (m ᶜ· G) -> ctx_NoHole G. Proof. Admitted.
Lemma StimesPreservesNoDest : forall (m : mode) (G : ctx), ctx_NoDest G -> ctx_NoDest (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesNoDest : forall (m : mode) (G : ctx), ctx_NoDest (m ᶜ· G) -> ctx_NoDest G. Proof. Admitted.
Lemma StimesPreservesValidity : forall (m : mode) (G : ctx), mode_IsValid m -> ctx_IsValid G -> ctx_IsValid (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesValidity : forall (m : mode) (G : ctx), ctx_IsValid (m ᶜ· G) -> mode_IsValid m * ctx_IsValid G. Proof. Admitted.
Lemma StimesPreservesDestOnly : forall (m : mode) (G : ctx), ctx_DestOnly G -> ctx_DestOnly (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesDestOnly : forall (m : mode) (G : ctx), ctx_DestOnly (m ᶜ· G) -> ctx_DestOnly G. Proof. Admitted.
Lemma StimesPreservesVarOnly : forall (m : mode) (G : ctx), ctx_VarOnly G -> ctx_VarOnly (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesVarOnly : forall (m : mode) (G : ctx), ctx_VarOnly (m ᶜ· G) -> ctx_VarOnly G. Proof. Admitted.
Lemma StimesPreservesHoleOnly : forall (m : mode) (G : ctx), ctx_HoleOnly G -> ctx_HoleOnly (m ᶜ· G). Proof. Admitted.
Lemma StimesBackpropagatesHoleOnly : forall (m : mode) (G : ctx), ctx_HoleOnly (m ᶜ· G) -> ctx_HoleOnly G. Proof. Admitted.

Lemma BndrInSingleton : forall (b : bndr), CtxM.MapsTo (bndr_name b) b (ᶜ{b}).
Proof.
    intros b. simpl. apply CtxM.add_1. reflexivity.
Qed.

Lemma SubLemma : forall (G1 G2 : ctx) (x : tmv) (m : mode) (T1 T2 : type) (t : term) (v : val), (G1 ⨄ ᶜ{ᵛ x ː m ‗ T2} ᵗ⊢ t ː T1) -> (G2 ᵗ⊢ term_Val v ː T2) -> mode_IsValid m -> ctx_IsValid (G1 ⨄ (m ᶜ· G2)) -> ((G1 ⨄ (m ᶜ· G2)) ᵗ⊢ t ᵗ[ x ≔ v ] ː T1).
Proof. Admitted.

Axiom ProofAbsurd : forall (P : Prop), (~P -> False) -> P.

Axiom not_forall_exists_negation : forall (A : Type) (P : A -> Prop),
  ~(forall x, P x) <-> exists x, ~P x.

Axiom not_implies : forall (P Q : Prop), (~(P -> Q)) -> (P /\ ~Q).

(* Missing ctx_DestOnly G in hypotheses? *)
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
        (* Get ctx_IsValid G1, ctx_IsValid G2 from ctx_IsValid (m ᶜ· G1 ⨄ G2) *)
        assert (ctx_IsValid (m ᶜ· G1) * ctx_IsValid G2) as ValidSG1G2. exact (UnionBackpropagatesValidity (m ᶜ· G1) G2 ValidG).
        destruct ValidSG1G2 as [ValidSG1 ValidG2].
        destruct (StimesBackpropagatesValidity m G1) as [Validm' ValidG1].
        exact ValidSG1.
        clear Validm'.
        (* Get ctx_NoHole G1, ctx_noHole G2 from ctx_IsValid (m ᶜ· G1 ⨄ G2) *)
        assert (ctx_NoHole (m ᶜ· G1) * ctx_NoHole G2) as NoHoleSG1G2. exact (UnionBackpropagatesNoHole (m ᶜ· G1) G2 NoHoleG).
        destruct NoHoleSG1G2 as [NoHoleSG1 NoHoleG2].
        assert (ctx_NoHole G1) as NoHoleG1. exact (StimesBackpropagatesNoHole m G1 NoHoleSG1).
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
              assert (ctx_DestOnly Gv2) as DestOnlyGv2. exact (InteractBackpropagatesDestOnlyRight Ge2 Gv2 DestOnlyGe2v2).
              rewrite (eq_sym Gv2IsHoleCtx) in DestOnlyGv2.
              unfold ctx_DestOnly in DestOnlyGv2.
              assert (CtxM.MapsTo (name_HD h) (⁻ h ː ¹ν ‗ T1 ⁔ m → T2) ᶜ{ ⁻ h ː ¹ν ‗ T1 ⁔ m → T2} -> bndr_IsDest (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)). exact (DestOnlyGv2 (name_HD h) (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)).
              assert (CtxM.MapsTo (name_HD h) (⁻ h ː ¹ν ‗ T1 ⁔ m → T2) ᶜ{ ⁻ h ː ¹ν ‗ T1 ⁔ m → T2}). exact (BndrInSingleton (⁻ h ː ¹ν ‗ T1 ⁔ m → T2)).
              assert (exists h0 m0 T n, ᶜ{ ⁻ h ː ¹ν ‗ T1 ⁔ m → T2} = ᶜ{ ⁺ h0 ː m0 ⌊ T ⌋ n}). destruct (H H0). exists h0, m0, T, n. tauto.
              (* Proof that singleton contexts with two different bndr are not equal *)
              destruct H1 as (h0 & m0 & T & n & H1). unfold ctx_from_list, fold_right, ctx_add, bndr_name in H1. simpl in H1. unfold CtxM.add in H1. simpl in H1. congruence.
            (* Case where u is indeed a lambda value *)
            * rename G into Gv2d, t0 into tb, T0 into T1d, m0 into md, T3 into T2d, TYRt into TYRtb, H2 into Validmd, H0 into Gv2dEqGv2, H into LamxtbEqv2, H1 into T1dEqT1, H3 into mdEqm, H4 into T2dEqT2.
              rewrite (eq_sym LamxtbEqv2) in TYRv2, REDu.
              clear mdEqm. clear Validmd. clear T1dEqT1. clear T2dEqT2. clear Gv2dEqGv2. clear md. clear Gv2d. clear T1d. clear T2d.  clear LamxtbEqv2. clear v2.
              assert (ctx_IsValid (m ᶜ· Gv1)) as ValidSGv1. exact (StimesPreservesValidity m Gv1 Validm ValidGv1).
              assert (ctx_IsValid (Gv2 ⨄ (m ᶜ· Gv1))) as ValidGv2SGv1.
                (*
                Idea of the proof:
                - Hole names in Ge2 can only have prefix d.2
                - Hole names in Ge1 can only have prefix d.1
                - Bindings that ⁻⨄⁺ erases from Gv1 in Ge1 ⁻⨄⁺ Gv1 are those matching Ge1 holes, thus must have prefix d.1
                - Bindings that ⁻⨄⁺ erases from Gv2 in Ge2 ⁻⨄⁺ Gv2 are those matching Ge2 holes, thus must have prefix d.2
                - We have that the union of interacts is valid. So removing Ge1 and Ge2 from sides of the union cannot make it invalid. The only potential source of invalidity are bindings removed by interact from Gv1 thanks to interaction with Ge1, and from Gv2 thanks to interaction with Ge2, that are no longer erased, and could conflict. But we proved that they cannot overlap because of name prefixes. So the union is valid
                *)
                admit. (* TODO: Really not easy *)
              (* Apply SubLemma on u[x := v1] *)
              assert ((Gv2 ⨄ (m ᶜ· Gv1)) ᵗ⊢ tb ᵗ[ x ≔ v1 ] ː T2).
                assert (ctx_IsValid ᶜ{ ᵛ x ː m ‗ T1}) as ValidXSing. unfold ctx_IsValid. intros n' b' MapsTo. unfold CtxM.MapsTo in MapsTo. simpl in MapsTo. unfold CtxM.Raw.PX.MapsTo in MapsTo. simpl in MapsTo. dependent destruction MapsTo. destruct H. simpl in H. simpl in H0. rewrite H0. simpl. exact Validm. inversion MapsTo.
                assert (ctx_NoDest ᶜ{ ᵛ x ː m ‗ T1}) as NoDestXSing. unfold ctx_NoDest. intros n' b' MapsTo. unfold CtxM.MapsTo in MapsTo. simpl in MapsTo. unfold CtxM.Raw.PX.MapsTo in MapsTo. simpl in MapsTo. dependent destruction MapsTo. destruct H. simpl in H. simpl in H0. rewrite H0. unfold not. intros IsDest. dependent destruction IsDest. inversion MapsTo.
                assert (ctx_NoHole ᶜ{ ᵛ x ː m ‗ T1}) as NoHoleXSing. unfold ctx_NoHole. intros n' b' MapsTo. unfold CtxM.MapsTo in MapsTo. simpl in MapsTo. unfold CtxM.Raw.PX.MapsTo in MapsTo. simpl in MapsTo. dependent destruction MapsTo. destruct H. simpl in H. simpl in H0. rewrite H0. unfold not. intros IsHole. dependent destruction IsHole. inversion MapsTo.
              exact (SubLemma Gv2 Gv1 x m T2 T1 tb v1 (Ty_term_T (Gv2 ⨄ ᶜ{ ᵛ x ː m ‗ T1}) tb T2 TYRtb (UnionPreservesValidityDest Gv2 ᶜ{ ᵛ x ː m ‗ T1} ValidGv2 ValidXSing (InteractBackpropagatesDestOnly Ge2 Gv2 DestOnlyGe2v2) (NoDestXSing)) (UnionPreservesNoHole Gv2 (ᶜ{ ᵛ x ː m ‗ T1}) NoHoleGv2 NoHoleXSing)) (Ty_term_T Gv1 (term_Val v1) T1 TYRv1 ValidGv1 NoHoleGv1) Validm ValidGv2SGv1).

              
              
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

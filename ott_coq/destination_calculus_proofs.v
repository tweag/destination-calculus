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

Lemma ValidOnlyUnionBackward : forall (G1 G2 : ctx), ctx_ValidOnly (G1 ⨄ G2) -> ctx_ValidOnly G1 /\ ctx_ValidOnly G2.
Proof. Admitted.
Lemma ValidOnlyUnionBackward' : forall (G1 G2 : ctx), Basics.impl (ctx_ValidOnly (G1 ⨄ G2)) (ctx_ValidOnly G1 /\ ctx_ValidOnly G2).
Proof.
  exact ValidOnlyUnionBackward.
Qed.
Hint Rewrite ValidOnlyUnionBackward' : propagate_down.

Lemma ValidOnlyUnionForward : forall (G1 G2 : ctx), ctx_ValidOnly G1 -> ctx_ValidOnly G2 -> ctx_Disjoint G1 G2 -> ctx_ValidOnly (G1 ⨄ G2).
Proof.
  intros * valid_G1 valid_G2 disjoint_G1G2. unfold ctx_ValidOnly in *.
  intros n b h. unfold ctx_union in *.
  destruct (In_dec n G1) as [[b1 h_inG1]|h_ninG1]; destruct (In_dec n G2) as [[b2 h_inG2]|h_ninG2]. all: rewrite ?In_None2 in *.
  - sfirstorder unfold: ctx_Disjoint.
  - hauto lq: on use: merge_with_spec_2.
  - hauto lq: on use: merge_with_spec_3.
  - hauto lq: on use: merge_with_spec_4.
Qed.
Lemma ValidOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_ValidOnly (m ᴳ· G) <-> ctx_ValidOnly G /\ mode_IsValid m.
Proof. Admitted.
Hint Rewrite ValidOnlyStimesEquiv : propagate_down.
Lemma ValidOnlyMinusEquiv : forall (G : ctx), ctx_ValidOnly (ᴳ-G) <-> ctx_LinNuOnly G /\ ctx_DestOnly G.
Proof. Admitted.
Hint Rewrite ValidOnlyMinusEquiv : propagate_down.
Lemma ValidOnlyHdnShiftEquiv: forall (G : ctx) (H : hdns) (h' : hdn), ctx_ValidOnly G <-> ctx_ValidOnly (G ᴳ[ H⩲h' ]).
Proof. Admitted.
Hint Rewrite <- ValidOnlyHdnShiftEquiv : propagate_down.

Lemma DestOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_DestOnly (G1 ⨄ G2) <-> ctx_DestOnly G1 /\ ctx_DestOnly G2.
Proof. Admitted.
Hint Rewrite DestOnlyUnionEquiv : propagate_down.
Lemma DestOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_DestOnly G <-> ctx_DestOnly (m ᴳ· G).
Proof. Admitted.
Hint Rewrite <- DestOnlyStimesEquiv : propagate_down.
Lemma DestOnlyHdnShiftEquiv: forall (G : ctx) (H : hdns) (h' : hdn), ctx_DestOnly G <-> ctx_DestOnly (G ᴳ[ H⩲h' ]).
Proof. Admitted.
Hint Rewrite <- DestOnlyHdnShiftEquiv : propagate_down.

Lemma mode_plus_not_lin_nu : forall b1 b2, ~mode_IsLinNu (mode_plus b1 b2).
Proof.
  intros [[q1 [a1|]]|].
  2:{ cbn. hauto lq: on. }
  2:{ cbn. hauto lq: on. }
  intros [[q2 [a2|]]|].
  2:{ cbn. hauto lq: on. }
  2:{ cbn. hauto lq: on. }
  cbn.
  destruct (HdnsM.MF.eq_dec a1 a2) as [?|?].
  2:{ cbn. hauto lq: on. }
  inversion 1.
Qed.

Lemma LinNuOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinNuOnly (G1 ⨄ G2) <-> ctx_LinNuOnly G1 /\ ctx_LinNuOnly G2 /\ ctx_Disjoint G1 G2.
Proof.
  intros *. unfold ctx_LinNuOnly.
  split.
  - intros h. unfold ctx_union in h.
    assert (forall n,
               (forall (tyb : binding_type_of n), G1 n = Some tyb -> mode_IsLinNu (tyb_mode tyb)) /\
               (forall (tyb : binding_type_of n), G2 n = Some tyb -> mode_IsLinNu (tyb_mode tyb)) /\
               (In n G1 -> In n G2 -> False)).
    2:{ hauto lq: on unfold: ctx_Disjoint. }
    intros n. specialize (h n).
    destruct (In_dec n G1) as [[b1 h_inG1]|h_ninG1]; destruct (In_dec n G2) as [[b2 h_inG2]|h_ninG2]. all: rewrite ?In_None2 in *.
    2:{ fcrush use: merge_with_spec_2. }
    2:{ fcrush use: merge_with_spec_3. }
    2:{ (* The hammer gets lost for some reason*)
        erewrite merge_with_spec_4 in h.
        2: { eauto. }
        sauto. }
    erewrite merge_with_spec_1 in h.
    2:{ eauto. }
    destruct n as [xx|xh]. all: cbn in *.
    + assert (mode_IsLinNu match union_tyb_var b1 b2 with ₓ m ‗ _ => m end) as h'.
      { eauto. }
      destruct b1 as [m1 t1]; destruct b2 as [m2 t2]. cbn in *.
      destruct (type_eq_dec t1 t2) as [?|?].
      2:{ inversion h'. }
      apply mode_plus_not_lin_nu in h'.
      destruct h'.
    + assert (mode_IsLinNu match union_tyb_dh b1 b2 with ₊ m ⌊ _ ⌋ _ => m | ₋ _ ‗ n => n end) as h'.
      { eauto. }
      destruct b1 as [m1 t1 n1|t1 n1]; destruct b2 as [m2 t2 n2|t2 n2]. all: cbn in *.
      all: destruct (type_eq_dec t1 t2) as [?|?].
      (* disgusting: *)
      all: try solve [inversion h'].
      * destruct (mode_eq_dec n1 n2) as [?|?].
        2:{ inversion h'. }
        apply mode_plus_not_lin_nu in h'.
        destruct h'.
      * apply mode_plus_not_lin_nu in h'.
        destruct h'.
  - intros [h_G1 [h_G2 h_disjoint]] n b h_union.
    unfold ctx_union in *.
    destruct (In_dec n G1) as [[b1 h_inG1]|h_ninG1]; destruct (In_dec n G2) as [[b2 h_inG2]|h_ninG2]. all: rewrite ?In_None2 in *.
    + sfirstorder unfold: ctx_Disjoint.
    + hauto lq: on use: merge_with_spec_2.
    + hauto lq: on use: merge_with_spec_3.
    + hauto lq: on use: merge_with_spec_4.
Qed.
Hint Rewrite LinNuOnlyUnionEquiv : propagate_down.

Lemma LinNuOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_LinNuOnly (m ᴳ· G) <-> ctx_LinNuOnly G /\ mode_IsLinNu m.
Proof. Admitted.
Hint Rewrite LinNuOnlyStimesEquiv : propagate_down.
Lemma LinNuOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_LinNuOnly G <-> ctx_LinNuOnly (G ᴳ[ H⩲h' ]).
Proof. Admitted.
Hint Rewrite <- LinNuOnlyHdnShiftEquiv : propagate_down.

Lemma LinOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinOnly (G1 ⨄ G2) <-> ctx_LinOnly G1 /\ ctx_LinOnly G2 /\ ctx_Disjoint G1 G2.
Proof. Admitted.
Hint Rewrite LinOnlyUnionEquiv : propagate_down.

Lemma LinOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_LinOnly (m ᴳ· G) <-> ctx_LinOnly G /\ mode_IsLin m.
Proof. Admitted.
Hint Rewrite LinOnlyStimesEquiv : propagate_down.
Lemma LinOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_LinOnly G <-> ctx_LinOnly (G ᴳ[ H⩲h' ]).
Proof. Admitted.
Hint Rewrite <- LinOnlyHdnShiftEquiv : propagate_down.

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
Hint Rewrite DisjointStimesLeftEquiv : propagate_down.

Lemma DisjointStimesRightEquiv : forall (m : mode) (D D' : ctx), ctx_Disjoint D (m ᴳ· D') <-> ctx_Disjoint D D'.
Proof. Admitted.
Hint Rewrite DisjointStimesRightEquiv : propagate_down.

Lemma DisjointMinusLeftEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint (ᴳ-D) D'.
Proof. Admitted.
Hint Rewrite <- DisjointMinusLeftEquiv : propagate_down.

Lemma DisjointMinusRightEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint D (ᴳ-D').
Proof. Admitted.
Hint Rewrite <- DisjointMinusRightEquiv : propagate_down.

Lemma DisjointNestedLeftEquiv : forall (D D' D'' : ctx), ctx_Disjoint (D ⨄ D') D'' <-> ctx_Disjoint D D'' /\ ctx_Disjoint D' D''.
Proof. Admitted.
Hint Rewrite DisjointNestedLeftEquiv : propagate_down.

Lemma DisjointNestedRightEquiv : forall (D D' D'' : ctx), ctx_Disjoint D  (D' ⨄ D'') <-> ctx_Disjoint D D' /\ ctx_Disjoint D D''.
Proof. Admitted.
Hint Rewrite DisjointNestedRightEquiv : propagate_down.
Lemma DisjointHdnShiftEq : forall (D D': ctx) (h': hdn), ctx_Disjoint D D' -> D ᴳ[ hnamesᴳ( D' ) ⩲ h' ] = D.
Proof. Admitted.

Lemma EmptyIsLinOnly : ctx_LinOnly ᴳ{}. (* TODO remove when we have actual definition of ctx_ValidOnly *)
Proof. Admitted.

Lemma EmptyUnionRight : forall (G : ctx), G = G ⨄ ᴳ{}.
Proof. Admitted.
Lemma EmptyUnionLeft : forall (G : ctx), G = ᴳ{} ⨄ G.
Proof. Admitted.

Lemma DisjointDestOnlyVar : forall (G : ctx) (x : var) (m : mode) (T : type), ctx_DestOnly G -> ctx_Disjoint G (ᴳ{ x : m ‗ T}).
Proof. Admitted.

Lemma UnionCommutative : forall (G1 G2 : ctx), G1 ⨄ G2 = G2 ⨄ G1.
Proof. Admitted.
Lemma UnionAssociative : forall (G1 G2 G3 : ctx), G1 ⨄ (G2 ⨄ G3) = (G1 ⨄ G2) ⨄ G3.
Proof. Admitted.

Lemma UnionHdnShiftEq : forall (G1 G2 : ctx) (H : hdns) (h' : hdn), (G1 ⨄ G2)ᴳ[ H⩲h' ] = G1 ᴳ[ H⩲h' ] ⨄ G2 ᴳ[ H⩲h' ].
Proof. Admitted.
Lemma StimesHdnShiftEq : forall (m : mode) (G : ctx) (H : hdns) (h' : hdn), (m ᴳ· G)ᴳ[ H⩲h' ] = m ᴳ· (G ᴳ[ H⩲h' ]).
Proof. Admitted.

Lemma StimesIsAction : forall (m n : mode) (G : ctx), m ᴳ· (n ᴳ· G) = (m · n) ᴳ· G.
Proof. Admitted.
Lemma StimesUnionDistributive : forall (m : mode) (G1 G2 : ctx),  m ᴳ· (G1 ⨄ G2) = m ᴳ· G1 ⨄ m ᴳ· G2.
Proof. Admitted.
Lemma StimesIdentity :  forall (G: ctx), G = ¹ν ᴳ· G.
Proof. Admitted.

Lemma TimesCommutative : forall (m n : mode), m · n = n · m.
Proof. Admitted.
Lemma TimesAssociative : forall (m1 m2 m3 : mode), m1 · (m2 · m3) = (m1 · m2) · m3.
Proof. Admitted.
Lemma TimesIdentityRight : forall (m : mode), m · ¹ν = m.
Proof. Admitted.
Lemma TimesIdentityLeft : forall (m : mode), ¹ν · m = m.
Proof. Admitted.

Lemma hnames_CWkhnames_G : forall (C : ectxs) (D : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), HdnsM.Subset hnamesᴳ(D) hnamesꟲ(C).
Proof. Admitted.

Lemma hnames_DisjointToDisjoint : forall (D D' : ctx), ctx_DestOnly D -> ctx_DestOnly D' -> hdns_Disjoint hnamesᴳ(D) hnamesᴳ(D') -> ctx_Disjoint D D'.
Proof. Admitted.

Lemma hdns_max_hnames_Disjoint : forall (H H' : hdns) (h' : hdn), ʰmax(H) <= h' -> hdns_Disjoint H (H' ᴴ⩲ h').
Proof. Admitted.

Lemma SubsetCtxUnionBackward : forall (G G': ctx) (H: hdns), HdnsM.Subset hnamesᴳ(G ⨄ G') H -> HdnsM.Subset hnamesᴳ(G) H /\ HdnsM.Subset hnamesᴳ(G') H.
Proof. Admitted.

Lemma HmaxSubset : forall (H H' : hdns), HdnsM.Subset H H' -> ʰmax(H) <= ʰmax(H').
Proof. Admitted.

Lemma hnamesMinusEq : forall (D : ctx), hnamesᴳ( ᴳ- D) = hnamesᴳ( D).
Proof. Admitted.
Lemma hnamesFullShiftEq : forall (G : ctx) (h' : hdn), hnamesᴳ(G ᴳ[ hnamesᴳ( G ) ⩲ h' ]) = hnamesᴳ(G) ᴴ⩲ h'.
Proof. Admitted.
Lemma MinusHdnShiftEq : forall (G : ctx) (H : hdns) (h' : hdn), (ᴳ- G) ᴳ[ H ⩲ h' ] = ᴳ- (G ᴳ[ H ⩲ h' ]).
Proof. Admitted.

Ltac hauto_ctx :=
  hauto
    depth: 3
    use: ValidOnlyUnionBackward, ValidOnlyUnionForward, ValidOnlyStimesEquiv, ValidOnlyMinusEquiv, ValidOnlyHdnShiftEquiv, DestOnlyUnionEquiv, DestOnlyStimesEquiv, DestOnlyHdnShiftEquiv, LinNuOnlyUnionEquiv, LinNuOnlyStimesEquiv, LinNuOnlyHdnShiftEquiv, LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyHdnShiftEquiv, LinNuOnlyWkLinOnly, LinOnlyWkValidOnly, IsLinNuWkIsLin, IsLinWkIsValid, DisjointStimesLeftEquiv, DisjointStimesRightEquiv, DisjointMinusLeftEquiv, DisjointMinusRightEquiv, DisjointNestedLeftEquiv, DisjointNestedRightEquiv, DisjointHdnShiftEq, EmptyIsLinOnly, EmptyUnionLeft, EmptyUnionRight, DisjointDestOnlyVar, UnionCommutative, UnionAssociative, UnionHdnShiftEq, StimesHdnShiftEq, StimesIsAction, StimesUnionDistributive, StimesIdentity, TimesCommutative, TimesAssociative, TimesIdentityRight, TimesIdentityLeft, hnames_CWkhnames_G, hnames_DisjointToDisjoint, hdns_max_hnames_Disjoint, SubsetCtxUnionBackward, HmaxSubset, hnamesMinusEq, hnamesFullShiftEq, MinusHdnShiftEq.

Ltac crush :=
  solve
    [ autorewrite with propagate_down in *; hauto lq: on
    (* ⬇️ should really be the last case because it can be quite slow. *)
    | hauto_ctx ].



Lemma Ty_ectxs_hnames_Disjoint : forall (C : ectxs) (D D' : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), hdns_Disjoint hnamesꟲ( C) hnamesᴳ(D') -> ctx_Disjoint D D'.
Proof. Admitted.

Lemma Ty_ectxs_LinOnlyD : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), ctx_LinOnly D.
Proof.
  intros D C T U0 H. induction H.
  - apply EmptyIsLinOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyWkValidOnly.
  - assert (ctx_LinOnly (¹↑ ᴳ· D1)).
      { hauto use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, (mode_IsLinProof (Fin 1)). }
    assert (ctx_Disjoint (D1 ⨄ D2) (ᴳ-D3)).
      { apply (Ty_ectxs_hnames_Disjoint C (D1 ⨄ D2) (ᴳ-D3) (U ⧔ T') U0); tauto. }
    assert (ctx_Disjoint (¹↑ ᴳ· D1) D3).
      { sblast use: DisjointNestedLeftEquiv, DisjointMinusRightEquiv, DisjointStimesLeftEquiv. }
    rewrite (LinOnlyUnionEquiv (¹↑ ᴳ· D1) D3). split; tauto.
Qed.

Lemma Ty_ectxs_DestOnlyD : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), ctx_DestOnly D.
Proof. Admitted.

Lemma TyR_v_hdn_shift : forall (G : ctx) (v : val) (T : type) (H: hdns) (h': hdn), (G ⫦ v : T) -> (G ᴳ[ H⩲h' ] ⫦ v ᵛ[H⩲h'] : T).
Proof. Admitted.
Lemma val_A_hdn_shift : forall (H : hdns) (v1 v2: val) (h': hdn), (H ⟨ v2 ❟ v1 ⟩)ᵛ[H⩲h'] = (H ᴴ⩲ h' ⟨ v2 ᵛ[H⩲h'] ❟ v1 ᵛ[H⩲h'] ⟩).
Proof. Admitted. (* TODO: remove when val_hdn_shift is defined *)

Lemma tSubLemma : forall (D1 D2 : ctx) (m : mode) (T U : type) (u : term) (x : var) (v : val), ctx_DestOnly D1 -> ctx_DestOnly D2 -> (D2 ⨄ ᴳ{ x : m ‗ T} ⊢ u : U) -> (D1 ⊢ ᵥ₎ v : T) -> (m ᴳ· D1 ⨄ D2 ⊢ u ᵗ[ x ≔ v] : U).
Proof. Admitted.

Lemma tSubLemma2 : forall (D11 D12 D2 : ctx) (m : mode) (T1 T2 U : type) (u : term) (x1 x2 : var) (v1 v2 : val), ctx_DestOnly D11 -> ctx_DestOnly D12 -> ctx_DestOnly D2 -> (ctx_Disjoint ᴳ{ x1 : m ‗ T1} ᴳ{ x2 : m ‗ T2}) -> (D2 ⨄ ᴳ{ x1 : m ‗ T1} ⨄ ᴳ{ x2 : m ‗ T2} ⊢ u : U) -> (D11 ⊢ ᵥ₎ v1 : T1) -> (D12 ⊢ ᵥ₎ v2 : T2) -> (m ᴳ· (D11 ⨄ D12) ⨄ D2 ⊢ u ᵗ[ x1 ≔ v1 ] ᵗ[ x2 ≔ v2 ] : U).
Proof. Admitted.

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - (* Sem-eterm-AppFoc1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := T) (t := t); swap 1 3. constructor 2 with (D2 := D2) (m := m) (t' := t') (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc1 *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ t' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) t' U T); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻ t').
      all: crush.
    - (* Sem-eterm-AppFoc2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
        constructor 1 with (D := D2) (T := T ⁔ m → U) (t := t'); swap 1 3. constructor 3 with (D1 := D1) (m := m) (v := v) (T := T) (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc2 *)
      inversion Tyt; subst. rename TyRv into TyRvp, TyC into TyCc, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tytp, Tyv into Tyt, T0 into T.
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ ᵥ₎ v' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) (ᵥ₎ v') U T); tauto. }
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := (ᵥ₎ v) ≻ (ᵥ₎ v')).
      all: crush.
    - (* Sem-eterm-AppRed *)
      inversion Tyt; subst.
      assert (m = m0) as Eqmm0.
        { inversion_clear Tytp; inversion_clear TyRv; tauto. }
      rewrite <- Eqmm0 in Tyt, Tytp, TyC, DestOnlyD, ValidOnlyD. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tytp; subst. clear H1. rename TyRv into TyRv'.
      inversion TyRv'; subst. rename H1 into DestOnlyD2.
      assert (m ᴳ· D1 ⨄ D2 ⊢ u ᵗ[ x ≔ v] : U) as Tyusub.
      { apply (tSubLemma D1 D2 m T U u x v). all: crush. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := u ᵗ[ x ≔ v]).
      all: crush.
    - (* Sem-eterm-PatUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (D1 ⨄ D2) C T2 U0); tauto. }
        constructor 1 with (D := D1) (T := 𝟏) (t := t); swap 1 3. constructor 4 with (D2 := D2) (U := T2) (u := u). all: crush.
    - (* Sem-eterm-PatUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename U into T2.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (D1 ⨄ D2) C T2 U0); tauto. }
      assert (D1 ⨄ D2 ⊢ ᵥ₎ v ᵗ; u : T2) as TyPat.
        { apply (Ty_term_PatU D1 D2 (ᵥ₎ v) u T2); tauto. }
      constructor 1 with (D := (D1 ⨄ D2)) (T := T2) (t := ᵥ₎ v ᵗ; u). all: crush.
    - (* Sem-eterm-PatURed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into T2.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst.
      constructor 1 with (D := D2) (T := T2) (t := u). all: crush.
    - (* Sem-eterm-PatSFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨁ T2)) (t := t) ; swap 1 3. constructor 5 with (D1 := D1) (D2 := D2) (m := m) (u1 := u1) (x1 := x1) (u2 := u2) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatSUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2} : U) as TyPat.
        { apply (Ty_term_PatS m D1 D2 (ᵥ₎ v) x1 u1 x2 u2 U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). all: crush.
    - (* Sem-eterm-PatLRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, TyRv into TyRInlv1.
      inversion TyRInlv1; subst.
      assert (D1 ⊢ ᵥ₎ v1 : T1) as Tyt'.
        { apply Ty_term_Val; tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ u1 ᵗ[ x1 ≔ v1] : U) as Tyusub.
        { apply (tSubLemma D1 D2 m T1 U u1 x1 v1); crush. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := u1 ᵗ[ x1 ≔ v1]). all: crush.
    - (* Sem-eterm-PatRRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, TyRv into TyRInlv2.
      inversion TyRInlv2; subst.
      assert (D1 ⊢ ᵥ₎ v2 : T2) as Tyt'.
        { apply Ty_term_Val; tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ u2 ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (tSubLemma D1 D2 m T2 U u2 x2 v2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := u2 ᵗ[ x2 ≔ v2]). all: crush.
    - (* Sem-eterm-PatPFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨂ T2)) (t := t) ; swap 1 3. constructor 6 with (D1 := D1) (D2 := D2) (u := u) (x1 := x1) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatPUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u : U) as TyPat.
        { apply (Ty_term_PatP m D1 D2 (ᵥ₎ v) x1 x2 u U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u). all: crush.
    - (* Sem-eterm-PatPRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst. rename G1 into D11, G2 into D12.
      assert (D11 ⊢ ᵥ₎ v1 : T1) as Tyt1.
        { apply Ty_term_Val; crush. }
      assert (D12 ⊢ ᵥ₎ v2 : T2) as Tyt2.
        { apply Ty_term_Val; crush. }
      assert (m ᴳ· (D11 ⨄ D12) ⨄ D2 ⊢ u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (tSubLemma2 D11 D12 D2 m T1 T2 U u x1 x2 v1 v2); crush. }
      constructor 1 with (D := (m ᴳ· (D11 ⨄ D12) ⨄ D2)) (T := U) (t := u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2]). all: crush.
    - (* Sem-eterm-PatEFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (! n ⁔ T)) (t := t) ; swap 1 3. constructor 7 with (D1 := D1) (D2 := D2) (u := u) (x := x) (U := U). all: crush.
    - (* Sem-eterm-PatEUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻caseᵉ m ᴇ n ⁔ x ⟼ u : U) as TyPat.
        { apply (Ty_term_PatE m D1 D2 (ᵥ₎ v) n x u U T); crush. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻caseᵉ m ᴇ n ⁔ x ⟼ u). all: crush.
    - (* Sem-eterm-PatERed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst.
      assert (G ⊢ ᵥ₎ v' : T) as Tyt'.
        { apply Ty_term_Val; crush. }
      assert ((m · n) ᴳ· G ⨄ D2 ⊢ u ᵗ[ x ≔ v'] : U) as Tyusub.
        { apply (tSubLemma G D2 (m · n) T U u x v'). all: try crush. }
      constructor 1 with (D := (m ᴳ· (n ᴳ· G) ⨄ D2)) (T := U) (t := u ᵗ[ x ≔ v']). all: crush.
    - (* Sem-eterm-MapFoc *)
      inversion Tyt; subst. rename T0 into T.
      rename Tyt into TyMap, Tyt0 into Tyt, P1 into D1, P2 into D2.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (D1 ⨄ D2) C (U ⧔ T') U0); tauto. }
      constructor 1 with (D := D1) (T := U ⧔ T) (t := t); swap 1 3. constructor 8 with (D1 := D1) (D2 := D2) (t' := t') (x := x) (T := T) (T' := T') (U := U). all: crush.
    - (* Sem-eterm-MapUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinOnlyD (D1 ⨄ D2) C (U ⧔ T') U0); tauto. }
      assert (D1 ⨄ D2 ⊢ ᵥ₎ v ≻map x ⟼ t' : U ⧔ T') as TyMap.
        { apply (Ty_term_Map D1 D2 (ᵥ₎ v) x t' U T' T); crush. }
      constructor 1 with (D := (D1 ⨄ D2)) (T := U ⧔ T') (t := ᵥ₎ v ≻map x ⟼ t'). all: crush.
    - (* Sem-eterm-MapRedAOpenFoc *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyMap, Tyt0 into Tyt, T0 into T.
      inversion Tyt; subst. rename H2 into DestOnlyD1.
      inversion TyRv; subst. rename D0 into D11, D3 into D12, D4 into D13, DestOnlyD0 into DestOnlyD11, DestOnlyD2 into DestOnlyD12, DestOnlyD3 into DestOnlyD13, LinOnlyD3 into LinOnlyD13, ValidOnlyD3 into ValidOnlyD13, DisjointD1D2 into DisjointD11D12, DisjointD1D3 into DisjointD11D13, DisjointD2D3 into DisjointD12D13.
      assert ((¹↑ ᴳ· D11 ⨄ D13) ᴳ[hnamesᴳ( ᴳ- D13) ⩲ ʰmax(hnamesꟲ(C))] ⊢ ᵥ₎ v1 ᵛ[hnamesᴳ( ᴳ- D13) ⩲ ʰmax(hnamesꟲ(C))] : T) as Tyt1.
        { apply Ty_term_Val. apply TyR_v_hdn_shift. all: crush. }
      constructor 1 with (D := ¹↑ ᴳ· (D2 ⨄ D11 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))]) ⨄ D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))]) (T := T') (t := t' ᵗ[ x ≔ v1 ᵛ[hnamesᴳ( ᴳ- D13) ⩲ ʰmax(hnamesꟲ(C))] ]); swap 3 4;
        assert (D11 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))] = D11) as D11Eq by ( apply DisjointHdnShiftEq; crush );
        assert (D12 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))] = D12) as D12Eq by ( apply DisjointHdnShiftEq; crush );
        rewrite D11Eq.
        { assert (ctx_ValidOnly (¹↑ ᴳ· (D2 ⨄ D11))).
          { rewrite ValidOnlyStimesEquiv. split.
            - rewrite (UnionCommutative (D11 ⨄ D12) D2) in ValidOnlyD.
              rewrite UnionAssociative in ValidOnlyD.
              apply ValidOnlyUnionBackward in ValidOnlyD.
              tauto.
            - exact (mode_IsValidProof (Lin, Fin 1)).
          }
          assert (ctx_ValidOnly (D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
          { apply ValidOnlyHdnShiftEquiv; tauto. }
          assert (ctx_Disjoint (¹↑ ᴳ· (D2 ⨄ D11)) (D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
          { apply DisjointStimesLeftEquiv.
            assert (ctx_Disjoint (D2 ⨄ D11) (D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])). {
          {  apply DisjointNestedLeftEquiv. assert (HdnsM.Subset hnamesᴳ(D11 ⨄ D12 ⨄ D2) hnamesꟲ(C)).
              { apply hnames_CWkhnames_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HdnsM.Subset hnamesᴳ(D2) hnamesꟲ(C)).
              { apply SubsetCtxUnionBackward with (G := D11 ⨄ D12) (G' := D2) (H := hnamesꟲ(C)). tauto. }
              assert (ʰmax(hnamesᴳ(D2)) <= ʰmax(hnamesꟲ(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2) (hnamesᴳ(D13) ᴴ⩲ ʰmax( hnamesꟲ( C)))).
              { apply hdns_max_hnames_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
            { assert (HdnsM.Subset hnamesᴳ(D11) hnamesꟲ(C)).
              { apply SubsetCtxUnionBackward in H1. destruct H1. apply SubsetCtxUnionBackward in H1. tauto. }
              assert (ʰmax(hnamesᴳ(D11)) <= ʰmax(hnamesꟲ(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11) (hnamesᴳ(D13) ᴴ⩲ ʰmax( hnamesꟲ( C)))).
              { apply hdns_max_hnames_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
          } } tauto. }
          apply ValidOnlyUnionForward; crush.
        }
        { rewrite (UnionCommutative D2 D11). apply DestOnlyUnionEquiv. split.
          { crush. }
          { crush. }
        }
        { assert (¹↑ ᴳ· (D2 ⨄ D11) ⨄ D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))] = (¹ν ᴳ· (¹↑ ᴳ· D11 ⨄ D13) ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))]) ⨄ ¹↑ ᴳ· D2) as ctxEq.
          { rewrite <- StimesIdentity.
            rewrite UnionHdnShiftEq.
            rewrite StimesHdnShiftEq.
            rewrite D11Eq.
            rewrite UnionCommutative with (G2 := ¹↑ ᴳ· D2).
            rewrite UnionAssociative.
            rewrite StimesUnionDistributive. tauto. }
          rewrite ctxEq.
          apply tSubLemma with (T := T) (D2 := ¹↑ ᴳ· D2). all: crush. }
      rewrite <- hnamesFullShiftEq.
      rewrite MinusHdnShiftEq.
      assert (ctx_LinOnly (D11 ⨄ D12 ⨄ D2)) as LinOnlyD. { apply (Ty_ectxs_LinOnlyD (D11 ⨄ D12 ⨄ D2) C (U ⧔ T') U0). tauto. }
      constructor 19 with (D1 := D2 ⨄ D11) (D3 := D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))]) (C := C) (v2 := v2 ᵛ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))]) (T' := T') (U0 := U0) (U := U) (D2 := 
      D12).
        { apply LinOnlyUnionEquiv. rewrite <- UnionAssociative. rewrite UnionCommutative. tauto. }
        {
          {  apply DisjointNestedLeftEquiv. assert (HdnsM.Subset hnamesᴳ(D11 ⨄ D12 ⨄ D2) hnamesꟲ(C)).
              { apply hnames_CWkhnames_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HdnsM.Subset hnamesᴳ(D2) hnamesꟲ(C)).
              { apply SubsetCtxUnionBackward with (G := D11 ⨄ D12) (G' := D2) (H := hnamesꟲ(C)). tauto. }
              assert (ʰmax(hnamesᴳ(D2)) <= ʰmax(hnamesꟲ(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2) (hnamesᴳ(D13) ᴴ⩲ ʰmax( hnamesꟲ( C)))).
              { apply hdns_max_hnames_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
            { assert (HdnsM.Subset hnamesᴳ(D11) hnamesꟲ(C)).
              { apply SubsetCtxUnionBackward in H. destruct H. apply SubsetCtxUnionBackward in H. tauto. }
              assert (ʰmax(hnamesᴳ(D11)) <= ʰmax(hnamesꟲ(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11) (hnamesᴳ(D13) ᴴ⩲ ʰmax( hnamesꟲ( C)))).
              { apply hdns_max_hnames_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
          } } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. }
          { rewrite <- D12Eq. rewrite <- MinusHdnShiftEq. rewrite <- UnionHdnShiftEq. apply TyR_v_hdn_shift. tauto.  }
          { rewrite <- MinusHdnShiftEq. rewrite hnamesFullShiftEq. apply hdns_max_hnames_Disjoint with (h' := ʰmax( hnamesꟲ( C))). reflexivity. }
    - give_up.
Admitted.



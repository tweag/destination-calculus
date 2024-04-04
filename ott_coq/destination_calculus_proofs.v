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

Lemma ValidOnlyUnionBackward : forall (G1 G2 : ctx), ctx_ValidOnly (G1 ⨄ G2) -> ctx_ValidOnly G1 /\ ctx_ValidOnly G2.
Proof.
  assert (forall m1 m2, mode_IsValid (mode_plus m1 m2) -> mode_IsValid m1 /\ mode_IsValid m2) as h_mode_plus.
  { intros [[p1 a1]|] [[p2 a2]|]. all: cbn.
    all: sfirstorder. }
  unfold ctx_ValidOnly, ctx_union in *. intros *.
  eapply (merge_with_propagate_backward).
  intros [xx|xh] [] []. all: cbn.
  all: let rec t := solve
                      [ inversion 1
                      | eauto
                      | match goal with
                        |  |- context [if ?x then _ else _] => destruct x
                        end; t
                      ]
       in t.
Qed.

Lemma ValidOnlyUnionBackward' : forall (G1 G2 : ctx), Basics.impl (ctx_ValidOnly (G1 ⨄ G2)) (ctx_ValidOnly G1 /\ ctx_ValidOnly G2).
Proof.
  exact ValidOnlyUnionBackward.
Qed.
Hint Rewrite ValidOnlyUnionBackward' : propagate_down.

Lemma ValidOnlyUnionForward : forall (G1 G2 : ctx), ctx_ValidOnly G1 -> ctx_ValidOnly G2 -> ctx_Disjoint G1 G2 -> ctx_ValidOnly (G1 ⨄ G2).
Proof.
  (* Note: merge_with_propagate_forward doesn't apply to this. Which is why the
     hypothesis `ctx_Disjoint G1 G2` is needed. *)
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

Lemma mode_plus_not_lin : forall b1 b2, ~mode_IsLin (mode_plus b1 b2).
Proof.
  intros [[q1 [a1|]]|].
  2:{ cbn.  sauto q: on. }
  2:{ cbn. sauto lq: on. }
  intros [[q2 [a2|]]|]. all: cbn.
  2:{ cbn. sauto lq: on. }
  2:{ cbn. sauto lq: on. }
  cbn. unfold mul_plus.
  inversion 1.
Qed.

Lemma mode_plus_not_lin_nu : forall b1 b2, ~mode_IsLinNu (mode_plus b1 b2).
Proof.
  intros b1 b2 h.
  sauto lq: on use: mode_plus_not_lin.
Qed.

Lemma LinNuOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinNuOnly (G1 ⨄ G2) <-> ctx_LinNuOnly G1 /\ ctx_LinNuOnly G2 /\ ctx_Disjoint G1 G2.
Proof.
  intros *. unfold ctx_LinNuOnly.
  apply merge_with_propagate_both_disjoint.
  intros [xx|xh].
  - intros [[[p1 a1]|] ?] [[[p2 a2]|] ?]. all: cbn. all:unfold mul_plus.
    all: let rec t := solve
                        [ discriminate
                        | match goal with
                          |  |- context [if ?x then _ else _] => destruct x
                          end; t
                        ]
         in t.
  - intros [[[? ?]|] ? ?|? [[? ?]|]] [[[? ?]|] ? ?|? [[? ?]|]]. all: cbn. all:unfold mul_plus.
    all: let rec t := solve
                        [ discriminate
                        | match goal with
                          |  |- context [if ?x then _ else _] => destruct x
                          end; t
                        ]
         in t.
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

Lemma FinAgeOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_FinAgeOnly (G1 ⨄ G2) <-> ctx_FinAgeOnly G1 /\ ctx_FinAgeOnly G2 /\ ctx_Disjoint G1 G2.
Proof. Admitted.
Hint Rewrite FinAgeOnlyUnionEquiv : propagate_down.

Lemma LinOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_LinOnly (m ᴳ· G) <-> ctx_LinOnly G /\ mode_IsLin m.
Proof. Admitted.
Hint Rewrite LinOnlyStimesEquiv : propagate_down.

Lemma FinAgeOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_FinAgeOnly (m ᴳ· G) <-> ctx_FinAgeOnly G /\ mode_IsFinAge m.
Proof. Admitted.
Hint Rewrite FinAgeOnlyStimesEquiv : propagate_down.

Lemma LinOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_LinOnly G <-> ctx_LinOnly (G ᴳ[ H⩲h' ]).
Proof. Admitted.
Hint Rewrite <- LinOnlyHdnShiftEquiv : propagate_down.

Lemma FinAgeOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_FinAgeOnly G <-> ctx_FinAgeOnly (G ᴳ[ H⩲h' ]).
Proof. Admitted.
Hint Rewrite <- FinAgeOnlyHdnShiftEquiv : propagate_down.

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
Proof.
  (* This proof, and the similar ones below are more complicated than
    they ought to because we can't rewrite under foralls. I [aspiwack]
    am however unwilling to spend the time and find a better way,
    copy-paste will do. *)
  intros *. unfold ctx_Disjoint, ctx_stimes.
  split.
  - intros h x.
    specialize (h x).
    rewrite <- map_In in h.
    trivial.
  - intros h x.
    rewrite <- map_In.
    eauto.
Qed.
Hint Rewrite DisjointStimesLeftEquiv : propagate_down.

Lemma DisjointStimesRightEquiv : forall (m : mode) (D D' : ctx), ctx_Disjoint D (m ᴳ· D') <-> ctx_Disjoint D D'.
Proof.
  intros *. unfold ctx_Disjoint, ctx_stimes.
  split.
  - intros h x.
    specialize (h x).
    rewrite <- map_In in h.
    trivial.
  - intros h x.
    rewrite <- map_In.
    eauto.
Qed.
Hint Rewrite DisjointStimesRightEquiv : propagate_down.

Lemma DisjointMinusLeftEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint (ᴳ-D) D'.
Proof.
  intros *. unfold ctx_Disjoint, ctx_minus.
  split.
  - intros h x.
    rewrite <- map_In.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite <- map_In in h.
    trivial.
Qed.
Hint Rewrite <- DisjointMinusLeftEquiv : propagate_down.

Lemma DisjointMinusRightEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint D (ᴳ-D').
Proof.
  intros *. unfold ctx_Disjoint, ctx_minus.
  split.
  - intros h x.
    rewrite <- map_In.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite <- map_In in h.
    trivial.
Qed.
Hint Rewrite <- DisjointMinusRightEquiv : propagate_down.

Lemma DisjointNestedLeftEquiv : forall (D D' D'' : ctx), ctx_Disjoint (D ⨄ D') D'' <-> ctx_Disjoint D D'' /\ ctx_Disjoint D' D''.
Proof.
  intros *. unfold ctx_Disjoint, ctx_union.
  split.
  - intros h.
    split.
    all: intros x.
    all: specialize (h x).
    all: rewrite merge_with_spec_5 in h.
    all: sfirstorder.
  - intros h x.
    rewrite merge_with_spec_5.
    sfirstorder.
Qed.
Hint Rewrite DisjointNestedLeftEquiv : propagate_down.

Lemma DisjointNestedRightEquiv : forall (D D' D'' : ctx), ctx_Disjoint D  (D' ⨄ D'') <-> ctx_Disjoint D D' /\ ctx_Disjoint D D''.
Proof.
Proof.
  intros *. unfold ctx_Disjoint, ctx_union.
  split.
  - intros h.
    split.
    all: intros x.
    all: specialize (h x).
    all: rewrite merge_with_spec_5 in h.
    all: sfirstorder.
  - intros h x.
    rewrite merge_with_spec_5.
    sfirstorder.
Qed.
Hint Rewrite DisjointNestedRightEquiv : propagate_down.

Lemma DisjointHdnShiftEq : forall (D D': ctx) (h': hdn), ctx_Disjoint D D' -> D ᴳ[ hnamesᴳ( D' ) ⩲ h' ] = D.
Proof. Admitted.

Lemma DisjointCommutative : forall (G1 G2 : ctx), ctx_Disjoint G1 G2 <-> ctx_Disjoint G2 G1.
Proof.
  intros *. unfold ctx_Disjoint.
  sfirstorder.
Qed.

Lemma EmptyIsLinOnly : ctx_LinOnly ᴳ{}.
Proof.
  scongruence unfold: ctx_LinOnly.
Qed.

Lemma EmptyIsFinAgeOnly : ctx_FinAgeOnly ᴳ{}.
Proof.
  scongruence unfold: ctx_FinAgeOnly.
Qed.

Lemma EmptyIsDestOnly : ctx_DestOnly ᴳ{}.
Proof.
  sauto q: on unfold: ctx_DestOnly.
Qed.

Lemma EmptyIsDisjointLeft : forall (G : ctx), ctx_Disjoint ᴳ{} G.
Proof.
  sauto q: on unfold: ctx_Disjoint.
Qed.

Lemma EmptyIsDisjointRight : forall (G : ctx), ctx_Disjoint G ᴳ{}.
Proof.
  sauto q: on unfold: ctx_Disjoint.
Qed.

Lemma StimesEmptyEq : forall (m : mode), m ᴳ· ᴳ{} = ᴳ{}.
Proof.
  intros *. unfold ctx_empty, empty, ctx_stimes, map. cbn.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma MinusEmptyEq : ᴳ- ᴳ{} = ᴳ{}.
Proof.
  apply Finitely.ext_eq.
  all: sfirstorder.
Qed.

Lemma UnionIdentityRight : forall (G : ctx), G = G ⨄ ᴳ{}.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros x. unfold ctx_union.
    destruct (In_dec x G) as [[y h_inG]|h_ninG]. all: rewrite ?In_None2 in *.
    + erewrite merge_with_spec_2.
      2:{ eauto. }
      eauto.
    + erewrite merge_with_spec_4.
      all: eauto.
  - unfold ctx_union. destruct G. cbn.
    rewrite app_nil_r. reflexivity.
Qed.

Lemma UnionIdentityLeft : forall (G : ctx), G = ᴳ{} ⨄ G.
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

Lemma DisjointTohdns_Disjoint : forall (D D' : ctx), ctx_Disjoint D D' -> hdns_Disjoint hnamesᴳ(D) hnamesᴳ(D').
Proof. Admitted.

Lemma hdns_max_hdns_Disjoint : forall (H H' : hdns) (h' : hdn), ʰmax(H) <= h' -> hdns_Disjoint H (H' ᴴ⩲ h').
Proof. Admitted.

Lemma SubsetCtxUnionBackward : forall (G G': ctx) (H: hdns), HdnsM.Subset hnamesᴳ(G ⨄ G') H -> HdnsM.Subset hnamesᴳ(G) H /\ HdnsM.Subset hnamesᴳ(G') H.
Proof. Admitted.

Lemma HmaxSubset : forall (H H' : hdns), HdnsM.Subset H H' -> ʰmax(H) <= ʰmax(H').
Proof. Admitted.

Lemma hnamesMinusEq : forall (D : ctx), hnamesᴳ( ᴳ- D) = hnamesᴳ( D).
Proof. Admitted.
Lemma hnamesFullShiftEq : forall (G : ctx) (h' : hdn), hnamesᴳ(G ᴳ[ hnamesᴳ( G ) ⩲ h' ]) = hnamesᴳ(G) ᴴ⩲ h'.
Proof. Admitted.
Lemma hnamesEmpty : hnamesᴳ(ᴳ{}) = HdnsM.empty.
Proof. Admitted.
Lemma EmptyIshdns_DisjointRight : forall (H : hdns), hdns_Disjoint H HdnsM.empty.
Proof. Admitted.
Lemma EmptyIshdns_DisjointLeft : forall (H : hdns), hdns_Disjoint HdnsM.empty H.
Proof. Admitted.
Lemma MinusHdnShiftEq : forall (G : ctx) (H : hdns) (h' : hdn), (ᴳ- G) ᴳ[ H ⩲ h' ] = ᴳ- (G ᴳ[ H ⩲ h' ]).
Proof. Admitted.

Lemma CompatibleDestSingleton : forall (h : hdn) (m : mode) (T : type) (n : mode), ctx_CompatibleDH (ᴳ{+ h : m ⌊ T ⌋ n}) h (₊ m ⌊ T ⌋ n).
Proof. Admitted.

Lemma IncompatibleVarDestOnly : forall (D : ctx) (x : var) (m : mode) (T : type), ctx_DestOnly D -> ~ctx_CompatibleVar D x (ₓ m ‗ T).
Proof. Admitted.

Lemma MinusSingletonEq : forall (h : hdn) (T : type) (n : mode), ᴳ- ᴳ{+ h : ¹ν ⌊ T ⌋ n} = ᴳ{- h : T ‗ n }.
Proof. Admitted.

Ltac hauto_ctx :=
  hauto
    depth: 3
    use: ValidOnlyUnionBackward, ValidOnlyUnionForward, ValidOnlyStimesEquiv, ValidOnlyMinusEquiv, ValidOnlyHdnShiftEquiv, DestOnlyUnionEquiv, DestOnlyStimesEquiv, DestOnlyHdnShiftEquiv, LinNuOnlyUnionEquiv, LinNuOnlyStimesEquiv, LinNuOnlyHdnShiftEquiv, LinOnlyUnionEquiv, LinOnlyStimesEquiv, LinOnlyHdnShiftEquiv, LinNuOnlyWkLinOnly, LinOnlyWkValidOnly, IsLinNuWkIsLin, IsLinWkIsValid, DisjointStimesLeftEquiv, DisjointStimesRightEquiv, DisjointMinusLeftEquiv, DisjointMinusRightEquiv, DisjointNestedLeftEquiv, DisjointNestedRightEquiv, DisjointHdnShiftEq, DisjointCommutative, EmptyIsLinOnly, EmptyIsDestOnly, EmptyIsDisjointLeft, EmptyIsDisjointRight, StimesEmptyEq, MinusEmptyEq, UnionIdentityRight, UnionIdentityLeft, DisjointDestOnlyVar, UnionCommutative, UnionAssociative, UnionHdnShiftEq, StimesHdnShiftEq, StimesIsAction, StimesUnionDistributive, StimesIdentity, TimesCommutative, TimesAssociative, TimesIdentityRight, TimesIdentityLeft, hnames_CWkhnames_G, hnames_DisjointToDisjoint, DisjointTohdns_Disjoint, hdns_max_hdns_Disjoint, UnionIdentityRight, UnionIdentityLeft, SubsetCtxUnionBackward, HmaxSubset, hnamesMinusEq, hnamesFullShiftEq, hnamesEmpty, EmptyIshdns_DisjointRight, EmptyIshdns_DisjointLeft, MinusHdnShiftEq, CompatibleDestSingleton, IncompatibleVarDestOnly, MinusSingletonEq, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, FinAgeOnlyHdnShiftEquiv, EmptyIsFinAgeOnly.

Ltac crush :=
  solve
    [ autorewrite with propagate_down in *; hauto lq: on
    (* ⬇️ should really be the last case because it can be quite slow. *)
    | hauto_ctx ].

Lemma empty_support_Empty : forall (G : ctx), support G = nil -> G = ᴳ{}.
Proof. Admitted.

Lemma Ty_ectxs_hnames_Disjoint : forall (C : ectxs) (D D' : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), hdns_Disjoint hnamesꟲ( C) hnamesᴳ(D') -> ctx_Disjoint D D'.
Proof. Admitted.

Lemma Ty_ectxs_LinFinOnlyD : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), ctx_LinOnly D /\ ctx_FinAgeOnly D.
Proof.
  intros D C T U0 H. induction H.
  - split. apply EmptyIsLinOnly. apply EmptyIsFinAgeOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, LinOnlyWkValidOnly.
  - assert (ctx_LinOnly (¹↑ ᴳ· D1)).
      { hauto use: LinOnlyUnionEquiv, LinOnlyStimesEquiv, (mode_IsLinProof (Fin 1)). }
    assert (ctx_FinAgeOnly (¹↑ ᴳ· D1)).
      { hauto use: FinAgeOnlyUnionEquiv, FinAgeOnlyStimesEquiv, (mode_IsFinAgeProof Lin 1). }
    assert (ctx_Disjoint (D1 ⨄ D2) (ᴳ-D3)).
      { apply (Ty_ectxs_hnames_Disjoint C (D1 ⨄ D2) (ᴳ-D3) (U ⧔ T') U0); tauto. }
    assert (ctx_Disjoint (¹↑ ᴳ· D1) D3).
      { sblast use: DisjointNestedLeftEquiv, DisjointMinusRightEquiv, DisjointStimesLeftEquiv. }
    rewrite LinOnlyUnionEquiv, FinAgeOnlyUnionEquiv. repeat split. all: tauto.
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

Lemma ectxsSubLemma : forall (D1 D2 D3 : ctx) (h : hdn) (C : ectxs) (n : mode) (T U U0 : type) (v : val),
  ctx_Disjoint D1 D2 ->
  ctx_Disjoint D1 D3 ->
  hdns_Disjoint hnamesꟲ(C) hnamesᴳ(ᴳ- D3) ->
  ctx_DestOnly D1 ->
  ctx_DestOnly D2 ->
  ctx_DestOnly D3 ->
  ctx_LinOnly D3 ->
  ctx_FinAgeOnly D3 ->
  ctx_ValidOnly D3 ->
  ctx_Disjoint D1 ᴳ{+ h : ¹ν ⌊ U ⌋ n } ->
  ctx_Disjoint D2 ᴳ{+ h : ¹ν ⌊ U ⌋ n } ->
  ctx_Disjoint D3 ᴳ{+ h : ¹ν ⌊ U ⌋ n } ->
 D1 ⨄ n ᴳ· D2 ⨄ ᴳ{+ h : ¹ν ⌊ U ⌋ n } ⊣ C : T ↣ U0 ->
 D2 ⨄ ᴳ- D3 ⫦ v : U ->
 D1 ⨄ n ᴳ· D3 ⊣ C ꟲ[ h ≔ hnamesᴳ( n ᴳ· (ᴳ- D3)) ‗ v ] : T ↣ U0.
Proof. Admitted.

Lemma CompatibleLinFinOnlyIsExact : forall (D : ctx) (h : hdn) (T : type) (n : mode), ctx_LinOnly D -> ctx_FinAgeOnly D -> ctx_CompatibleDH D h (₊ ¹ν ⌊ T ⌋ n) -> D = ᴳ{+ h : ¹ν ⌊ T ⌋ n}.
Proof. Admitted.

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - (* Sem-eterm-AppFoc1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := T) (t := t); swap 1 3. constructor 2 with (D2 := D2) (m := m) (t' := t') (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc1 *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ t' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) t' U T); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ⨄ D2)) (T := U) (t := ᵥ₎ v ≻ t').
      all: crush.
    - (* Sem-eterm-AppFoc2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
        constructor 1 with (D := D2) (T := T ⁔ m → U) (t := t'); swap 1 3. constructor 3 with (D1 := D1) (m := m) (v := v) (T := T) (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc2 *)
      inversion Tyt; subst. rename TyRv into TyRvp, TyC into TyCc, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tytp, Tyv into Tyt, T0 into T.
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ ᵥ₎ v' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) (ᵥ₎ v') U T); tauto. }
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
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
        { apply (Ty_ectxs_LinFinOnlyD (D1 ⨄ D2) C T2 U0); tauto. }
        constructor 1 with (D := D1) (T := ①) (t := t); swap 1 3. constructor 4 with (D2 := D2) (U := T2) (u := u). all: crush.
    - (* Sem-eterm-PatUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename U into T2.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (D1 ⨄ D2) C T2 U0); tauto. }
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
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨁ T2)) (t := t) ; swap 1 3. constructor 5 with (D1 := D1) (D2 := D2) (m := m) (u1 := u1) (x1 := x1) (u2 := u2) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatSUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
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
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨂ T2)) (t := t) ; swap 1 3. constructor 6 with (D1 := D1) (D2 := D2) (u := u) (x1 := x1) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatPUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
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
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (! n ⁔ T)) (t := t) ; swap 1 3. constructor 7 with (D1 := D1) (D2 := D2) (u := u) (x := x) (U := U). all: crush.
    - (* Sem-eterm-PatEUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (m ᴳ· D1 ⨄ D2) C U U0); tauto. }
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
        { apply (Ty_ectxs_LinFinOnlyD (D1 ⨄ D2) C (U ⧔ T') U0); tauto. }
      constructor 1 with (D := D1) (T := U ⧔ T) (t := t); swap 1 3. constructor 8 with (D1 := D1) (D2 := D2) (t' := t') (x := x) (T := T) (T' := T') (U := U). all: crush.
    - (* Sem-eterm-MapUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (D1 ⨄ D2) C (U ⧔ T') U0); tauto. }
      assert (D1 ⨄ D2 ⊢ ᵥ₎ v ≻map x ⟼ t' : U ⧔ T') as TyMap.
        { apply (Ty_term_Map D1 D2 (ᵥ₎ v) x t' U T' T); crush. }
      constructor 1 with (D := (D1 ⨄ D2)) (T := U ⧔ T') (t := ᵥ₎ v ≻map x ⟼ t'). all: crush.
    - (* Sem-eterm-MapRedAOpenFoc *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyMap, Tyt0 into Tyt, T0 into T.
      inversion Tyt; subst. rename H2 into DestOnlyD1.
      inversion TyRv; subst. rename D0 into D11, D3 into D12, D4 into D13, DestOnlyD0 into DestOnlyD11, DestOnlyD2 into DestOnlyD12, DestOnlyD3 into DestOnlyD13, LinOnlyD3 into LinOnlyD13, ValidOnlyD3 into ValidOnlyD13, DisjointD1D2 into DisjointD11D12, DisjointD1D3 into DisjointD11D13, DisjointD2D3 into DisjointD12D13, FinAgeOnlyD3 into FinAgeOnlyD13.
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
              { apply hdns_max_hdns_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
            { assert (HdnsM.Subset hnamesᴳ(D11) hnamesꟲ(C)).
              { apply SubsetCtxUnionBackward in H1. destruct H1. apply SubsetCtxUnionBackward in H1. tauto. }
              assert (ʰmax(hnamesᴳ(D11)) <= ʰmax(hnamesꟲ(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11) (hnamesᴳ(D13) ᴴ⩲ ʰmax( hnamesꟲ( C)))).
              { apply hdns_max_hdns_Disjoint. tauto. }
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
      assert (ctx_LinOnly (D11 ⨄ D12 ⨄ D2)) as LinOnlyD. { apply (Ty_ectxs_LinFinOnlyD (D11 ⨄ D12 ⨄ D2) C (U ⧔ T') U0). tauto. }
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
              { apply hdns_max_hdns_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
            { assert (HdnsM.Subset hnamesᴳ(D11) hnamesꟲ(C)).
              { apply SubsetCtxUnionBackward in H. destruct H. apply SubsetCtxUnionBackward in H. tauto. }
              assert (ʰmax(hnamesᴳ(D11)) <= ʰmax(hnamesꟲ(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11) (hnamesᴳ(D13) ᴴ⩲ ʰmax( hnamesꟲ( C)))).
              { apply hdns_max_hdns_Disjoint. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ ʰmax( hnamesꟲ( C))])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
          } } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite UnionCommutative in TyC. rewrite UnionAssociative in TyC. tauto. }
          { rewrite <- D12Eq. rewrite <- MinusHdnShiftEq. rewrite <- UnionHdnShiftEq. apply TyR_v_hdn_shift. tauto.  }
          { rewrite <- MinusHdnShiftEq. rewrite hnamesFullShiftEq. apply hdns_max_hdns_Disjoint with (h' := ʰmax( hnamesꟲ( C))). reflexivity. }
    - (* Sem-eterm-AOpenUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, TyRv into TyRv1. clear H2.
      inversion TyCc; subst. rename H6 into hdnsDisjoint.
      assert (D1 ⨄ D2 ⊢ ᵥ₎ hnamesᴳ( ᴳ- D3) ⟨ v2 ❟ v1 ⟩ : U ⧔ T) as TyA.
        { apply Ty_term_Val. apply TyR_val_A; swap 8 1. all: apply Ty_ectxs_hnames_Disjoint with (D := D1 ⨄ D2) (D' := ᴳ- D3) (C := C) (T := U ⧔ T) (U0 := U0) in hdnsDisjoint. all: crush.
         }
      assert (ctx_LinOnly (D1 ⨄ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD (D1 ⨄ D2) C (U ⧔ T) U0). tauto. }
      constructor 1 with (D := (D1 ⨄ D2)) (T := U ⧔ T) (t := ᵥ₎ hnamesᴳ( ᴳ- D3) ⟨ v2 ❟ v1 ⟩). all: crush.
    - (* Sem-eterm-AllocRed *)
      inversion Tyt; subst.
      assert (hnamesᴳ(ᴳ- ᴳ{+ 1 : ¹ν ⌊ U ⌋ ¹ν }) = ᴴ{ 1}) as hnamesD3Eq.
        { cbn. reflexivity. }
      assert (ᴳ{} ⊢ ᵥ₎ ᴴ{ 1} ⟨ ᵛ- 1 ❟ ᵛ+ 1 ⟩ : U ⧔ ⌊ U ⌋ ¹ν) as Tytp.
        { rewrite <- hnamesD3Eq. apply Ty_term_Val. rewrite (UnionIdentityLeft ᴳ{}). apply TyR_val_A.
          - crush.
          - crush.
          - intros n. unfold ctx_singleton. rewrite in_singleton. intros H; subst. cbv; tauto.
          - intros n tyb. unfold ctx_singleton. rewrite mapsto_singleton. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (tyb = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n tyb. unfold ctx_singleton. rewrite mapsto_singleton. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (tyb = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n tyb. unfold ctx_singleton. rewrite mapsto_singleton. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (tyb = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - crush.
          - crush.
          - crush.
          - rewrite StimesEmptyEq. rewrite <- UnionIdentityLeft. constructor. crush.
          - rewrite <- UnionIdentityLeft. rewrite MinusSingletonEq. constructor.
          - crush.
        }
      constructor 1 with (D := ᴳ{}) (T := U ⧔ ⌊ U ⌋ ¹ν) (t := ᵥ₎ ᴴ{ 1} ⟨ ᵛ- 1 ❟ ᵛ+ 1 ⟩). all: crush.
    - (* Sem-eterm-ToAFoc *)
      inversion Tyt; subst.
      rename Tyt into TyToA.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C (U ⧔ ①) U0). tauto. }
      constructor 1 with (D := D) (t := u) (T := U); swap 1 3. constructor 9. all: crush.
    - (* Sem-eterm-ToAUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C (U ⧔ ①) U0). tauto. }
      assert (D ⊢ to⧔ ᵥ₎ v2 : U ⧔ ①) as TyToA.
        { apply (Ty_term_ToA D (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D) (T := U ⧔ ①) (t := to⧔ ᵥ₎ v2). all: crush.
    - (* Sem-eterm-ToARed *)
      inversion Tyt; subst.
      rename Tyt into TyToA, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      inversion Tyu; subst.
      assert (ᴳ{} ⨄ D2 ⊢ ᵥ₎ hdns_from_list nil ⟨ v2 ❟ ᵛ() ⟩ : U ⧔ ①).
        { apply Ty_term_Val. assert (hnamesᴳ( ᴳ- ᴳ{}) = hdns_from_list nil) by crush. rewrite <- H. apply TyR_val_A; swap 1 11; swap 2 10.
          rewrite MinusEmptyEq. rewrite <- UnionIdentityRight; tauto.
          rewrite StimesEmptyEq. rewrite <- UnionIdentityRight. constructor.
          all:crush. }
      rewrite <- UnionIdentityLeft in H.
      constructor 1 with (D := D2) (T := U ⧔ ①) (t := ᵥ₎ hdns_from_list nil ⟨ v2 ❟ ᵛ() ⟩). all: crush.
    - (* Sem-eterm-FromAFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFromA, T into U.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C U U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := U ⧔ ①); swap 1 3. constructor 10. all: crush.
    - (* Sem-eterm-FromAUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename U1 into U, v into v2, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      assert (ctx_LinOnly D2) as LinOnlyD2.
        { apply (Ty_ectxs_LinFinOnlyD D2 C U U0). tauto. }
      assert (D2 ⊢ from⧔ ᵥ₎ v2 : U) as TyFromA.
        { apply (Ty_term_FromA D2 (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D2) (T := U) (t := from⧔ ᵥ₎ v2). all: crush.
    - (* Sem-eterm-FromARed *)
      inversion Tyt; subst.
      rename Tyt0 into Tytp, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2, T into U.
      inversion Tytp; subst.
      inversion TyRv; subst. rename D0 into D2.
      inversion TyRv1. apply eq_sym in H3. apply (app_eq_nil (support D1) (support D3)) in H3. destruct H3. apply empty_support_Empty in H, H3. subst. rewrite StimesEmptyEq in *. rewrite <- UnionIdentityLeft in *. rewrite MinusEmptyEq in *. rewrite <- UnionIdentityRight in *.
      assert (D2 ⊢ ᵥ₎ v2 : U).
        { apply Ty_term_Val; tauto. }
      constructor 1 with (D := D2) (T := U) (t := ᵥ₎ v2). all: crush.
    - (* Sem-eterm-FillUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tyt.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C ① U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ ① ⌋ n); swap 1 3. constructor 11. all: crush.
    - (* Sem-eterm-FillUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C ① U0). tauto. }
      assert (D ⊢ ᵥ₎ v⨞() : ①) as TyFillU.
        { apply (Ty_term_FillU D (ᵥ₎ v) n). tauto. }
      constructor 1 with (D := D) (T := ①) (t := ᵥ₎ v⨞()). all: crush.
    - (* Sem-eterm-FillURed *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tytp.
      assert (ctx_LinOnly D /\ ctx_FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnlyD D C ① U0). tauto. }
      inversion Tytp; subst. clear H1.
      inversion TyRv; subst.
      assert (D = ᴳ{+ h : ¹ν ⌊ ① ⌋ n}) as EqD.
        { apply CompatibleLinFinOnlyIsExact. all:tauto. }
      subst.
      assert (ᴳ{} ⊣ C ꟲ[ h ≔ hdns_from_list nil ‗ ᵛ()] : ① ↣ U0).
        { assert (ᴳ{} ⨄ n ᴳ· ᴳ{} = ᴳ{}) as e1 by crush. rewrite <- e1.
          assert (hnamesᴳ(n ᴳ· (ᴳ- ᴳ{})) = hdns_from_list nil) as e2 by crush. rewrite <- e2.
          assert (ᴳ{} ⨄ n ᴳ· ᴳ{} ⨄ ᴳ{+ h : ¹ν ⌊ ① ⌋ n} = ᴳ{+ h : ¹ν ⌊ ① ⌋ n}) as e3 by crush. rewrite <- e3 in TyC.
          apply ectxsSubLemma with (D2 := ᴳ{}) (U := ①); swap 1 14.
          rewrite <- UnionIdentityLeft. rewrite MinusEmptyEq. apply TyR_val_U.
          all: crush. }
      constructor 1 with (D := ᴳ{}) (T := ①) (t := ᵥ₎ ᵛ()); swap 1 4.
      apply Ty_term_Val. apply TyR_val_U. all: crush.
    - (* Sem-eterm-FillLFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFillL, Tyt0 into Tyt.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C (⌊ T1 ⌋ n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ T1 ⨁ T2 ⌋ n); swap 1 3. constructor 12. all: crush.
    - (* Sem-eterm-FillLUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst.
      assert (ctx_LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnlyD D C (⌊ T1 ⌋ n) U0). tauto. }
      assert (D ⊢ ᵥ₎ v ⨞Inl : ⌊ T1 ⌋ n) as TyFillL.
        { apply (Ty_term_FillL D (ᵥ₎ v) T1 n T2). tauto. }
      constructor 1 with (D := D) (T := ⌊ T1 ⌋ n) (t := ᵥ₎ v ⨞Inl). all: crush.
    - (* Sem-eterm-FillLRed *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillL, Tyt0 into Tytp.
      assert (ctx_LinOnly D /\ ctx_FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnlyD D C (⌊ T1 ⌋ n) U0). tauto. }
      inversion Tytp; subst. clear H1.
      inversion TyRv; subst; intros hpMaxCh.
      assert (D = ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n}) as EqD.
        { apply CompatibleLinFinOnlyIsExact. all:tauto. }
      rewrite EqD in *. clear EqD.
      (* ectxsSubLemma is false because we need to shift n mode of dests by n, which we cannot do with just minus and shift *)
      give_up.
      (* assert (ᴳ{} ⊣ C ꟲ[ h ≔ ᴴ{ h' + 1} ‗ Inl ᵛ- (h' + 1)] : ⌊ T1 ⌋ n ↣ U0).
        { assert (ᴳ{} ⨄ n ᴳ· ᴳ{} = ᴳ{}) as e1 by crush. rewrite <- e1.
          assert (hnamesᴳ(n ᴳ· (ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν})) = ᴴ{ h' + 1}) as e2 by admit. rewrite <- e2.
          assert (ᴳ{} ⨄ n ᴳ· ᴳ{} ⨄ ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n} = ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n}) as e3 by crush. rewrite <- e3 in TyC.
          apply ectxsSubLemma with (D2 := ᴳ{}) (D3 := ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) (U := ⌊ T1 ⨁ T2 ⌋ n); swap 1 14.
          rewrite <- UnionIdentityLeft. rewrite MinusEmptyEq. apply TyR_val_L.
          all: crush. }
      constructor 1 with (D := ᴳ{}) (T := ⌊ T1 ⌋ n) (t := ᵥ₎ ᵛ()); swap 1 4.
      apply Ty_term_Val. apply TyR_val_L. all: crush. *)
    - give_up.
Admitted.

Lemma exists_impl_to_forall : forall (A : Type) (H1 : A -> Prop) (H2 : Prop),
  Basics.impl ((exists n, H1 n) -> H2) (forall n, H1 n -> H2).
Proof.
  intros A H1 H2.
  - intros H_exist_impl_H2 n H_n. (* Assuming (exists n, H1 n) -> H2 *)
    apply H_exist_impl_H2. (* Applying the hypothesis *)
    exists n. (* Proving the existential statement *)
    apply H_n. (* Applying H1 n -> H2 *)
Qed.

Lemma DestOnlyValHole : forall (D : ctx) (h : hdn) (T : type), (D ⫦ ᵛ- h : T) -> ctx_DestOnly D -> False.
Proof.
  intros D h T TyRv DestOnlyD. inversion TyRv; subst.
  specialize (DestOnlyD (ʰ h)). unfold ctx_DestOnly, ctx_singleton, In, Fun.In in DestOnlyD. rewrite exists_impl_to_forall in DestOnlyD. specialize (DestOnlyD (₋ T ‗ ¹ν)). rewrite mapsto_singleton in DestOnlyD. specialize (DestOnlyD eq_refl). destruct (singleton (ʰ h) name_eq_dec (₋ T ‗ ¹ν) (ʰ h)) eqn:H' in DestOnlyD. rewrite mapsto_singleton in H'. assert (b = ₋ T‗ ¹ν) as Eqb. { apply inj_pair2_eq_dec. exact name_eq_dec. apply (eq_sym H'). } rewrite Eqb in DestOnlyD. all: tauto.
Qed.

Lemma term_NotVal_dec : forall (t : term), {exists v, t = ᵥ₎ v} + {term_NotVal t}.
Proof.
  intros t. destruct t.
  { left. exists v; tauto. }
  all: right; congruence.
Qed.

Theorem Progress : forall (C : ectxs) (t : term) (U0 : type), ⊢ C ʲ[t] : U0 -> ((exists v, t = ᵥ₎ v) -> C <> ꟲ⬜) -> exists (C' : ectxs) (t' : term), C ʲ[t] ⟶ C' ʲ[t'].
Proof.
  intros C t U0 Tyj CNilOrNotValt. inversion Tyj; subst. inversion Tyt; subst.
  inversion TyC; subst. all: try rename TyC into TyCc. all: try rename C0 into C. all: try rename TyC0 into TyC. all: try rename T0 into T.
  - exfalso. apply CNilOrNotValt. exists v. all: reflexivity.
  - exists C, (ᵥ₎ v ≻ t'). constructor.
  - rename v into v', v0 into v, D into D2, ValidOnlyD into ValidOnlyD2. clear DestOnlyD. exists C, (ᵥ₎ v ≻ ᵥ₎ v'). constructor.
  - exists C, (ᵥ₎ v ᵗ; u). constructor.
  - exists C, (ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). constructor.
  - exists C, (ᵥ₎ v ≻caseᵖ m ᵗ( x1, x2) ⟼ u). constructor.
  - exists C, (ᵥ₎ v ≻caseᵉ m ᴇ m' ⁔ x ⟼ u). constructor.
  - exists C, (ᵥ₎ v ≻map x ⟼ t'). constructor.
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
  - rename v into v1, TyRv into TyRv1. exists C, (ᵥ₎ hnamesᴳ( ᴳ- D3) ⟨ v2 ❟ v1 ⟩). constructor.
  - exfalso. apply (IncompatibleVarDestOnly D x ¹ν T (DestOnlyD)); tauto.
  - rename Tyt into TyApp, T into U, T0 into T, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2.
    destruct (term_NotVal_dec t). all: try destruct e; subst. all: try rename x into v.
    * destruct (term_NotVal_dec t'). all: try destruct e; subst. all: try rename x into v'.
      + inversion Tytp; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : T ⁔ m → U ‗ ¹ν}) (h := h) (T := T ⁔ m → U); tauto. }
      exists C, (u ᵗ[x ≔ v]). constructor.
      + exists (C ∘ (v ≻⬜)), t'. constructor; tauto.
    * exists (C ∘ ⬜≻ t'), t. constructor; tauto.
  - rename Tyt into TyPatU, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ① ‗ ¹ν}) (h := h) (T := ①); tauto. } exists C, u. constructor.
    * exists (C ∘ ⬜; u), t. constructor; tauto.
  - rename Tyt into TyPatS, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : T1 ⨁ T2 ‗ ¹ν}) (h := h) (T := T1 ⨁ T2); tauto. }
      { exists C, (u1 ᵗ[x1 ≔ v1]). constructor. }
      { exists C, (u2 ᵗ[x2 ≔ v2]). constructor. }
    * exists (C ∘ (⬜≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2})), t. constructor; tauto.
  - rename Tyt into TyPatP, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : T1 ⨂ T2 ‗ ¹ν}) (h := h) (T := T1 ⨂ T2); tauto. }
      { exists C, (u ᵗ[x1 ≔ v1] ᵗ[x2 ≔ v2]). constructor. }
    * exists (C ∘ ⬜≻caseᵖ m ᵗ( x1, x2)⟼ u), t. constructor; tauto.
  - rename Tyt into TyPatE, T into U, T0 into T, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ! n ⁔ T ‗ ¹ν}) (h := h) (T := ! n ⁔ T); tauto. }
      { exists C, (u ᵗ[x ≔ v']). constructor. }
    * exists (C ∘ ⬜≻caseᵉ m ᴇ n ⁔ x ⟼ u), t. constructor; tauto.
  - rename Tyt into TyMap, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : U ⧔ T ‗ ¹ν}) (h := h) (T := U ⧔ T); tauto. }
      rename D0 into D1, D2 into D', D3 into D2, D4 into D3.
      exists (C ∘ hnamesᴳ( ᴳ- D3) ᴴ⩲ ʰmax(hnamesꟲ(C)) ᵒᵖ⟨ v2 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ ʰmax(hnamesꟲ(C))] ❟⬜), (t' ᵗ[x ≔ v1 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ ʰmax(hnamesꟲ(C))]]). constructor; tauto.
    * exists (C ∘ ⬜≻map x ⟼ t'), t. constructor; tauto.
  - rename Tyt into TyToA. destruct (term_NotVal_dec u).
    * destruct e; subst. rename x into v2. exists C, (ᵥ₎ HdnsM.empty ⟨ v2 ❟ ᵛ() ⟩ ). constructor.
    * exists (C ∘ to⧔⬜), u. constructor; tauto.
  - rename Tyt into TyToA, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : T ⧔ ① ‗ ¹ν}) (h := h) (T := T ⧔ ①); tauto. }
      inversion TyRv1; subst. { assert (ctx_DestOnly (¹↑ ᴳ· D1 ⨄ D3)) by crush. exfalso. apply DestOnlyValHole with (D := (¹↑ ᴳ· D1 ⨄ D3)) (h := h) (T := ①). all:tauto. }
      assert (D3 = ᴳ{}) as EmptyD3. { apply eq_sym in H2. apply (app_eq_nil (support D1) (support D3)) in H2. destruct H2. apply empty_support_Empty in H, H2. tauto. } subst. rewrite hnamesMinusEq, hnamesEmpty.
      exists C, (ᵥ₎ v2). constructor.
    * exists (C ∘ from⧔⬜), t. constructor; tauto.
  - rename Tyt into TyAlloc. exists C, (ᵥ₎ ᴴ{ 1 } ⟨ ᵛ-1 ❟ ᵛ+1 ⟩ ). constructor.
  - rename Tyt into TyFillU, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ ① ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ① ⌋ n); tauto. }
      exists (C ꟲ[ h ≔ HdnsM.empty ‗ ᵛ()]), (ᵥ₎ ᵛ()). constructor.
    * exists (C ∘ ⬜⨞()), t. constructor; tauto.
  - rename Tyt into TyFillL, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ꟲ[ h ≔ ᴴ{ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1} ‗ Inl ᵛ- (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1)]), (ᵥ₎ ᵛ+ (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inl), t. constructor; tauto.
  - rename Tyt into TyFillR, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ꟲ[ h ≔ ᴴ{ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1} ‗ Inr ᵛ- (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1)]), (ᵥ₎ ᵛ+ (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inr), t. constructor; tauto.
  - rename Tyt into TyFillP, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T1 ⨂ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨂ T2 ⌋ n); tauto. }
    exists (C ꟲ[ h ≔ ᴴ{ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1 , ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 2} ‗ ᵛ( ᵛ- (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1), ᵛ- (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 2))]), (ᵥ₎ ᵛ( ᵛ+ (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1), ᵛ+ (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 2))). constructor; tauto.
    * exists (C ∘ ⬜⨞(,)), t. constructor; tauto.
  - rename Tyt into TyFillE, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ ! n' ⁔ T ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ! n' ⁔ T ⌋ n); tauto. }
    exists (C ꟲ[ h ≔ ᴴ{ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1} ‗ ᴇ n' ⁔ ᵛ- (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1)]), (ᵥ₎ ᵛ+ (ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞ᴇ n'), t. constructor; tauto.
  - rename Tyt into TyFillF, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T ⁔ m → U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T ⁔ m → U ⌋ n); tauto. }
    exists (C ꟲ[ h ≔ HdnsM.empty ‗ λᵛ x ⁔ m ⟼ u ]), (ᵥ₎ ᵛ()). constructor; tauto.
    * exists (C ∘ ⬜⨞(λ x ⁔ m ⟼ u)), t. constructor; tauto.
  - rename Tyt into TyFillC, Tyt0 into Tyt, t0 into t, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. destruct (term_NotVal_dec t').
      + destruct e; subst. rename x into v'. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ U ⌋ n); tauto. } rename H1 into DestOnlyD'. inversion Tytp; subst. rename TyRv0 into TyRvp. inversion TyRvp; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h0 : U ⧔ T ‗ ¹ν}) (h := h0) (T := U ⧔ T); tauto. } rename D1 into D', D0 into D1, D3 into D2, D4 into D3. 
      exists
        ( C ꟲ[ h ≔ hnamesᴳ( ᴳ- D3) ᴴ⩲ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h}) ‗  v2 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h})] ] ),
        (ᵥ₎ v1 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ ʰmax( hnamesꟲ( C) ∪ ᴴ{ h})]).
      constructor; tauto.
      + exists (C ∘ v ⨞·⬜), t'. constructor; tauto.
    * exists (C ∘ ⬜⨞· t'), t. constructor; tauto.
Qed.

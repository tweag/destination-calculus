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
Lemma UnionCommutative : forall (G1 G2: ctx), G1 ⨄ G2 = G2 ⨄ G1. Proof. Admitted.

Lemma UnionPreservesValidityHole : forall (G1 G2: ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_HoleOnly G1 -> ctx_NoHole G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.
Lemma UnionPreservesValidityVar : forall (G1 G2: ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_VarOnly G1 -> ctx_NoVar G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.
Lemma UnionPreservesValidityDest : forall (G1 G2: ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_DestOnly G1 -> ctx_NoDest G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.

Definition equivT (A B : Type) : Type := (A -> B) * (B -> A).

Lemma VarOnlyNoHoleNoDestEquiv : forall (G : ctx), equivT (ctx_VarOnly G) (ctx_NoHole G * ctx_NoDest G). Proof. Admitted.
Lemma DestOnlyNoVarNoHoleEquiv : forall (G : ctx), equivT (ctx_DestOnly G) (ctx_NoVar G * ctx_NoHole G). Proof. Admitted.
Lemma HoleOnlyNoVarNoDestEquiv : forall (G : ctx), equivT (ctx_HoleOnly G) (ctx_NoVar G * ctx_NoDest G). Proof. Admitted.

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

Lemma SubLemma : forall (G1 G2 : ctx) (x : var) (m : mode) (T1 T2 : type) (t : term) (v : val), (G1 ⨄ ᶜ{ᵛ x ː m ‗ T2} ⊢ᵗ t ː T1) -> (G2 ⫦ᵛ v ː T2) -> mode_IsValid m -> ctx_IsValid (G1 ⨄ (m ᶜ· G2)) -> ctx_NoHole G2 -> ((G1 ⨄ (m ᶜ· G2)) ⊢ᵗ (t ˢ[ x ≔ v ]) ː T1).
Proof. Admitted.

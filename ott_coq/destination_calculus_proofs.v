Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.
Require Import Coq.Program.Equality.
From Hammer Require Import Tactics.

Lemma DestOnlyUnionBackward : forall (G1 G2 : ctx), ctx_DestOnly (G1 ⨄ G2) -> ctx_DestOnly G1 /\ ctx_DestOnly G2.
Proof. Admitted.
Lemma DestOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_DestOnly (m ᴳ· G) -> ctx_DestOnly G.
Proof. Admitted.
Lemma LinOnlyUnionBackward : forall (G1 G2 : ctx), ctx_LinOnly (G1 ⨄ G2) -> ctx_LinOnly G1 /\ ctx_LinOnly G2 /\ ctx_Disjoint G1 G2.
Proof. Admitted.
Lemma LinOnlyUnionForward : forall (G1 G2 : ctx), ctx_LinOnly G1 -> ctx_LinOnly G2 -> ctx_Disjoint G1 G2 -> ctx_LinOnly (G1 ⨄ G2).
Proof. Admitted.
Lemma LinOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_LinOnly (m ᴳ· G) -> ctx_LinOnly G /\ mode_IsLin m.
Proof. Admitted.
Lemma LinOnlyStimesForward : forall (m : mode) (G : ctx), ctx_LinOnly G -> mode_IsLin m -> ctx_LinOnly (m ᴳ· G).
Proof. Admitted.
Lemma LinOnlyIsValid : forall (G : ctx), ctx_LinOnly G -> ctx_IsValid G.
Proof. Admitted.
Lemma LinOnlyEmpty : ctx_LinOnly ᴳ{}.
Proof. Admitted.
Lemma IsLinIsValid : forall (m : mode), mode_IsLin m -> mode_IsValid m. Proof.
  intros m H. destruct H. apply (mode_IsValidProof (Lin, a)).
Qed.
Lemma hdns_Disjoint_implies_Disjoint : forall (D D' : ctx) (C : ectxs) (T U0: type), D ⊣ C : T ↣ U0 -> hdns_Disjoint hnamesꟲ( C) hnamesᴳ(D') -> ctx_Disjoint D D'. Proof. Admitted.
Lemma DisjointStimesLeftBackward : forall (m : mode) (D D' : ctx), ctx_Disjoint (m ᴳ· D) D' -> ctx_Disjoint D D'. Proof. Admitted.
Lemma DisjointStimesRightBackward : forall (m : mode) (D D' : ctx), ctx_Disjoint D (m ᴳ· D') -> ctx_Disjoint D D'. Proof. Admitted.
Lemma DisjointStimesLeftForward : forall (m : mode) (D D' : ctx), ctx_Disjoint D D' -> ctx_Disjoint (m ᴳ· D) D'. Proof. Admitted.
Lemma DisjointStimesRightForward : forall (m : mode) (D D' : ctx), ctx_Disjoint D D' -> ctx_Disjoint D (m ᴳ· D'). Proof. Admitted.
Lemma DisjointMinusLeftForward : forall (D D' : ctx), ctx_Disjoint D D' -> ctx_Disjoint (ᴳ-D) D'. Proof. Admitted.
Lemma DisjointMinusRightForward : forall (D D' : ctx), ctx_Disjoint D D' -> ctx_Disjoint D (ᴳ-D'). Proof. Admitted.
Lemma DisjointMinusLeftBackward : forall (D D' : ctx), ctx_Disjoint (ᴳ-D) D' -> ctx_Disjoint D D'. Proof. Admitted.
Lemma DisjointMinusRightBackward : forall (D D' : ctx), ctx_Disjoint D (ᴳ-D') -> ctx_Disjoint D D'. Proof. Admitted.
Lemma DisjointNestedLeft : forall (D D' D'' : ctx), ctx_Disjoint (D ⨄ D') D'' -> ctx_Disjoint D D'' /\ ctx_Disjoint D' D''. Proof. Admitted.
Lemma DisjointNestedRight : forall (D D' D'' : ctx), ctx_Disjoint D  (D' ⨄ D'') -> ctx_Disjoint D D' /\ ctx_Disjoint D D''. Proof. Admitted.

Lemma Ty_ectxs_DLin : forall (D : ctx) (C : ectxs) (t : term) (T U0 : type), (D ⊣ C : T ↣ U0) -> ctx_LinOnly D.
Proof.
  intros D C t T U0 H. induction H.
  - apply LinOnlyEmpty.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - best use: LinOnlyUnionBackward use: LinOnlyStimesBackward.
  - assert (ctx_LinOnly D2) as LinOnlyD2 by apply (LinOnlyUnionBackward D1 D2 IHTy_ectxs).
    assert (ctx_LinOnly (¹↑ ᴳ· D2)) as LinOnlysD2 by apply (LinOnlyStimesForward ¹↑ D2 LinOnlyD2 (mode_IsLinProof (Fin 1))).
    assert (ctx_Disjoint (D1 ⨄ D2) (ᴳ-D3)) by apply (hdns_Disjoint_implies_Disjoint (D1 ⨄ D2) (ᴳ-D3) C (T1 ⧔ U) U0 H H0).
    assert (ctx_Disjoint D1 (ᴳ- D3) /\ ctx_Disjoint D2 (ᴳ- D3)) as (DisjointD1mD3 & DisjointD2mD3) by apply (DisjointNestedLeft D1 D2 (ᴳ- D3) H1).
    assert (ctx_Disjoint D2 D3) as DisjointD2D3 by apply (DisjointMinusRightBackward D2 D3 DisjointD2mD3).
    assert (ctx_Disjoint (¹↑ ᴳ· D2) D3) as DisjointsD2D3 by apply (DisjointStimesLeftForward ¹↑ D2 D3 DisjointD2D3).
    exact (LinOnlyUnionForward (¹↑ ᴳ· D2) D3 LinOnlysD2 LinOnlyD3 DisjointsD2D3).
Qed.

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - inversion Tyt.
      (* Split context and propagates DestOnly *)
      rewrite <- H in DestOnlyD.
      assert (ctx_DestOnly (m ᴳ· P1) /\ ctx_DestOnly P2)
        as (DestOnlymD1 & DestOnlyD2)
        by apply (DestOnlyUnionBackward (m ᴳ· P1) P2 DestOnlyD).
      assert (ctx_DestOnly P1)
        as DestOnlyD1
        by apply (DestOnlyStimesBackward m P1 DestOnlymD1).
      rename P1 into D1, P2 into D2.
      assert (ctx_LinOnly D)
        as LinOnlyD
        by apply (Ty_ectxs_DLin D C t T U0 TyC).
      rewrite <- H in LinOnlyD.
      assert (ctx_LinOnly (m ᴳ· D1) /\ ctx_LinOnly D2 /\ ctx_Disjoint (m ᴳ· D1) D2) 
        as (LinOnlymD1 & LinOnlyD2 & DisjointmD1D2)
        by apply (LinOnlyUnionBackward (m ᴳ· D1) D2 LinOnlyD).
      assert (ctx_Disjoint D1 D2)
        as DisjointD1D2
        by apply (DisjointStimesLeftBackward m D1 D2 DisjointmD1D2).
      rewrite <- H in TyC.
      assert (ctx_LinOnly D1 /\ mode_IsLin m)
        as (LinOnlyD1 & IsLinm)
        by apply (LinOnlyStimesBackward m D1 LinOnlymD1).
      assert (D1 ⊣ C ∘ ⬜≻ u : T1 ↣ U0)
        as TyCc
        by apply (Ty_ectxs_AppFoc1 D1 C u T1 U0 D2 m T DisjointD1D2 DestOnlyD1 DestOnlyD2 (IsLinIsValid m IsLinm) (LinOnlyIsValid D2 LinOnlyD2) TyC Tyu).
      exact (Ty_eterm_ClosedEterm (C ∘ ⬜≻ u) t U0 D1 T1 (LinOnlyIsValid D1 LinOnlyD1) DestOnlyD1 TyCc Tyt0).
    - give_up.
Admitted.

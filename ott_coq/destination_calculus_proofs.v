Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.
Require Import Coq.Program.Equality.
From Hammer Require Import Tactics.

(* Todo : add equivalences *)

Lemma ValidUnionBackward : forall (G1 G2 : ctx), ctx_IsValid (G1 ⨄ G2) -> ctx_IsValid G1 /\ ctx_IsValid G2. Proof. Admitted.
Lemma ValidUnionForward : forall (G1 G2 : ctx), ctx_IsValid G1 -> ctx_IsValid G2 -> ctx_Disjoint G1 G2 -> ctx_IsValid (G1 ⨄ G2). Proof. Admitted.
Lemma ValidStimesBackward : forall (m : mode) (G : ctx), ctx_IsValid (m ᴳ· G) -> ctx_IsValid G /\ mode_IsValid m. Proof. Admitted.
Lemma ValidStimesForward : forall (m : mode) (G : ctx), mode_IsValid m -> ctx_IsValid G -> ctx_IsValid (m ᴳ· G). Proof. Admitted.
Lemma ValidMinusBackward : forall (G : ctx), ctx_IsValid (ᴳ-G) -> ctx_IsValid G. Proof. Admitted.
Lemma ValidMinusForward : forall (G : ctx), ctx_IsValid G -> ctx_IsValid (ᴳ-G). Proof. Admitted.
Lemma DestOnlyUnionBackward : forall (G1 G2 : ctx), ctx_DestOnly (G1 ⨄ G2) -> ctx_DestOnly G1 /\ ctx_DestOnly G2.
Proof. Admitted.
Lemma DestOnlyUnionForward : forall (G1 G2 : ctx), ctx_DestOnly G1 -> ctx_DestOnly G2 -> ctx_DestOnly (G1 ⨄ G2).
Proof. Admitted.
Lemma DestOnlyStimesForward : forall (m : mode) (G : ctx), ctx_DestOnly G -> ctx_DestOnly (m ᴳ· G).
Proof. Admitted.
Lemma DestOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_DestOnly (m ᴳ· G) -> ctx_DestOnly G.
Proof. Admitted.
Lemma DestOnlyMinusForward : forall (G : ctx), ctx_DestOnly G -> ctx_DestOnly (ᴳ-G).
Proof. Admitted.
Lemma DestOnlyMinusBackward : forall (G : ctx), ctx_DestOnly (ᴳ-G) -> ctx_DestOnly G.
Proof. Admitted.
Lemma LinOnlyUnionBackward : forall (G1 G2 : ctx), ctx_LinOnly (G1 ⨄ G2) -> ctx_LinOnly G1 /\ ctx_LinOnly G2 /\ ctx_Disjoint G1 G2.
Proof. Admitted.
Lemma LinOnlyUnionForward : forall (G1 G2 : ctx), ctx_LinOnly G1 -> ctx_LinOnly G2 -> ctx_Disjoint G1 G2 -> ctx_LinOnly (G1 ⨄ G2).
Proof. Admitted.
Lemma LinOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_LinOnly (m ᴳ· G) -> ctx_LinOnly G /\ mode_IsLin m.
Proof. Admitted.
Lemma LinOnlyStimesForward : forall (m : mode) (G : ctx), ctx_LinOnly G -> mode_IsLin m -> ctx_LinOnly (m ᴳ· G).
Proof. Admitted.
Lemma LinOnlyMinusBackward : forall (G : ctx), ctx_LinOnly (ᴳ-G) -> ctx_LinOnly G.
Proof. Admitted.
Lemma LinOnlyMinusForward : forall (G : ctx), ctx_LinOnly G -> ctx_LinOnly (ᴳ-G).
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

Lemma Ty_ectxs_DLin : forall (D : ctx) (C : ectxs) (T U0 : type), (D ⊣ C : T ↣ U0) -> ctx_LinOnly D.
Proof.
  intros D C T U0 H. induction H.
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

Lemma tSubLemma : forall (D1 D2 : ctx) (m : mode) (T1 T2 : type) (t' : term) (x : var) (v : val), ctx_DestOnly D2 -> (D2 ⨄ ᴳᵛ{ ᵛ x : m ‗ T1} ⊢ t' : T2) -> (D1 ⊢ ᵥ₎ v : T1) -> (m ᴳ· D1 ⨄ D2 ⊢ t' ᵗ[ x ≔ v] : T2). Proof. Admitted.

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - (* Sem-eterm-AppFoc1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (ctx_DestOnly (m ᴳ· D1) /\ ctx_DestOnly D2)
        as (DestOnlymD1 & DestOnlyD2)
        by apply (DestOnlyUnionBackward (m ᴳ· D1) D2 DestOnlyD).
      assert (ctx_DestOnly D1)
        as DestOnlyD1
        by apply (DestOnlyStimesBackward m D1 DestOnlymD1).
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2))
        as LinOnlyD
        by apply (Ty_ectxs_DLin (m ᴳ· D1 ⨄ D2) C T2 U0 TyC).
      assert (ctx_LinOnly (m ᴳ· D1) /\ ctx_LinOnly D2 /\ ctx_Disjoint (m ᴳ· D1) D2) 
        as (LinOnlymD1 & LinOnlyD2 & DisjointmD1D2)
        by apply (LinOnlyUnionBackward (m ᴳ· D1) D2 LinOnlyD).
      assert (ctx_Disjoint D1 D2)
        as DisjointD1D2
        by apply (DisjointStimesLeftBackward m D1 D2 DisjointmD1D2).
      assert (ctx_LinOnly D1 /\ mode_IsLin m)
        as (LinOnlyD1 & IsLinm)
        by apply (LinOnlyStimesBackward m D1 LinOnlymD1).
      assert (D1 ⊣ C ∘ ⬜≻ u : T1 ↣ U0)
        as TyCc
        by apply (Ty_ectxs_AppFoc1 D1 C u T1 U0 D2 m T2 DisjointD1D2 DestOnlyD1 DestOnlyD2 (IsLinIsValid m IsLinm) (LinOnlyIsValid D2 LinOnlyD2) TyC Tyu).
      exact (Ty_eterm_ClosedEterm (C ∘ ⬜≻ u) t U0 D1 T1 (LinOnlyIsValid D1 LinOnlyD1) DestOnlyD1 TyCc Tyt).
    - (* Sem-eterm-AppUnfoc1 *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D1, ValidD into ValidD1, DestOnlyD into DestOnlyD1. clear H0.
      inversion TyCc; subst. clear DestOnlyD0. rename T into T1.
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ u : T2)
        as TyApp
        by apply (Ty_term_App m D1 D2 (ᵥ₎ v) u T2 T1 Tyt Tyu).
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2))
        as LinOnlymD1D2
        by apply (Ty_ectxs_DLin (m ᴳ· D1 ⨄ D2) C T2 U0 TyC).
      assert (ctx_IsValid (m ᴳ· D1 ⨄ D2))
        as ValidmD1D2
        by apply (LinOnlyIsValid (m ᴳ· D1 ⨄ D2) LinOnlymD1D2).
      assert (ctx_DestOnly (m ᴳ· D1))
        as DestOnlymD
        by apply (DestOnlyStimesForward m D1 DestOnlyD1).
      assert (ctx_DestOnly (m ᴳ· D1 ⨄ D2))
        as DestOnlymD1D2
        by apply (DestOnlyUnionForward (m ᴳ· D1) D2 DestOnlymD DestOnlyD2).
      exact (Ty_eterm_ClosedEterm C (ᵥ₎ v ≻ u) U0 (m ᴳ· D1 ⨄ D2) T2 ValidmD1D2 DestOnlymD1D2 TyC TyApp).
    - (* Sem-eterm-AppFoc2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (ctx_DestOnly (m ᴳ· D1) /\ ctx_DestOnly D2)
        as (DestOnlymD1 & DestOnlyD2)
        by apply (DestOnlyUnionBackward (m ᴳ· D1) D2 DestOnlyD).
      assert (ctx_DestOnly D1)
        as DestOnlyD1
        by apply (DestOnlyStimesBackward m D1 DestOnlymD1).
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2))
        as LinOnlyD
        by apply (Ty_ectxs_DLin (m ᴳ· D1 ⨄ D2) C T2 U0 TyC).
      assert (ctx_LinOnly (m ᴳ· D1) /\ ctx_LinOnly D2 /\ ctx_Disjoint (m ᴳ· D1) D2) 
        as (LinOnlymD1 & LinOnlyD2 & DisjointmD1D2)
        by apply (LinOnlyUnionBackward (m ᴳ· D1) D2 LinOnlyD).
      assert (ctx_Disjoint D1 D2)
        as DisjointD1D2
        by apply (DisjointStimesLeftBackward m D1 D2 DisjointmD1D2).
      assert (ctx_LinOnly D1 /\ mode_IsLin m)
        as (LinOnlyD1 & IsLinm)
        by apply (LinOnlyStimesBackward m D1 LinOnlymD1).
      assert (D2 ⊣ C ∘ v ≻⬜ : (T1 ⁔ m → T2) ↣ U0)
        as TyCc
        by apply (Ty_ectxs_AppFoc2 D2 C v T1 m T2 U0 D1 DisjointD1D2 DestOnlyD1 DestOnlyD2 (LinOnlyIsValid (m ᴳ· D1) LinOnlymD1) TyC Tyt).
      exact (Ty_eterm_ClosedEterm (C ∘ v ≻⬜) u U0 D2 (T1 ⁔ m → T2) (LinOnlyIsValid D2 LinOnlyD2) DestOnlyD2 TyCc Tyu).
    - (* Sem-eterm-AppUnfoc2 *)
      inversion Tyt; subst. rename H2 into TyRv, TyC into TyCc, D into D2, ValidD into ValidD2, DestOnlyD into DestOnlyD2. clear H0.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tyu, Tyv into Tyt.
      assert (m ᴳ· D1 ⨄ D2 ⊢ ᵥ₎ v ≻ ᵥ₎ v' : T2)
        as TyApp
        by apply (Ty_term_App m D1 D2 (ᵥ₎ v) (ᵥ₎ v') T2 T1 Tyt Tyu).
      assert (ctx_LinOnly (m ᴳ· D1 ⨄ D2))
        as LinOnlymD1D2
        by apply (Ty_ectxs_DLin (m ᴳ· D1 ⨄ D2) C T2 U0 TyC).
      assert (ctx_IsValid (m ᴳ· D1 ⨄ D2))
        as ValidmD1D2
        by apply (LinOnlyIsValid (m ᴳ· D1 ⨄ D2) LinOnlymD1D2).
      assert (ctx_DestOnly (m ᴳ· D1))
        as DestOnlymD
        by apply (DestOnlyStimesForward m D1 DestOnlyD1).
      assert (ctx_DestOnly (m ᴳ· D1 ⨄ D2))
        as DestOnlymD1D2
        by apply (DestOnlyUnionForward (m ᴳ· D1) D2 DestOnlymD DestOnlyD2).
      exact (Ty_eterm_ClosedEterm C ((ᵥ₎ v) ≻ (ᵥ₎ v')) U0 (m ᴳ· D1 ⨄ D2) T2 ValidmD1D2 DestOnlymD1D2 TyC TyApp).
    - (* Sem-eterm-AppRed *)
      inversion Tyt; subst.
      assert (m = m0) as Eqmm0.
        inversion_clear Tyu. inversion_clear H0. tauto.
      rewrite <- Eqmm0 in Tyu, Tyt, TyC, DestOnlyD, ValidD. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into T2, t into t'.
      inversion Tyu; subst. clear H0. rename H2 into TyRv'.
      inversion TyRv'; subst. rename Tyt0 into Tyt'. rename H1 into DestOnlyD2.
      assert (m ᴳ· D1 ⨄ D2 ⊢ t' ᵗ[ x ≔ v] : T2)
        as Tytpsub
        by (apply (tSubLemma D1 D2 m T1 T2 t' x v DestOnlyD2 Tyt' Tyt)).
      exact (Ty_eterm_ClosedEterm C (t' ᵗ[ x ≔ v]) U0 (m ᴳ· D1 ⨄ D2) T2 ValidD DestOnlyD TyC Tytpsub).
    - give_up.
Admitted.

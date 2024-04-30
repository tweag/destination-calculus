Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.destination_calculus_notations.
Require Import Dest.ext_nat.
Require Import Coq.Program.Equality.
Require Import Dest.Finitely.
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
Require Import Dest.destination_calculus_proofs.
Require Import Lia.

Theorem Ty_term_sterm_Alloc : forall (P : ctx) (T : type), DisposableOnly P -> P ⊢ alloc : T ⧔ (⌊ T ⌋ ¹ν).
Proof.
  intros P T DisposP.
  unfold sterm_Alloc.
  rewrite union_empty_r_eq with (G := P).
  apply Ty_term_Val.
  - assumption.
  - rewrite union_empty_r_eq with (G := ᴳ{}).
    assert (hvarsᴳ(ᴳ- ᴳ{+ 1 : ¹ν ⌊ T ⌋ ¹ν }) = ᴴ{ 1}) as hvarsD3Eq.
      { rewrite hvars_minus_eq. unfold hvars_ctx, hvars_dom, ctx_singleton, hminus. rewrite dom_singleton_eq. cbn. reflexivity. }
    rewrite <- hvarsD3Eq. apply Ty_val_Ampar; swap 1 10; swap 2 11.
    + rewrite stimes_empty_eq, <- union_empty_l_eq. apply Ty_val_Dest.
    + rewrite <- union_empty_l_eq. rewrite hminus_singleton. apply Ty_val_Hole.
    + apply DestOnly_singleton_dest.
    + apply LinOnly_singleton_iff. cbn. constructor.
    + apply FinAgeOnly_singleton_iff. cbn. constructor.
    + apply ValidOnly_singleton_iff. cbn. constructor.
    + apply Disjoint_empty_l.
    + apply Disjoint_empty_l.
    + apply Disjoint_empty_l.
    + apply DestOnly_empty.
    + apply DestOnly_empty.
  - + apply DestOnly_empty.
Qed.

Theorem Ty_term_sterm_FromA' : forall (P : ctx) (t : term) (T : type), P ⊢ t : T ⧔ ① -> P ⊢ from⧔' t : T.
Proof.
  intros * Tyt.
  unfold sterm_FromA'.
  replace P with (¹ν ᴳ· P ᴳ+ ᴳ{}). 2:{ crush. }
  apply Ty_term_PatP with (T1 := T) (T2 := ! ¹∞ ⁔ ①).
  - constructor.
  - apply Disjoint_empty_l.
  - apply Disjoint_empty_l.
  - apply Disjoint_singletons_iff. sfirstorder.
  - apply Ty_term_FromA.
    replace P with (P ᴳ+ ᴳ{}). 2:{ crush. }
    apply Ty_term_Map with (T := ①).
    + apply Disjoint_empty_l.
    + assumption.
    + rewrite stimes_empty_eq, union_commutative. apply Ty_term_PatU.
      * rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ①}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
      * rewrite union_empty_l_eq with (G := ᴳ{}). apply Ty_term_Val. { apply DisposableOnly_empty. } { rewrite <- stimes_empty_eq with (m := ¹∞). apply Ty_val_Exp. apply Ty_val_Unit. repeat constructor. } { apply DestOnly_empty. }
  - replace (ᴳ{} ᴳ+ ᴳ{ 1 : ¹ν ‗ T} ᴳ+ ᴳ{ 2 : ¹ν ‗ ! ¹∞ ⁔ ①}) with (¹ν ᴳ· ᴳ{ 2 : ¹ν ‗ ! ¹∞ ⁔ ①} ᴳ+ ᴳ{ 1 : ¹ν ‗ T}). 2:{ crush. }
    apply Ty_term_PatE with (T := ①).
    + repeat constructor.
    + repeat constructor.
    + apply Disjoint_singletons_iff. sfirstorder.
    + rewrite union_empty_l_eq with (G := ᴳ{ 2 : ¹ν ‗ ! ¹∞ ⁔ ①}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
    + rewrite union_commutative. apply Ty_term_PatU.
      * cbn. rewrite union_empty_l_eq at 1. apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
      * rewrite union_empty_l_eq with (G := ᴳ{ 1 : ¹ν ‗ T}). apply Ty_term_Var. { apply DisposableOnly_empty. }  { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

Lemma Ty_term_sterm_FillLeaf : forall (P1 P2 : ctx) (t t' : term) (T : type) (n : mode), IsValid n -> P1 ⊢ t : ⌊T⌋n -> P2 ⊢ t' : T -> P1 ᴳ+ (¹↑ · n) ᴳ·P2 ⊢ t ˢ⨞ t' : ①.
Proof.
  intros * Validn Tyt Tyt'.
  unfold sterm_FillLeaf.
  replace (¹↑ · n) with (mode_times' ((¹↑ :: nil) ++ (n :: nil) ++ nil)). 2:{ cbn. destruct n; try destruct p; try destruct p2, a2; cbn; try destruct m, a; cbn; try rewrite Nat.add_0_r; trivial. }
  apply Ty_term_FillComp with (U := T); trivial.
  apply Ty_term_ToA. assumption.
Qed.

Lemma Ty_term_sterm_Fun : forall (P2 : ctx) (x: var) (m: mode) (u : term) (T U : type), UserDefined P2 -> IsValid m -> P2 # ᴳ{ x : m ‗ T} -> P2 ᴳ+ ᴳ{ x : m ‗ T} ⊢ u : U -> P2 ⊢ ˢλ x ⁔ m ⟼ u : T ⁔ m → U.
Proof.
  intros * UserDefinedP2 Validm DisjointP2x Tyu.
  unfold sterm_Fun.
  apply Ty_term_sterm_FromA'.
  rewrite union_empty_l_eq with (G := P2).
  apply Ty_term_Map with (T := ⌊T ⁔ m → U⌋ ¹ν).
  { apply UserDefined_Disjoint; trivial. lia. }
  apply Ty_term_sterm_Alloc. apply DisposableOnly_empty.
  rewrite union_commutative.
  replace (¹↑) with (mode_times' ((¹↑ :: nil) ++ (¹ν :: nil) ++ nil)). 2:{ cbn. reflexivity. }
  apply Ty_term_FillF with (T := T) (U := U); trivial.
  constructor.
  rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ⌊ T ⁔ m → U ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

Lemma Ty_term_sterm_Left : forall (P2 : ctx) (t : term) (T1 T2 : type), UserDefined P2 -> P2 ⊢ t : T1 -> P2 ⊢ ˢInl t : T1 ⨁ T2.
Proof.
  intros * UserDefinedP2 Tyt.
  unfold sterm_Left.
  apply Ty_term_sterm_FromA'.
  rewrite union_empty_l_eq with (G := P2).
  apply Ty_term_Map with (T := ⌊T1 ⨁ T2⌋ ¹ν).
  { apply UserDefined_Disjoint; trivial. lia. }
  apply Ty_term_sterm_Alloc. apply DisposableOnly_empty.
  rewrite union_commutative.
  replace (¹↑) with (¹↑ · ¹ν). 2:{ cbn. reflexivity. }
  apply Ty_term_sterm_FillLeaf with (T := T1); trivial.
  constructor.
  apply Ty_term_FillL with (T1 := T1) (T2 := T2); trivial.
  rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ⌊ T1 ⨁ T2 ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

Lemma Ty_term_sterm_Right : forall (P2 : ctx) (t : term) (T1 T2 : type), UserDefined P2 -> P2 ⊢ t : T2 -> P2 ⊢ ˢInr t : T1 ⨁ T2.
Proof.
  intros * UserDefinedP2 Tyt.
  unfold sterm_Right.
  apply Ty_term_sterm_FromA'.
  rewrite union_empty_l_eq with (G := P2).
  apply Ty_term_Map with (T := ⌊T1 ⨁ T2⌋ ¹ν).
  { apply UserDefined_Disjoint; trivial. lia. }
  apply Ty_term_sterm_Alloc. apply DisposableOnly_empty.
  rewrite union_commutative.
  replace (¹↑) with (¹↑ · ¹ν). 2:{ cbn. reflexivity. }
  apply Ty_term_sterm_FillLeaf with (T := T2); trivial.
  constructor.
  apply Ty_term_FillR with (T1 := T1) (T2 := T2); trivial.
  rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ⌊ T1 ⨁ T2 ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

Lemma Ty_term_sterm_Exp : forall (P2 : ctx) (m : mode) (t : term) (T : type), UserDefined P2 -> IsValid m -> P2 ⊢ t : T -> m ᴳ· P2 ⊢ ˢᴇ m ⁔ t : ! m ⁔ T.
Proof.
  intros * UserDefinedP2 Validm Tyt.
  unfold sterm_Exp.
  apply Ty_term_sterm_FromA'.
  rewrite union_empty_l_eq with (G := m ᴳ· P2).
  apply Ty_term_Map with (T := ⌊! m ⁔ T⌋ ¹ν).
  { apply UserDefined_Disjoint; trivial.
    unfold UserDefined in *. intros x. specialize (UserDefinedP2 x). unfold stimes. rewrite In_map_iff. assumption.
    lia. }
  apply Ty_term_sterm_Alloc. apply DisposableOnly_empty.
  rewrite union_commutative.
  rewrite stimes_is_action.
  apply Ty_term_sterm_FillLeaf with (P2 := P2) (T := T); trivial.
  replace (⌊ T ⌋ m) with (⌊ T ⌋ mode_times' ((m :: nil) ++ (¹ν :: nil) ++ nil)). 2: { f_equal. cbn. apply mode_times_linnu_r_eq. }
  apply Ty_term_FillE.
  constructor.
  rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ⌊ ! m ⁔ T ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

Lemma Ty_term_sterm_Prod : forall (P21 P22 : ctx) (t1 t2 : term) (T1 T2 : type), UserDefined P21 -> UserDefined P22 -> P21 ⊢ t1 : T1 -> P22 ⊢ t2 : T2 -> (P21 ᴳ+ P22) ⊢ ˢ(t1, t2) : T1 ⨂ T2.
Proof.
  intros * UserDefinedP21 UserDefinedP22 Tyt1 Tyt2.
  assert (UserDefined (P21 ᴳ+ P22)).
  { apply UserDefined_union_iff. split; assumption. }
  unfold sterm_Prod.
  apply Ty_term_sterm_FromA'.
  rewrite union_empty_l_eq with (G := P21 ᴳ+ P22).
  apply Ty_term_Map with (T := ⌊T1 ⨂ T2⌋ ¹ν).
  { apply UserDefined_Disjoint; trivial. lia. }
  apply Ty_term_sterm_Alloc. apply DisposableOnly_empty.
  rewrite union_commutative.
  replace (ᴳ{ 0 : ¹ν ‗ ⌊ T1 ⨂ T2 ⌋ ¹ν}) with (¹ν ᴳ· ᴳ{ 0 : ¹ν ‗ ⌊ T1 ⨂ T2 ⌋ ¹ν}). 2:{ rewrite stimes_linnu_eq. reflexivity. }
  apply Ty_term_PatP with (T1 := ⌊ T1 ⌋ ¹ν) (T2 := ⌊ T2 ⌋ ¹ν).
  constructor.
  { apply UserDefined_Disjoint; trivial.
    unfold UserDefined in *. intros x. specialize (H x). unfold stimes. rewrite In_map_iff. assumption.
  unfold max_runtime_var. lia. } { apply UserDefined_Disjoint; trivial.
    unfold UserDefined in *. intros x. specialize (H x). unfold stimes. rewrite In_map_iff. assumption.
  unfold max_runtime_var. lia. }
  apply Disjoint_singletons_iff. injection. inversion H0.
  apply Ty_term_FillP with (T1 := T1) (T2 := T2); trivial.
  rewrite union_empty_l_eq with (G := ᴳ{ 0 : ¹ν ‗ ⌊ T1 ⨂ T2 ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
  replace (¹↑ ᴳ· (P21 ᴳ+ P22) ᴳ+ ᴳ{ 1 : ¹ν ‗ ⌊ T1 ⌋ ¹ν} ᴳ+ ᴳ{ 2 : ¹ν ‗ ⌊ T2 ⌋ ¹ν}) with ((ᴳ{ 1 : ¹ν ‗ ⌊ T1 ⌋ ¹ν} ᴳ+ ¹↑ ᴳ· P21) ᴳ+ (ᴳ{ 2 : ¹ν ‗ ⌊ T2 ⌋ ¹ν} ᴳ+ ¹↑ ᴳ· P22)). 2:{ rewrite stimes_distrib_on_union. rewrite union_commutative with (G1 := ᴳ{ 1 : ¹ν ‗ ⌊ T1 ⌋ ¹ν}). rewrite union_associative. rewrite <- union_associative with (G1 := ¹↑ ᴳ· P21). rewrite <- union_associative. rewrite union_commutative with (G1 := ᴳ{ 1 : ¹ν ‗ ⌊ T1 ⌋ ¹ν} ᴳ+ ᴳ{ 2 : ¹ν ‗ ⌊ T2 ⌋ ¹ν}). crush. }
  apply Ty_term_PatU;
  replace (¹↑) with (¹↑ · ¹ν); try (cbn; reflexivity).
  apply Ty_term_sterm_FillLeaf with (P2 := P21) (T := T1); trivial.
  constructor.
  rewrite union_empty_l_eq with (G := ᴳ{ 1 : ¹ν ‗ ⌊ T1 ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
  apply Ty_term_sterm_FillLeaf with (P2 := P22) (T := T2); trivial.
  constructor.
  rewrite union_empty_l_eq with (G := ᴳ{ 2 : ¹ν ‗ ⌊ T2 ⌋ ¹ν}). apply Ty_term_Var. { apply DisposableOnly_empty. } { apply Disjoint_empty_l. } { repeat constructor. }
Qed.

Theorem Ty_sterm_coherency : forall (P : ctx) (t : term) (T : type), P ˢ⊢ t : T -> P ⊢ t : T.
Proof.
  intros * Tyst. inversion Tyst; subst. inversion Tyst; subst.
  - apply Ty_term_sterm_Alloc; trivial.
  - apply Ty_term_sterm_FromA'; trivial.
  - replace (mode_times' ((¹↑ :: nil) ++ (n :: nil) ++ nil)) with (¹↑ · n). 2:{ cbn. destruct n; try destruct p; try destruct p2, a2; cbn; try destruct m, a; cbn; try rewrite Nat.add_0_r; trivial. } apply Ty_term_sterm_FillLeaf with (T := T0); trivial.
  - apply Ty_term_sterm_Fun; trivial.
  - apply Ty_term_sterm_Left; trivial.
  - apply Ty_term_sterm_Right; trivial.
  - apply Ty_term_sterm_Exp; trivial.
  - apply Ty_term_sterm_Prod; trivial.
Qed.

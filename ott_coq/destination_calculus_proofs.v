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
Require Import Coq.Arith.Plus.
Require Import Arith.

(* =========================================================================
 * Waiting for PR #2 to be merged
 * ========================================================================= *)

Lemma gt_S_max : forall h H, HVars.mem h H = true -> h < maxᴴ(H) + 1.
Proof.
  intros * h_H. unfold hvar_max.
  destruct (HVars.max_elt H) eqn:h_max_elt.
  2:{ apply HVars.max_elt_spec3 in h_max_elt. unfold HVars.Empty in *.
      sfirstorder use: HVarsFacts.mem_iff. }
  apply HVars.max_elt_spec2  with (y:=h) in h_max_elt.
  - sfirstorder.
  - sfirstorder use: HVarsFacts.mem_iff.
Qed.

Lemma pre_cshift_surjective : forall H h' x, exists x', pre_cshift H h' x' = x.
Proof.
  intros *. unfold pre_cshift.
  destruct x as [xx|h].
  { exists (ˣ xx). reflexivity. }
  eexists (ʰ _). f_equal.
  eapply Permutation.pre_inverse.
Qed.

Lemma ValidOnly_cshift_iff: forall (G : ctx) (H : hvars) (h' : hvar), ValidOnly G <-> ValidOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ValidOnly, ctx_cshift.
  rewrite map_propagate_both with (Q := fun x b => IsValid (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- ValidOnly_cshift_iff : propagate_down.

Lemma DestOnly_cshift_iff: forall (G : ctx) (H : hvars) (h' : hvar), DestOnly G <-> DestOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold DestOnly, ctx_cshift.
  rewrite map_propagate_both with (Q := fun x b => IsDest _ b).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- DestOnly_cshift_iff : propagate_down.

Lemma LinNuOnly_cshift_iff : forall (G : ctx) (H : hvars) (h' : hvar), LinNuOnly G <-> LinNuOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold LinNuOnly, ctx_cshift.
  rewrite map_propagate_both with (Q := fun x b => IsLinNu (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- LinNuOnly_cshift_iff : propagate_down.

Lemma LinOnly_cshift_iff : forall (G : ctx) (H : hvars) (h' : hvar), LinOnly G <-> LinOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold LinOnly, ctx_cshift.
  rewrite map_propagate_both with (Q := fun x b => IsLin (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- LinOnly_cshift_iff : propagate_down.

Lemma FinAgeOnly_cshift_iff : forall (G : ctx) (H : hvars) (h' : hvar), FinAgeOnly G <-> FinAgeOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold FinAgeOnly, ctx_cshift.
  rewrite map_propagate_both with (Q := fun x b => IsFinAge (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- FinAgeOnly_cshift_iff : propagate_down.

(* TODO: Not necessarily true if `h\in D'` and `h+h' \in D`. *)
Lemma cshift_by_Disjoint_eq : forall (D D': ctx) (h': hvar), D # D' -> D ᴳ[ hvarsᴳ( D' ) ⩲ h' ] = D.
Proof. Admitted.

(* Sometimes bijections are beautiful *)
Lemma Disjoint_cshift_iff : forall D1 D2 H h', D1 # D2 <-> (D1 ᴳ[ H ⩲ h']) # (D2 ᴳ[ H ⩲ h']).
Proof. Admitted.

(* TODO: Annoying reasoning on supports. May work in setoid form though. But worth trying to do as an equality. *)
Lemma cshift_distrib_on_union : forall (G1 G2 : ctx) (H : hvars) (h' : hvar), (G1 ᴳ+ G2)ᴳ[ H⩲h' ] = G1 ᴳ[ H⩲h' ] ᴳ+ G2 ᴳ[ H⩲h' ].
Proof. Admitted.
(* TODO: add to canonalize? *)

Lemma cshift_distrib_on_stimes : forall (m : mode) (G : ctx) (H : hvars) (h' : hvar), (m ᴳ· G)ᴳ[ H⩲h' ] = m ᴳ· (G ᴳ[ H⩲h' ]).
Proof. Admitted.
(* TODO: add to canonalize? *)

(* TODO: not true, requires h' to be bigger than the max of H' as well, I believe. *)
Lemma cshift_by_max_impl_HDisjoint : forall (H H' : hvars) (h' : hvar), maxᴴ(H) < h' -> H ## (H' ᴴ⩲ h').
Proof. Admitted.

Lemma total_cshift_eq : forall (G : ctx) (h' : hvar), hvarsᴳ(G ᴳ[ hvarsᴳ( G ) ⩲ h' ]) = hvarsᴳ(G) ᴴ⩲ h'.
Proof. Admitted.
Lemma cshift_distrib_on_hminus : forall (G : ctx) (H : hvars) (h' : hvar), (ᴳ- G) ᴳ[ H ⩲ h' ] = (ᴳ- (G ᴳ[ H ⩲ h' ])).
Proof. Admitted.
Lemma cshift_distrib_on_hminus_inv : forall (G : ctx) (H : hvars) (h' : hvar), (ᴳ-⁻¹ G) ᴳ[ H ⩲ h' ] = (ᴳ-⁻¹ (G ᴳ[ H ⩲ h' ])).
Proof. Admitted.

Lemma cshift_distrib_on_hvars : forall H h' D, hvars_cshift hvarsᴳ( D) H h' = hvarsᴳ( D ᴳ[ H ⩲ h']).
Proof. Admitted.

(* Could really be generalised to any var-only context. *)
Lemma cshift_singleton_var_eq : forall H h' x m T, ᴳ{ x : m ‗ T}ᴳ[ H ⩲ h'] = ᴳ{ x : m ‗ T}.
Proof. Admitted.
Lemma TyR_val_cshift : forall (G : ctx) (v : val) (T : type) (H: hvars) (h': hvar), (G ⫦ v : T) -> (G ᴳ[ H⩲h' ] ⫦ v ᵛ[H⩲h'] : T)
with Ty_term_cshift : forall (G : ctx) (t : term) (T : type) (H: hvars) (h': hvar), (G ⊢ t : T) -> (G ᴳ[ H⩲h' ] ⊢ term_cshift t H h' : T).
Proof.
  - destruct 1.
    + cbn. unfold ctx_cshift, hvar_cshift, ctx_singleton, singleton.
      give_up . (* some extensionality required *)
    + give_up . (* I want to see a recursive case first *)
    + replace (ᴳ{} ᴳ[ H ⩲ h']) with ᴳ{}.
      2:{ apply ext_eq. cbn. congruence. }
      cbn.
      constructor.
    + cbn.
      constructor.
      * assumption.
      * erewrite <- cshift_singleton_var_eq, <- cshift_distrib_on_union.
        auto.
      * hauto l: on use: DestOnly_cshift_iff.
    + cbn.
      constructor. auto.
    + cbn.
      constructor. auto.
    + cbn. rewrite cshift_distrib_on_union.
      constructor. all: auto.
    + cbn. rewrite cshift_distrib_on_stimes.
      constructor. all: auto.
    + cbn. rewrite cshift_distrib_on_union, cshift_distrib_on_hvars, cshift_distrib_on_hminus.
      constructor.
      (* 11 goals *)
      * hauto l: on use: DestOnly_cshift_iff.
      * hauto l: on use: DestOnly_cshift_iff.
      * hauto l: on use: DestOnly_cshift_iff.
      * hauto l: on use: LinOnly_cshift_iff.
      * hauto l: on use: FinAgeOnly_cshift_iff.
      * hauto l: on use: ValidOnly_cshift_iff.
      * hauto l: on use: Disjoint_cshift_iff.
      * give_up. (* should be fixed now *)
      * give_up. (* arnaud: basically same *)
      * try rewrite <- cshift_distrib_on_stimes, <- cshift_distrib_on_union.
        (* TODO: I don't know how to prove that goal yet. Why doesn't D3 have a shift to it? *)
        give_up.
      * (* same as above *)
        give_up.
  - (* TODO *) give_up.
Admitted.

(* ========================================================================= *)

Lemma ValidOnly_union_backward : forall (G1 G2 : ctx), ValidOnly (G1 ᴳ+ G2) -> ValidOnly G1 /\ ValidOnly G2.
Proof.
  assert (forall m1 m2, IsValid (mode_plus m1 m2) -> IsValid m1 /\ IsValid m2) as h_mode_plus.
  { intros [[p1 a1]|] [[p2 a2]|]. all: cbn.
    all: sfirstorder. }
  unfold ValidOnly, union in *. intros *.
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

Lemma ValidOnly_union_backward' : forall (G1 G2 : ctx), Basics.impl (ValidOnly (G1 ᴳ+ G2)) (ValidOnly G1 /\ ValidOnly G2).
Proof.
  exact ValidOnly_union_backward.
Qed.
Hint Rewrite ValidOnly_union_backward' : propagate_down.

Lemma ValidOnly_union_forward : forall (G1 G2 : ctx), ValidOnly G1 -> ValidOnly G2 -> G1 # G2 -> ValidOnly (G1 ᴳ+ G2).
Proof.
  (* Note: merge_with_propagate_forward doesn't apply to this. Which is why the
     hypothesis `G1 # G2` is needed. *)
  intros * valid_G1 valid_G2 disjoint_G1G2. unfold ValidOnly in *.
  intros n b h. unfold union in *.
  destruct (In_dec n G1) as [[b1 h_inG1]|h_ninG1]; destruct (In_dec n G2) as [[b2 h_inG2]|h_ninG2]. all: rewrite ?nIn_iff_nMapsTo in *.
  - sfirstorder unfold: Disjoint.
  - hauto lq: on use: merge_with_Some_None_eq.
  - hauto lq: on use: merge_with_None_Some_eq.
  - hauto lq: on use: merge_with_None_None_eq.
Qed.

Lemma ValidOnly_union_forward' : forall (G1 G2 : ctx), Basics.impl (ValidOnly G1 /\ ValidOnly G2 /\ G1 # G2) (ValidOnly (G1 ᴳ+ G2)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: ValidOnly_union_forward.
Qed.
Hint Rewrite <- ValidOnly_union_forward' : suffices.

Lemma ValidOnly_singleton_iff : forall x m T, ValidOnly ᴳ{ x : m ‗ T} <-> IsValid m.
Proof.
  intros *. unfold ValidOnly.
  split.
  - intros h.
    specialize (h (ˣ x) (ₓ m ‗ T)). cbn in h.
    apply h.
    rewrite Fun.singleton_MapsTo_at_elt. reflexivity.
  - intros h x' binding hx'. unfold ctx_singleton in hx'. cbn.
    rewrite singleton_MapsTo_iff in hx'.
    rewrite eq_sigT_iff_eq_dep in hx'.
    destruct hx'. cbn.
    assumption.
Qed.
Hint Rewrite ValidOnly_singleton_iff : propagate_down.

Lemma ValidOnly_stimes_backward : forall (m : mode) (G : ctx), ValidOnly (m ᴳ· G) -> ValidOnly G.
Proof.
  intros *.
  intros validmG.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_var m
      | ʰ _ => stimes_dh m
      end)
    as mf.
  unfold ValidOnly in *. intros n binding mapstoG. specialize (validmG n (mf n binding)).
  assert ((m ᴳ· G) n = Some (mf n binding)).
    { eapply map_MapsTo_iff. exists binding. split. tauto. tauto. }
  specialize (validmG H).
  destruct n, binding; cbn in validmG; try rename n into m0; cbn; destruct m0; try constructor; unfold mode_times in validmG; destruct m in validmG; cbn in validmG; try destruct p as (_, _) in validmG; tauto.
Qed.

Lemma ValidOnly_stimes_backward' : forall (m : mode) (G : ctx), Basics.impl (ValidOnly (m ᴳ· G)) (ValidOnly G).
Proof.
  exact ValidOnly_stimes_backward.
Qed.
Hint Rewrite ValidOnly_stimes_backward' : propagate_down.

Lemma IsValid_times_iff : forall (m1 m2 : mode), IsValid (m1 · m2) <-> IsValid m1 /\ IsValid m2.
Proof.
  intros [[p1 a1]|] [[p2 a2]|]. all: cbn.
  all: sfirstorder.
Qed.
Hint Rewrite IsValid_times_iff : propagate_down.

Lemma ValidOnly_stimes_forward : forall (m : mode) (G : ctx), ValidOnly G /\ IsValid m -> ValidOnly (m ᴳ· G).
Proof.
  intros * [validG validm]. unfold ValidOnly, stimes in *.
  apply map_propagate_forward'.
  - eauto.
  - intros [xx|xh] []. all: cbn.
    all: sfirstorder use: IsValid_times_iff.
Qed.

Lemma ValidOnly_stimes_forward' : forall (m : mode) (G : ctx), Basics.impl (ValidOnly G /\ IsValid m) (ValidOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: ValidOnly_stimes_forward.
Qed.
Hint Rewrite <- ValidOnly_stimes_forward' : suffices.

Lemma DestOnly_union_iff : forall (G1 G2 : ctx), DestOnly (G1 ᴳ+ G2) <-> DestOnly G1 /\ DestOnly G2.
Proof.
  intros *. unfold DestOnly, union.
  apply merge_with_propagate_both.
  intros [xx|xh]. all: cbn. { sfirstorder. }
  intros b1 b2. unfold union_dh. destruct b1, b2;
  destruct (type_eq_dec T T0), (mode_eq_dec n n0). all:sfirstorder.
Qed.
Hint Rewrite DestOnly_union_iff : propagate_down.
Lemma DestOnly_stimes_iff : forall (m : mode) (G : ctx), DestOnly G <-> DestOnly (m ᴳ· G).
Proof.
  intros *. unfold DestOnly, stimes.
  rewrite map_propagate_both'.
  { sfirstorder. }
  unfold IsDest.
  hauto lq: on.
Qed.
Hint Rewrite <- DestOnly_stimes_iff : propagate_down.

Lemma nIsLin_mode_plus : forall b1 b2, ~IsLin (mode_plus b1 b2).
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

Lemma IsLinNu_wk_IsLin : forall (m : mode), IsLinNu m -> IsLin m.
Proof.
  intros *.
  sauto lq: on.
Qed.

Lemma IsLinNu_wk_IsLin' : forall (m : mode), Basics.impl (IsLinNu m) (IsLinNu m /\ IsLin m).
Proof.
  sfirstorder use: IsLinNu_wk_IsLin.
Qed.
Hint Rewrite IsLinNu_wk_IsLin' : saturate.

Lemma IsLin_wk_IsValid : forall (m : mode), IsLin m -> IsValid m.
Proof.
  intros m H. destruct H. apply (IsValidProof (Lin, a)).
Qed.

Lemma IsLin_wk_IsValid' : forall (m : mode), Basics.impl (IsLin m) (IsLin m /\ IsValid m).
Proof.
  sfirstorder use: IsLin_wk_IsValid.
Qed.
Hint Rewrite IsLin_wk_IsValid' : saturate.

Lemma IsLinNu_mode_plus : forall b1 b2, ~IsLinNu (mode_plus b1 b2).
Proof.
  intros b1 b2 h.
  apply IsLinNu_wk_IsLin in h.
  sfirstorder use: nIsLin_mode_plus.
Qed.

Lemma LinOnly_union_iff : forall (G1 G2 : ctx), LinOnly (G1 ᴳ+ G2) <-> LinOnly G1 /\ LinOnly G2 /\ G1 # G2.
Proof.
  intros *.
  apply merge_with_propagate_both_disjoint.
  intros [xx|xh]. all: cbn.
  - intros [? ?] [? ?]. cbn.
    match goal with
    |  |- context [if ?x then _ else _] => destruct x
    end.
    (* 2 goals *)
    all: sauto lq: on use: nIsLin_mode_plus.
  - intros [? ? ?|? ?] [? ? ?|? ?]. all: cbn.
    all: repeat match goal with
    |  |- context [if ?x then _ else _] => destruct x
           end.
    (* 7 goals *)
    all: sauto lq: on use: nIsLin_mode_plus.
Qed.
Hint Rewrite LinOnly_union_iff : propagate_down.

Lemma LinNuOnly_wk_LinOnly : forall (G : ctx), LinNuOnly G -> LinOnly G.
Proof.
  intros *.
  sfirstorder use: IsLinNu_wk_IsLin.
Qed.

Lemma LinOnly_wk_ValidOnly : forall (G : ctx), LinOnly G -> ValidOnly G.
Proof.
  intros *.
  sfirstorder use: IsLin_wk_IsValid.
Qed.

Lemma LinNuOnly_union_iff : forall (G1 G2 : ctx), LinNuOnly (G1 ᴳ+ G2) <-> LinNuOnly G1 /\ LinNuOnly G2 /\ G1 # G2.
Proof.
  intros *.
  split.
  - intros h.
    assert (G1 # G2) as disj.
    { hauto lq: on use: LinOnly_union_iff, LinNuOnly_wk_LinOnly. }
    assert (LinNuOnly G1 /\ LinNuOnly G2).
    2:{ hauto lq: on. }
    unfold LinNuOnly, union in *.
    eapply merge_with_propagate_backward_disjoint'.
    { apply disj. }
    eauto.
  - intros h. unfold LinNuOnly, union in *.
    apply merge_with_propagate_forward_disjoint.
    all: sfirstorder.
Qed.
Hint Rewrite LinNuOnly_union_iff : propagate_down.

Lemma LinNuOnly_stimes_forward : forall (m : mode) (G : ctx), IsLinNu m -> LinNuOnly G -> LinNuOnly (m ᴳ· G).
Proof.
  intros * linm linG.
  unfold LinNuOnly in *.
  intros n b h.
  unfold stimes in h.
  rewrite map_MapsTo_iff in h. destruct h. destruct H.
  specialize (linG n x H). destruct n.
  - unfold stimes_var in H0. destruct x. subst. unfold mode_of in *. unfold IsLinNu in *. subst. unfold mode_times. cbn. reflexivity.
  - unfold stimes_dh in H0. destruct x; subst.
    + unfold mode_of in *. unfold IsLinNu in *. subst. unfold mode_times. cbn. reflexivity.
    + unfold mode_of in *. unfold IsLinNu in *. subst. unfold mode_times. cbn. reflexivity.
Qed.
Lemma LinNuOnly_stimes_forward' : forall (m : mode) (G : ctx), Basics.impl (IsLinNu m /\ LinNuOnly G) (LinNuOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: LinNuOnly_stimes_forward.
Qed.
Hint Rewrite <- LinNuOnly_stimes_forward' : suffices.

Lemma n_plus_n0_eq_0_implies_n0_eq_0 : forall n n0 : nat,
  n + n0 = 0 -> n0 = 0.
Proof.
  intros n n0 H.
  apply Nat.eq_add_0 in H. (* Definition of zero *)
  destruct H. tauto.
Qed.

Lemma LinNuOnly_stimes_backward : forall (m : mode) (G : ctx), LinNuOnly (m ᴳ· G) -> LinNuOnly G.
Proof.
  intros *.
  intros islinNu.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_var m
      | ʰ _ => stimes_dh m
      end)
    as mf.
    unfold LinNuOnly in *. intros n binding mapstoG. specialize (islinNu n (mf n binding)).
  assert ((m ᴳ· G) n = Some (mf n binding)).
    { eapply map_MapsTo_iff. exists binding. split. tauto. tauto. }
  specialize (islinNu H). unfold stimes in H. rewrite map_MapsTo_iff in H. destruct H. destruct H. destruct n; cbn in *. all: rewrite H in mapstoG; inversion mapstoG; subst. all:clear mf.
  - destruct binding. unfold stimes_var in *. unfold mode_times, IsLinNu in *. destruct m, m0; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m, m0, a, a0; cbn; inversion islinNu; subst. rewrite H2, (n_plus_n0_eq_0_implies_n0_eq_0 n n0). all:trivial. }
    all: try congruence.
  - destruct binding; unfold stimes_dh in *; unfold mode_times, IsLinNu in *; try rename n into m0; destruct m; destruct m0; cbn; try destruct p; try destruct p0; unfold mul_times, age_times, ext_plus in *; try rename n into m0; try destruct m; try destruct m0; try destruct a; try destruct a0; cbn; inversion islinNu; subst; rewrite H2.
    + rewrite (n_plus_n0_eq_0_implies_n0_eq_0 n0 n1). all:trivial.
    + rewrite (n_plus_n0_eq_0_implies_n0_eq_0 n n0). all:trivial.
Qed.
Lemma LinNuOnly_stimes_backward' : forall (m : mode) (G : ctx), Basics.impl (LinNuOnly (m ᴳ· G)) (LinNuOnly G).
Proof.
  exact LinNuOnly_stimes_backward.
Qed.
Hint Rewrite LinNuOnly_stimes_backward' : propagate_down.

Lemma FinAgeOnly_union_backward : forall (G1 G2 : ctx), FinAgeOnly (G1 ᴳ+ G2) -> FinAgeOnly G1 /\ FinAgeOnly G2.
Proof.
  intros *.
  apply merge_with_propagate_backward.
  intros [xx|xh]. all: cbn.
  - intros [m1 ?] [m2 ?]. cbn.
    match goal with
    |  |- context [if ?x then _ else _] => destruct x
    end.
    2:{ inversion 1. }
    unfold mode_plus.
    destruct m1 as [[? [?|]]|]; destruct m2 as [[? [?|]]|]. all: unfold age_plus. all: cbn.
    all:try solve[inversion 1].
    (* Only one goal left *)
    repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    (* 2 goals *)
    all: sfirstorder.
  - intros [m1 ? ?|? m1] [m2 ? ?|? m2]. all: cbn.
    all: repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    (* 7 goals *)
    all:try solve[inversion 1].
    (* 2 goals left *)
    all:destruct m1 as [[? [?|]]|]; destruct m2 as [[? [?|]]|]. all: unfold age_plus. all: cbn.
    all:try solve[inversion 1].
    (* 2 goals left *)
    all: sfirstorder.
Qed.
Lemma FinAgeOnly_union_backward' : forall (G1 G2 : ctx), Basics.impl (FinAgeOnly (G1 ᴳ+ G2)) (FinAgeOnly G1 /\ FinAgeOnly G2).
Proof.
  exact FinAgeOnly_union_backward.
Qed.
Hint Rewrite FinAgeOnly_union_backward' : propagate_down.

Lemma FinAgeOnly_union_forward : forall (G1 G2 : ctx), (FinAgeOnly G1 /\ FinAgeOnly G2 /\ G1 # G2) -> FinAgeOnly (G1 ᴳ+ G2).
Proof.
  intros * h. unfold union, FinAgeOnly.
  apply merge_with_propagate_forward_disjoint.
  all: sfirstorder.
Qed.
Lemma FinAgeOnly_union_forward' : forall (G1 G2 : ctx), Basics.impl (FinAgeOnly G1 /\ FinAgeOnly G2 /\ G1 # G2) (FinAgeOnly (G1 ᴳ+ G2)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: FinAgeOnly_union_forward.
Qed.
Hint Rewrite <- FinAgeOnly_union_forward' : suffices.

Lemma LinOnly_stimes_backward : forall (m : mode) (G : ctx), LinOnly (m ᴳ· G) -> LinOnly G.
Proof.
  intros *.
  intros islin.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_var m
      | ʰ _ => stimes_dh m
      end)
    as mf.
    unfold LinOnly in *. intros n binding mapstoG. specialize (islin n (mf n binding)).
  assert ((m ᴳ· G) n = Some (mf n binding)).
    { eapply map_MapsTo_iff. exists binding. split. tauto. tauto. }
  specialize (islin H). unfold stimes in H. rewrite map_MapsTo_iff in H. destruct H. destruct H. destruct n; cbn in *. all: rewrite H in mapstoG; inversion mapstoG; subst. all:clear mf.
  - destruct binding. unfold stimes_var in *. unfold mode_times in *. destruct m eqn:em, m0 eqn:em0; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion islin. }
    all: inversion islin.
  - destruct binding; unfold stimes_dh in *; unfold mode_times in *; try destruct m eqn:em; try destruct m0 eqn:em0; try destruct n eqn:en; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion islin. }
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion islin. }
    all: inversion islin.
    { unfold mul_times, age_times, ext_plus in *. destruct m0, m1, a, a0; cbn; try constructor. all: inversion islin. }
Qed.
Lemma LinOnly_stimes_backward' : forall (m : mode) (G : ctx), Basics.impl (LinOnly (m ᴳ· G)) (LinOnly G).
Proof.
  exact LinOnly_stimes_backward.
Qed.
Hint Rewrite LinOnly_stimes_backward' : propagate_down.

Lemma LinOnly_stimes_forward : forall (m : mode) (G : ctx), IsLin m -> LinOnly G -> LinOnly (m ᴳ· G).
Proof.
  intros * validm linG.
  unfold LinOnly in *.
  intros n b h.
  unfold stimes in h.
  rewrite map_MapsTo_iff in h. destruct h. destruct H.
  specialize (linG n x H). destruct n.
  - unfold stimes_var in H0. destruct x. subst. unfold mode_of in *. destruct m, m0; try destruct p; try destruct p0; try destruct m; try destruct m0; unfold mode_times, mul_times in *; cbn; try constructor; try inversion linG; try inversion validm.
  - unfold stimes_dh in H0. destruct x; subst; unfold mode_of in *; try rename n into m0; destruct m, m0; try destruct p; try destruct p0; try destruct m; try destruct m0; unfold mode_times, mul_times in *; cbn; try constructor; try inversion linG; try inversion validm.
Qed.
Lemma LinOnly_stimes_forward' : forall (m : mode) (G : ctx), Basics.impl (IsLin m /\ LinOnly G) (LinOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: LinOnly_stimes_forward.
Qed.
Hint Rewrite <- LinOnly_stimes_forward' : suffices.

Lemma FinAgeOnly_stimes_backward : forall (m : mode) (G : ctx), FinAgeOnly (m ᴳ· G) -> FinAgeOnly G.
Proof.
  intros *.
  intros isfinAge.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_var m
      | ʰ _ => stimes_dh m
      end)
    as mf.
    unfold FinAgeOnly in *. intros n binding mapstoG. specialize (isfinAge n (mf n binding)).
  assert ((m ᴳ· G) n = Some (mf n binding)).
    { eapply map_MapsTo_iff. exists binding. split. tauto. tauto. }
  specialize (isfinAge H). unfold stimes in H. rewrite map_MapsTo_iff in H. destruct H. destruct H. destruct n; cbn in *. all: rewrite H in mapstoG; inversion mapstoG; subst. all:clear mf.
  - destruct binding. unfold stimes_var in *. unfold mode_times in *. destruct m eqn:em, m0 eqn:em0; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion isfinAge. }
    all: inversion isfinAge.
  - destruct binding; unfold stimes_dh in *; unfold mode_times in *; try destruct m eqn:em; try destruct m0 eqn:em0; try destruct n eqn:en; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion isfinAge. }
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion isfinAge. }
    all: inversion isfinAge.
    { unfold mul_times, age_times, ext_plus in *. destruct m0, m1, a, a0; cbn; try constructor. all: inversion isfinAge. }
Qed.
Lemma FinAgeOnly_stimes_backward' : forall (m : mode) (G : ctx), Basics.impl (FinAgeOnly (m ᴳ· G)) (FinAgeOnly G).
Proof.
  exact FinAgeOnly_stimes_backward.
Qed.
Hint Rewrite FinAgeOnly_stimes_backward' : propagate_down.

Lemma FinAgeOnly_stimes_forward : forall (m : mode) (G : ctx), IsFinAge m -> FinAgeOnly G -> FinAgeOnly (m ᴳ· G).
Proof.
  intros * validm finAgeG.
  unfold FinAgeOnly in *.
  intros n b h.
  unfold stimes in h.
  rewrite map_MapsTo_iff in h. destruct h. destruct H.
  specialize (finAgeG n x H). destruct n.
  - unfold stimes_var in H0. destruct x. subst. unfold mode_of in *. destruct m, m0; try destruct p; try destruct p0; try destruct a; try destruct a0; unfold mode_times, age_times in *; cbn; try constructor; try inversion finAgeG; try inversion validm.
  - unfold stimes_dh in H0. destruct x; subst; unfold mode_of in *; try rename n into m0; destruct m, m0; try destruct p; try destruct p0; try destruct a; try destruct a0; unfold mode_times, age_times in *; cbn; try constructor; try inversion finAgeG; try inversion validm.
Qed.
Lemma FinAgeOnly_stimes_forward' : forall (m : mode) (G : ctx), Basics.impl (IsFinAge m /\ FinAgeOnly G) (FinAgeOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: FinAgeOnly_stimes_forward.
Qed.
Hint Rewrite <- FinAgeOnly_stimes_forward' : suffices.

Lemma Disjoint_stimes_l_iff : forall (m : mode) (D D' : ctx), (m ᴳ· D) # D' <-> D # D'.
Proof.
  (* This proof, and the similar ones below are more complicated than
    they ought to because we can't rewrite under foralls. I [aspiwack]
    am however unwilling to spend the time and find a better way,
    copy-paste will do. *)
  intros *. unfold Disjoint, stimes.
  split.
  - intros h x.
    specialize (h x).
    rewrite In_map_iff in h.
    trivial.
  - intros h x.
    rewrite In_map_iff.
    eauto.
Qed.
Hint Rewrite Disjoint_stimes_l_iff : propagate_down.

Lemma Disjoint_stimes_r_iff : forall (m : mode) (D D' : ctx), D # (m ᴳ· D') <-> D # D'.
Proof.
  intros *. unfold Disjoint, stimes.
  split.
  - intros h x.
    specialize (h x).
    rewrite In_map_iff in h.
    trivial.
  - intros h x.
    rewrite In_map_iff.
    eauto.
Qed.
Hint Rewrite Disjoint_stimes_r_iff : propagate_down.

Lemma Disjoint_hminus_l_iff : forall (D D' : ctx), D # D' <-> ((ᴳ- D)) # D'.
Proof.
  intros *. unfold Disjoint, hminus.
  split.
  - intros h x.
    rewrite In_map_iff.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite In_map_iff in h.
    trivial.
Qed.
Hint Rewrite <- Disjoint_hminus_l_iff : propagate_down.

Lemma Disjoint_hminus_inv_l_iff : forall (D D' : ctx), D # D' <-> ((ᴳ-⁻¹ D)) # D'.
Proof.
  intros *. unfold Disjoint, hminus_inv.
  split.
  - intros h x.
    rewrite In_map_iff.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite In_map_iff in h.
    trivial.
Qed.

Lemma Disjoint_hminus_r_iff : forall (D D' : ctx), D # D' <-> D # ((ᴳ-D')).
Proof.
  intros *. unfold Disjoint, hminus.
  split.
  - intros h x.
    rewrite In_map_iff.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite In_map_iff in h.
    trivial.
Qed.
Hint Rewrite <- Disjoint_hminus_r_iff : propagate_down.

Lemma Disjoint_hminus_inv_r_iff : forall (D D' : ctx), D # D' <-> D # ((ᴳ-⁻¹D')).
Proof.
  intros *. unfold Disjoint, hminus_inv.
  split.
  - intros h x.
    rewrite In_map_iff.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite In_map_iff in h.
    trivial.
Qed.

Lemma Disjoint_union_l_iff : forall (D D' D'' : ctx), (D ᴳ+ D') # D'' <-> D # D'' /\ D' # D''.
Proof.
  intros *. unfold Disjoint, union.
  split.
  - intros h.
    split.
    all: intros x.
    all: specialize (h x).
    all: rewrite In_merge_iff in h.
    all: sfirstorder.
  - intros h x.
    rewrite In_merge_iff.
    sfirstorder.
Qed.
Hint Rewrite Disjoint_union_l_iff : propagate_down.

Lemma Disjoint_union_r_iff : forall (D D' D'' : ctx), D # (D' ᴳ+ D'') <-> D # D' /\ D # D''.
Proof.
Proof.
  intros *. unfold Disjoint, union.
  split.
  - intros h.
    split.
    all: intros x.
    all: specialize (h x).
    all: rewrite In_merge_iff in h.
    all: sfirstorder.
  - intros h x.
    rewrite In_merge_iff.
    sfirstorder.
Qed.
Hint Rewrite Disjoint_union_r_iff : propagate_down.

Lemma Disjoint_commutative : forall (G1 G2 : ctx), G1 # G2 <-> G2 # G1.
Proof.
  intros *. unfold Disjoint.
  sfirstorder.
Qed.

Lemma LinOnly_empty : LinOnly ᴳ{}.
Proof.
  scongruence unfold: LinOnly.
Qed.

Lemma FinAgeOnly_empty : FinAgeOnly ᴳ{}.
Proof.
  scongruence unfold: FinAgeOnly.
Qed.

Lemma DestOnly_empty : DestOnly ᴳ{}.
Proof.
  sauto q: on unfold: DestOnly.
Qed.

Lemma Disjoint_empty_l : forall (G : ctx), ᴳ{} # G.
Proof.
  sauto q: on unfold: Disjoint.
Qed.

Lemma Disjoint_empty_r : forall (G : ctx), Disjoint G ᴳ{}.
Proof.
  sauto q: on unfold: Disjoint.
Qed.

Lemma DisposableOnly_empty : DisposableOnly ᴳ{}.
Proof.
  sauto q: on unfold: DisposableOnly.
Qed.

Lemma stimes_empty_eq : forall (m : mode), m ᴳ· ᴳ{} = ᴳ{}.
Proof.
  intros *. unfold ctx_empty, empty, stimes, map. cbn.
  f_equal.
  apply proof_irrelevance.
Qed.
Hint Rewrite stimes_empty_eq : canonalize.

Lemma hminus_empty_eq : (ᴳ- ᴳ{}) = ᴳ{}.
Proof.
  apply ext_eq.
  all: sfirstorder.
Qed.
Hint Rewrite hminus_empty_eq : canonalize.

Lemma hminus_inv_empty_eq : (ᴳ-⁻¹ ᴳ{}) = ᴳ{}.
Proof.
  unfold hminus_inv, empty, map. cbn.
  apply ext_eq.
  all: sfirstorder.
Qed.
Hint Rewrite hminus_inv_empty_eq : canonalize.

Lemma union_empty_r_eq : forall (G : ctx), G = G ᴳ+ ᴳ{}.
Proof.
  intros *.
  apply ext_eq.
  intros x. unfold union.
  destruct (In_dec x G) as [[y h_inG]|h_ninG]. all: rewrite ?nIn_iff_nMapsTo in *.
  + erewrite merge_with_Some_None_eq.
    2:{ eauto. }
    eauto.
  + erewrite merge_with_None_None_eq.
    all: eauto.
Qed.
Hint Rewrite <- union_empty_r_eq : canonalize.

Lemma union_empty_l_eq : forall (G : ctx), G = ᴳ{} ᴳ+ G.
Proof.
  intros *.
  apply ext_eq.
  intros x. unfold union.
  destruct (In_dec x G) as [[y h_inG]|h_ninG]. all: rewrite ?nIn_iff_nMapsTo in *.
  + erewrite merge_with_None_Some_eq.
    2:{ eauto. }
    eauto.
  + erewrite merge_with_None_None_eq.
    all: eauto.
Qed.
Hint Rewrite <- union_empty_l_eq : canonalize.

Lemma DestOnly_Disjoint_singleton_var : forall (G : ctx) (x : var) (m : mode) (T : type), DestOnly G -> G # (ᴳ{ x : m ‗ T}).
Proof.
  intros * destonly.
  unfold DestOnly, Disjoint in *.
  intros n inG inSing.
  unfold In, Fun.In in *.
  destruct inG as (binding & mapsto).
  specialize (destonly n binding mapsto).
  unfold ctx_singleton in inSing. destruct inSing. rewrite singleton_MapsTo_iff in H.
  inversion H; subst.
  unfold IsDest in destonly. assumption.
Qed.

Lemma mode_plus_commutative : forall (m n: mode), mode_plus m n = mode_plus n m.
Proof.
  intros [[p1 a1]|] [[p2 a2]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct a1 as [?|]; destruct a2 as [?|].
  all: unfold mul_plus, age_plus. all: cbn.
  all: repeat match goal with
         |  |- context [if ?x then _ else _] => destruct x
         end.
  (* 28 goals *)
  all: congruence.
Qed.

Lemma mode_plus_associative : forall (m n o: mode), mode_plus m (mode_plus n o) = mode_plus (mode_plus m n) o.
Proof.
  intros [[p1 a1]|] [[p2 a2]|] [[p3 a3]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct p3 as [|]; destruct a1 as [?|]; destruct a2 as [?|]; destruct a3 as [?|].
  all: unfold mul_plus, age_plus. all: cbn.
  all: repeat match goal with
         |  |- context [if ?x then _ else _] => destruct x
         | H: context [if ?x then _ else _] |- _ => destruct x
         end.
  (* 232 goals *)
  all: congruence.
Qed.

Lemma union_commutative' : forall (G1 G2 : ctx) x, (G1 ᴳ+ G2) x = (G2 ᴳ+ G1) x.
Proof.
  intros *. unfold union.
  apply merge_with_commutative'.
  destruct x as [xx|xh].
  - intros [? ?] [? ?]. cbn.
    repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    all: sfirstorder use: mode_plus_commutative.
  - intros [? ? ?|? ?] [? ? ?|? ?]. all: cbn.
    all: repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    all: sfirstorder use: mode_plus_commutative.
Qed.

Lemma union_commutative : forall (G1 G2 : ctx), G1 ᴳ+ G2 = G2 ᴳ+ G1.
Proof.
  intros *. apply ext_eq.
  apply union_commutative'.
Qed.

Lemma union_associative : forall (G1 G2 G3 : ctx), G1 ᴳ+ (G2 ᴳ+ G3) = (G1 ᴳ+ G2) ᴳ+ G3.
Proof.
  intros *. unfold union.
  apply merge_with_associative.
  intros [xx|xh].
  - intros [? ?] [? ?] [? ?]. cbn. unfold union_var.
    repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    { rewrite mode_plus_associative. reflexivity. }
    all: try sfirstorder.
    (* 3 goals left *)
    all: destruct m as [[? ?]|]; cbn.
    all: sfirstorder.
  - intros [? ? ?|? ?] [? ? ?|? ?] [? ? ?|? ?]. all: cbn. all: unfold union_dh.
    all: repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    (* 94 goals *)
    all: try solve[rewrite mode_plus_associative; reflexivity].
    (* 92 goals left *)
    all: try sfirstorder.
    (* 16 goals left *)
    all: try destruct m as [[? ?]|]; try destruct n as [[? ?]|]; cbn.
    (* 58 goals *)
    all: scongruence.
Qed.
Hint Rewrite union_associative : canonalize.

Lemma mode_times_commutative : forall (m n : mode), m · n = n · m.
Proof.
  intros [[p1 a1]|] [[p2 a2]|]. cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct a1 as [?|]; destruct a2 as [?|].
  all: cbn.
  all: sfirstorder use: PeanoNat.Nat.add_comm.
Qed.

Lemma mode_times_associative : forall (m1 m2 m3 : mode), m1 · (m2 · m3) = (m1 · m2) · m3.
Proof.
  intros [[p1 a1]|] [[p2 a2]|] [[p3 a3]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct p3 as [|]; destruct a1 as [?|]; destruct a2 as [?|]; destruct a3 as [?|]. all: cbn.
  all: sfirstorder use: PeanoNat.Nat.add_assoc.
Qed.
Hint Rewrite mode_times_associative : canonalize.

Lemma mode_times_linnu_r_eq : forall (m : mode), m · ¹ν = m.
Proof.
  intros [[p a]|]. all: cbn.
  2:{ trivial. }
  destruct p as [|]; destruct a as [?|]. all: cbn.
  all: hauto lq: on use: PeanoNat.Nat.add_0_r.
Qed.
Hint Rewrite mode_times_linnu_r_eq : canonalize.

Lemma mode_times_linnu_l_eq : forall (m : mode), ¹ν · m = m.
Proof.
  intros [[p a]|]. all: cbn.
  2:{ trivial. }
  destruct p as [|]; destruct a as [?|]. all: cbn.
  all: hauto lq: on use: PeanoNat.Nat.add_0_l.
Qed.
Hint Rewrite mode_times_linnu_l_eq : canonalize.

Lemma stimes_is_action : forall (m n : mode) (G : ctx), m ᴳ· (n ᴳ· G) = (m · n) ᴳ· G.
Proof.
  intros *.
  apply ext_eq.
  intros x. unfold stimes.
  rewrite map_comp.
  apply map_ext. clear x.
  intros [xx|xh].
  - apply functional_extensionality. cbn.
    intros [? ?]. cbn.
    sfirstorder use: mode_times_associative.
  - apply functional_extensionality. cbn.
    intros [? ? ?|? ?]. all: cbn.
    all: sfirstorder use: mode_times_associative.
Qed.
Hint Rewrite stimes_is_action : canonalize.

Lemma mode_times_distrib_plus : forall (m n o : mode), m · (mode_plus n o) = mode_plus (m · n) (m · o).
Proof.
  intros [[p1 a1]|] [[p2 a2]|] [[p3 a3]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct p3 as [|]; destruct a1 as [?|]; destruct a2 as [?|]; destruct a3 as [?|]. all: unfold mul_plus, mul_times, age_plus, age_times, ext_plus; repeat destruct age_eq_dec. all: trivial; try congruence; try reflexivity.
  all: exfalso; assert (n0 <> n1) as Hneq by (intros H; apply n2; rewrite H; constructor);
                  assert (n + n0 = n + n1) as Heq by (injection e; auto);
                  apply Hneq; rewrite Nat.add_cancel_l with (p := n) in Heq; assumption.
Qed.

Lemma stimes_distrib_union : forall (m : mode) (G1 G2 : ctx),  m ᴳ· (G1 ᴳ+ G2) = m ᴳ· G1 ᴳ+ m ᴳ· G2.
Proof.
  intros *.
  apply ext_eq.
  intros n. unfold stimes, union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.on_conflict_do.
  assert (exists e, age_eq_dec Inf Inf = left e) as eq_inf_inf.
    { destruct age_eq_dec. exists e; reflexivity. congruence. } destruct eq_inf_inf as (eqrefl & eq_inf_inf).
  destruct (In_dec n G1), (In_dec n G2), n.
  - destruct H as (binding1 & mapstoG1), H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG1; rewrite mapstoG2; cbn.
    f_equal. unfold stimes_var, union_var.
    destruct binding1, binding2, (type_eq_dec T T0).
    { rewrite mode_times_distrib_plus; reflexivity. }
    { unfold mode_times. destruct m. destruct p. all: tauto. }
  - destruct H as (binding1 & mapstoG1), H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG1; rewrite mapstoG2; cbn.
    f_equal. unfold stimes_dh, union_dh.
    destruct binding1, binding2, (type_eq_dec T T0); try destruct (mode_eq_dec n n0).
    all: try rewrite mode_times_distrib_plus; try reflexivity.
    all: unfold mode_times; destruct m; try destruct p. all: tauto.
  - destruct H as (binding1 & mapstoG1); cbn; rewrite mapstoG1; cbn. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
  - destruct H as (binding1 & mapstoG1); cbn; rewrite mapstoG1; cbn. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
  - destruct H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG2; cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. reflexivity.
  - destruct H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG2; cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. reflexivity.
  - cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
  - cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
Qed.
Hint Rewrite stimes_distrib_union : canonalize.

Lemma hminus_distrib_union : forall (G1 G2 : ctx), G1 # G2 ->(ᴳ- (G1 ᴳ+ G2)) = (ᴳ-G1) ᴳ+ (ᴳ-G2).
Proof.
  intros * DisjointG1G2.
  apply ext_eq.
  intros n. unfold hminus, union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.on_conflict_do.
  destruct (In_dec n G1), (In_dec n G2).
  { unfold Disjoint in DisjointG1G2. specialize (DisjointG1G2 n H H0). contradiction. }
  all: destruct n; try destruct H as (binding1 & mapstoG1); try destruct H0 as (binding2 & mapstoG2); cbn; try rewrite nIn_iff_nMapsTo in H; try rewrite nIn_iff_nMapsTo in H0; try rewrite mapstoG1; try rewrite mapstoG2; try rewrite H; try rewrite H0; cbn; trivial.
Qed.

Lemma hminus_inv_distrib_union : forall (G1 G2 : ctx), G1 # G2 ->(ᴳ-⁻¹ (G1 ᴳ+ G2)) = (ᴳ-⁻¹G1) ᴳ+ (ᴳ-⁻¹G2).
Proof.
  intros * DisjointG1G2.
  apply ext_eq.
  intros n. unfold hminus_inv, union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.on_conflict_do.
  destruct (In_dec n G1), (In_dec n G2).
  { unfold Disjoint in DisjointG1G2. specialize (DisjointG1G2 n H H0). contradiction. }
  all: destruct n; try destruct H as (binding1 & mapstoG1); try destruct H0 as (binding2 & mapstoG2); cbn; try rewrite nIn_iff_nMapsTo in H; try rewrite nIn_iff_nMapsTo in H0; try rewrite mapstoG1; try rewrite mapstoG2; try rewrite H; try rewrite H0; cbn; trivial.
Qed.

Lemma stimes_linnu_eq :  forall (G: ctx), G = ¹ν ᴳ· G.
Proof.
  intros *.
  apply ext_eq.
  intros x. unfold stimes.
  destruct x as [xx|xh].
  + destruct (In_dec (ˣ xx) G) as [[binding mapsto]|notinG].
    * rewrite mapsto. symmetry. apply map_MapsTo_iff. exists binding. split; trivial.
      unfold stimes_var, mode_times. destruct binding, m; try destruct p; try destruct m, a; unfold mul_times, age_times, ext_plus; rewrite? Nat.add_0_l; reflexivity.
    * rewrite nIn_iff_nMapsTo in notinG. rewrite notinG. symmetry. rewrite map_nMapsTo_iff; tauto.
  + destruct (In_dec (ʰ xh) G) as [[binding mapsto]|notinG].
    * rewrite mapsto. symmetry. apply map_MapsTo_iff. exists binding. split; trivial.
      unfold stimes_dh, mode_times. destruct binding; try rename n into m; destruct m; try destruct p; try destruct m, a; unfold mul_times, age_times, ext_plus; rewrite? Nat.add_0_l; reflexivity.
    * rewrite nIn_iff_nMapsTo in notinG. rewrite notinG. symmetry. rewrite map_nMapsTo_iff; tauto.
Qed.
Hint Rewrite <- stimes_linnu_eq : canonalize.

Lemma hunion_hempty_l_eq : forall (H : hvars), H = (HVars.empty ∪ H).
Proof.
  intros H.
  apply HVars.eq_leibniz. unfold HVars.eq.
  intros h. rewrite HVarsFacts.union_iff. (* Definition of set equality *)
  split.
  - right; tauto.
  - intros [H1 | H2]. (* By definition of union, we can prove any goal if it is in one of the two sets *)
    + inversion H1.
    + tauto.
Qed.

Lemma hunion_hempty_r_eq : forall (H : hvars), H = (HVars.union H HVars.empty).
Proof.
  intros H.
  apply HVars.eq_leibniz. unfold HVars.eq.
  intros h. rewrite HVarsFacts.union_iff. (* Definition of set equality *)
  split.
  - intros H'. left; assumption.
  - intros [H1 | H2]. (* By definition of union, we can prove any goal if it is in one of the two sets *)
    + tauto.
    + inversion H2.
Qed.

Definition ListSubset {A : Type} (l1 l2 : list A) : Prop := forall x, List.In x l1 -> List.In x l2.

Lemma ListSubset_refl {A : Type} : forall (l : list A), ListSubset l l.
Proof.
  intros l x H. assumption.
Qed.

Lemma ListSubset_cons_iff {A : Type} : forall (l1 l2 : list A) (x : A), ListSubset (x :: l1) l2 <-> List.In x l2 /\ ListSubset l1 l2.
Proof.
  intros l1 l2 x.
  split.
  - intros Subsetcons. split.
    + unfold ListSubset in Subsetcons. specialize (Subsetcons x (in_eq x l1)). assumption.
    + unfold ListSubset in *. intros y; specialize (Subsetcons y); intros Inyl1. apply (List.in_cons x) in Inyl1. specialize (Subsetcons Inyl1). assumption.
  - intros (Inxl2 & Subsetl1l2). unfold ListSubset in *. intros y. specialize (Subsetl1l2 y). intros Inycons. destruct Inycons.
    + subst; assumption.
    + specialize (Subsetl1l2 H); assumption.
Qed.

Lemma hvars_spec : forall (G : ctx) (h : hvar), HVars.In h (hvarsᴳ(G)) <-> exists x, G (name_DH h) = Some x.
Proof.
  intros *. split.
  - intros Hin. unfold hvars_ctx, hvars_dom in Hin. remember (dom(G)) as l in Hin. assert (ListSubset l (dom G)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    * inversion Hin.
    * rename a into n, l into ns.
      rewrite ListSubset_cons_iff in H; destruct H; rewrite dom_spec in H; rewrite In_iff_exists_Some in H. destruct ((fix hvars_dom (dom : list name) : HVars.t := match dom with
| ©️⬜ => HVars.empty
| xs ∘ ˣ _ => hvars_dom xs
| xs ∘ ʰ h => HVars.add h (hvars_dom xs)
end) ns).
      destruct n.
      + specialize (IHl Hin H0). assumption.
      + destruct (Nat.eq_dec h h0).
        { rewrite e in *; assumption. }
        { assert (HVars.In h {| HVars.this := this; HVars.is_ok := is_ok |}).
          { rewrite HVars.add_spec in Hin. destruct Hin. congruence. assumption. }
          specialize (IHl H1 H0). assumption.
        }
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. apply dom_spec in Hin. unfold hvars_ctx, hvars_dom. remember (dom(G)) as l. assert (ListSubset l (dom G)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    * inversion Hin.
    * rename a into n, l into ns.
      destruct n.
      { rewrite ListSubset_cons_iff in H; destruct H.
        assert (List.In (ʰ h) ns).
        { destruct Hin. congruence. assumption. }
        specialize (IHl H1 H0). assumption.
      }
      { destruct (Nat.eq_dec h h0).
        { rewrite e in *. apply HVars.add_spec. left. congruence. }
        { assert (List.In (ʰ h) ns).
          { destruct Hin. inversion H0. congruence. assumption. }
          apply ListSubset_cons_iff in H; destruct H. specialize (IHl H0 H1). apply HVars.add_spec. right. assumption.
        }
      }
Qed.

Lemma HIn_union_iff : forall (G G': ctx) (h: hvar), HVars.In h hvarsᴳ(G ᴳ+ G') <-> HVars.In h hvarsᴳ(G) \/ HVars.In h hvarsᴳ(G').
Proof.
  intros *. split.
  - intros Hin. apply hvars_spec in Hin. rewrite hvars_spec, hvars_spec. destruct Hin as [x Hin]. destruct (In_dec (name_DH h) G) as [inG|notinG], (In_dec (name_DH h) G') as [inG'|notinG']; try unfold In, Fun.In in inG; try unfold In, Fun.In in inG'.
    + left. assumption.
    + left. assumption.
    + right. assumption.
    + assert (In (ʰ h) (G ᴳ+ G')). { unfold In, Fun.In. exists x. assumption. } apply In_merge_iff in H. unfold In, Fun.In in H. assumption.
  - intros [inG|inG'].
    + apply hvars_spec. rewrite hvars_spec in inG. destruct inG as [x inG]. destruct (In_dec (ʰ h) G').
      * unfold In, Fun.In in H. destruct H as (y & H). exists (union_dh x y). apply merge_with_Some_Some_eq. split; assumption.
      * rewrite nIn_iff_nMapsTo in H. exists x. apply merge_with_Some_None_eq. split; assumption.
    + apply hvars_spec. rewrite hvars_spec in inG'. destruct inG' as [x inG']. destruct (In_dec (ʰ h) G).
      * unfold In, Fun.In in H. destruct H as (y & H). exists (union_dh y x). apply merge_with_Some_Some_eq. split; assumption.
      * rewrite nIn_iff_nMapsTo in H. exists x. apply merge_with_None_Some_eq. split; assumption.
Qed.

Lemma HIn_stimes_iff : forall (m : mode) (G : ctx) (h: hvar), HVars.In h hvarsᴳ(m ᴳ· G) <-> HVars.In h hvarsᴳ(G).
Proof.
  sauto lq: on use: hvars_spec, map_MapsTo_iff.
Qed.

Lemma HSubset_union_backward : forall (G G': ctx) (H: hvars), HVars.Subset hvarsᴳ(G ᴳ+ G') H -> HVars.Subset hvarsᴳ(G) H /\ HVars.Subset hvarsᴳ(G') H.
Proof.
  unfold HVars.Subset in *. intros *. intros Hyp. split.
  - intros h Hin. specialize (Hyp h). apply Hyp, HIn_union_iff. left. assumption.
  - intros h Hin. specialize (Hyp h). apply Hyp, HIn_union_iff. right. assumption.
Qed.
Lemma HSubset_union_backward' : forall (G G': ctx) (H: hvars), Basics.impl (HVars.Subset hvarsᴳ(G ᴳ+ G') H) (HVars.Subset hvarsᴳ(G) H /\ HVars.Subset hvarsᴳ(G') H).
Proof.
  exact HSubset_union_backward.
Qed.
Hint Rewrite HSubset_union_backward' : propagate_down.

Lemma HSubset_stimes_backward : forall (m : mode) (G : ctx) (H: hvars), HVars.Subset hvarsᴳ(m ᴳ· G) H -> HVars.Subset hvarsᴳ(G) H.
Proof.
  unfold HVars.Subset in *. intros *. intros Hyp h Hin. specialize (Hyp h). apply Hyp, HIn_stimes_iff. assumption.
Qed.
Lemma HSubset_stimes_backward' : forall (m : mode) (G : ctx) (H: hvars), Basics.impl (HVars.Subset hvarsᴳ(m ᴳ· G) H) (HVars.Subset hvarsᴳ(G) H).
Proof.
  exact HSubset_stimes_backward.
Qed.
Hint Rewrite HSubset_stimes_backward' : propagate_down.

Lemma hvars_minus_eq : forall (D : ctx), hvarsᴳ( (ᴳ- D)) = hvarsᴳ( D).
Proof.
  intros D. apply HVars.eq_leibniz. unfold HVars.eq. intros h. rewrite! hvars_spec. split.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus in Hin. rewrite In_map_iff in Hin. rewrite <- In_iff_exists_Some. assumption.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus. rewrite <- In_iff_exists_Some. rewrite In_map_iff. assumption.
Qed.

Lemma hvars_hminus_inv_eq : forall (D : ctx), hvarsᴳ( (ᴳ-⁻¹ D)) = hvarsᴳ( D).
Proof.
  intros D. apply HVars.eq_leibniz. unfold HVars.eq. intros h. rewrite! hvars_spec. split.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus_inv in Hin. rewrite In_map_iff in Hin. rewrite <- In_iff_exists_Some. assumption.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus_inv. rewrite <- In_iff_exists_Some. rewrite In_map_iff. assumption.
Qed.

Lemma hvars_C_wk_hvars_G : forall (C : ectxs) (D : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), HVars.Subset hvarsᴳ(D) hvars©(C).
Proof.
  intros * TyC. induction TyC.
  { cbn. unfold hvars_ctx, ctx_empty.
    rewrite dom_empty_eq_nil. reflexivity. }
  all:
      try (cbn; unfold HVars.Subset; apply HSubset_union_backward in IHTyC; destruct IHTyC as (IHTyC1 & IHTyC2);  try apply HSubset_stimes_backward in IHTyC1; unfold HVars.Subset in IHTyC1 ; intros h Hin; specialize (IHTyC1 h Hin); apply HVarsFacts.union_iff; right; assumption);
      try (cbn; unfold HVars.Subset; apply HSubset_union_backward in IHTyC; destruct IHTyC as (IHTyC1 & IHTyC2); try apply HSubset_stimes_backward in IHTyC2; unfold HVars.Subset in IHTyC2; intros h Hin; specialize (IHTyC2 h Hin); apply HVarsFacts.union_iff; right; assumption);
      try (cbn; unfold HVars.Subset in * ; intros h Hin; specialize (IHTyC h Hin); apply HVarsFacts.union_iff; right; assumption).
  simpl. unfold HVars.Subset in *. intros h Hin. apply HVarsFacts.union_iff. apply HIn_union_iff in Hin. destruct Hin as [inD1|inD3].
  - right. apply HIn_stimes_iff in inD1. assert (HVars.In h hvarsᴳ( D1 ᴳ+ D2)).
    { apply HIn_union_iff. left. assumption. }
    specialize (IHTyC h H0). assumption.
  - left. rewrite hvars_minus_eq. assumption.
Qed.

Lemma HDisjoint_to_Disjoint : forall (D D' : ctx), DestOnly D -> hvarsᴳ(D) ## hvarsᴳ(D') -> D # D'.
Proof.
  intros * DestOnlyD hvarsDisjoint.
  unfold Disjoint. intros n inD inD'. unfold In, Fun.In in *. destruct n.
  - unfold DestOnly, IsDest in DestOnlyD. destruct inD as (binding & inD); specialize (DestOnlyD (name_Var x) binding inD); cbn in DestOnlyD. assumption.
  - rewrite <- hvars_spec in inD, inD'. unfold HDisjoint in hvarsDisjoint.
    assert (HVars.In h (HVars.inter hvarsᴳ(D) hvarsᴳ(D'))).
      { apply HVars.inter_spec. split; assumption. }
    unfold HVars.Empty in hvarsDisjoint. specialize (hvarsDisjoint h). congruence.
Qed.

Lemma Disjoint_to_HDisjoint : forall (D D' : ctx), D # D' -> hvarsᴳ(D) ## hvarsᴳ(D').
Proof.
  intros * DisjointDDp.
  unfold HDisjoint. unfold HVars.Empty. intros h HinInter.
  rewrite HVarsFacts.inter_iff in HinInter. destruct HinInter as (inD & inD').
  rewrite hvars_spec in inD, inD'. rewrite <- In_iff_exists_Some in inD, inD'.
  unfold Disjoint in DisjointDDp. specialize (DisjointDDp (name_DH h) inD inD'). assumption.
Qed.

Lemma not_lt_le : forall (x y : nat),
  ~ x < y -> y <= x.
Proof.
  sfirstorder.
Qed.

Lemma HSubset_impl_lt_max : forall (H H' : hvars), HVars.Subset H H' -> maxᴴ(H) <= maxᴴ(H').
Proof.
  intros *. unfold HVars.Subset. intros Hyp. unfold hvar_max. destruct (HVars.max_elt H) as [h|] eqn:eMax.
    - apply HVars.max_elt_spec1 in eMax. specialize (Hyp h eMax).
      destruct (HVars.max_elt H') as [h'|] eqn:eMax'.
      + assert (~(h'<h)). { apply HVars.max_elt_spec2 with (s := H'). all:assumption. }
        apply not_lt_le; assumption.
      + apply HVars.max_elt_spec3 in eMax'. unfold HVars.Empty in eMax'. specialize (eMax' h). congruence.
    - apply Nat.le_0_l.
Qed.

Lemma hvars_empty_is_hempty : hvarsᴳ(ᴳ{}) = HVars.empty.
Proof.
  unfold hvars_ctx, hvars_dom, ctx_empty. rewrite dom_empty_eq_nil. reflexivity.
Qed.

Lemma HDisjoint_hempty_r : forall (H : hvars), H ## HVars.empty.
Proof.
  intros H. unfold HDisjoint. unfold HVars.Empty. intros h Hin. rewrite HVars.inter_spec in Hin. destruct Hin. inversion H1.
Qed.
Lemma HDisjoint_hempty_l : forall (H : hvars), HVars.empty ## H.
Proof.
  intros H. unfold HDisjoint. unfold HVars.Empty. intros h Hin. rewrite HVars.inter_spec in Hin. destruct Hin. inversion H0.
Qed.

Lemma ModeSubtype_refl : forall (m : mode), ModeSubtype m m.
Proof.
  intros m. sauto lq: on.
Qed.

(* Lemma CompatibleDestSingleton : forall (h : hvar) (m : mode) (T : type) (n : mode), ctx_CompatibleDH (ᴳ{+ h : m ⌊ T ⌋ n}) h (₊ m ⌊ T ⌋ n).
Proof.
  intros *.
  unfold ctx_CompatibleDH. split.
  + unfold ctx_singleton. apply In_singleton_iff. reflexivity.
  + unfold ctx_singleton. intros nam binding Hin. rewrite singleton_MapsTo_iff in Hin. pose proof Hin as Hin'. apply eq_sigT_fst in Hin; subst. apply inj_pair2_eq_dec in Hin'; subst.
    simpl. destruct (HVarsFacts.eq_dec h h).
    - repeat split. apply ModeSubtype_refl.
    - congruence.
    - exact (name_eq_dec).
Qed.

Lemma IncompatibleVarDestOnlyD : forall (D : ctx) (x : var) (m : mode) (T : type), DestOnly D -> ~CompatibleVar D x (ₓ m ‗ T).
Proof.
  intros * DestOnlyD CompatibleVar. destruct CompatibleVar as (inD & CompatibleVar).
  unfold DestOnly, IsDest in DestOnlyD. unfold CompatibleVar in CompatibleVar. destruct (dom(D)) eqn:eDomD.
  - rewrite <- dom_spec in inD. rewrite eDomD in inD. inversion inD.
  - assert (List.In n (dom D)). { rewrite eDomD. apply in_eq. }
    rewrite dom_spec in H. destruct H as (binding & mapstoD). destruct n. specialize (DestOnlyD (ˣ x0) binding mapstoD). assumption. apply In_iff_exists_Some in inD; destruct inD as (binding' & mapstoD'). specialize (DestOnlyD (ˣ x) binding' mapstoD'). simpl in DestOnlyD. assumption.
Qed. *)

Lemma hminus_singleton : forall (h : hvar) (T : type) (n : mode), (ᴳ- ᴳ{+ h : ¹ν ⌊ T ⌋ n}) = ᴳ{- h : T ‗ n }.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold hminus, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₊ ¹ν ⌊ T ⌋ n). split; tauto. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ ¹ν ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma hminus_inv_singleton : forall (h : hvar) (T : type) (n : mode), (ᴳ-⁻¹ ᴳ{- h : T ‗ n}) = ᴳ{+ h : ¹ν ⌊ T ⌋ n }.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold hminus_inv, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₋ T ‗ n). split; tauto. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ ¹ν ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma stimes_singleton_var : forall (x : var) (m : mode) (T : type) (m' : mode), m' ᴳ· ᴳ{ x : m ‗ T} = ᴳ{ x : (m · m') ‗ T}.
Proof.
  intros *.
  apply ext_eq.
  intros n. unfold stimes, ctx_singleton.
  destruct (name_eq_dec n (ˣ x)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (ₓ m ‗ T). split. tauto. unfold stimes_var. rewrite mode_times_commutative. reflexivity. }
  { assert (@singleton name binding_type_of (ˣ x) name_eq_dec (ₓ m ‗ T) n = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ˣ x) name_eq_dec (ₓ (m · m') ‗ T) n = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma stimes_singleton_dest : forall (h : hvar) (m n : mode) (T : type) (m': mode), m' ᴳ· ᴳ{+ h : m ⌊ T ⌋ n} = ᴳ{+ h : (m · m') ⌊ T ⌋ n}.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold stimes, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₊ m ⌊ T ⌋ n). split. tauto. unfold stimes_dh. rewrite mode_times_commutative. reflexivity. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ m ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ (m · m') ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.
Lemma stimes_singleton_hole : forall (h : hvar) (T : type) (n : mode) (m': mode), m' ᴳ· ᴳ{- h : T ‗ n} = ᴳ{- h : T ‗ (n · m') }.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold stimes, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₋ T ‗ n). split. tauto. unfold stimes_dh. rewrite mode_times_commutative. reflexivity. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ (n · m')) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma hvars_singleton_dest : forall (h : hvar) (m n : mode) (T : type), hvarsᴳ( ᴳ{+ h : m ⌊ T ⌋ n} ) = ᴴ{ h }.
Proof.
  intros *.
  unfold hvars_ctx, hvars_dom, hvars_, ctx_singleton.
  rewrite dom_singleton_eq. reflexivity.
Qed.

Lemma hvars_singleton_hole : forall (h : hvar) (T : type) (n : mode), hvarsᴳ( ᴳ{- h : T ‗ n} ) = ᴴ{ h }.
Proof.
  intros *.
  unfold hvars_ctx, hvars_dom, hvars_, ctx_singleton.
  rewrite dom_singleton_eq. reflexivity.
Qed.

Lemma DestOnly_singleton_dest : forall (h : hvar) (m n : mode) (T : type), DestOnly ᴳ{+ h : m ⌊ T ⌋ n}.
Proof.
  unfold DestOnly, ctx_singleton, IsDest. intros * mapsto.
  apply singleton_MapsTo_iff in mapsto. pose proof mapsto as mapsto'. apply eq_sigT_fst in mapsto. destruct x; try congruence. inversion mapsto. rewrite <- H0 in *. apply inj_pair2_eq_dec in mapsto'. rewrite <- mapsto' in *. trivial. exact name_eq_dec.
Qed.

Lemma VarOnly_singleton_var : forall (x : var) (m : mode) (T : type), VarOnly ᴳ{ x : m ‗ T}.
Proof.
  unfold VarOnly, ctx_singleton, IsVar. intros * mapsto.
  apply singleton_MapsTo_iff in mapsto. pose proof mapsto as mapsto'. apply eq_sigT_fst in mapsto. destruct x0; try congruence. inversion mapsto. rewrite <- H0 in *. apply inj_pair2_eq_dec in mapsto'. trivial. exact name_eq_dec.
Qed.

(* TODO: revisit if stuff breaks *)
Lemma dom_nil_is_empty : forall (G : ctx), dom G = nil -> G = ᴳ{}.
Proof.
  apply Finitely.dom_nil_is_empty.
Qed.

Lemma HSubset_preserves_HDisjoint : forall (H1 H2 H3 : hvars), HVars.Subset H1 H2 -> HDisjoint H2 H3 -> HDisjoint H1 H3.
Proof.
  intros * H1H2 H2H3. unfold HDisjoint, HVars.Subset, HVars.Empty in *.
  intros h. specialize (H1H2 h). specialize (H2H3 h).
  intros HinInter. apply HVars.inter_spec in HinInter. destruct HinInter as [H1h H3h]. specialize (H1H2 H1h). destruct H2H3. apply HVars.inter_spec. split; assumption.
Qed.

Lemma In_union_forward_l : forall (D1 D2 : ctx) (n : name), In n D1 -> In n (D1 ᴳ+ D2).
Proof.
  intros * inD1. destruct (In_dec n D2); unfold union.
  - rewrite In_iff_exists_Some in *. destruct inD1 as (binding1 & inD1); destruct H as (binding2 & inD2); rewrite merge_with_Some_Some_eq with (y1 := binding1) (y2 := binding2). exists ((match n as n0 return (binding_type_of n0 -> binding_type_of n0 -> binding_type_of n0) with
| ˣ _ => union_var
| ʰ _ => union_dh
end binding1 binding2)). reflexivity. split; assumption.
  - rewrite nIn_iff_nMapsTo in H. rewrite In_iff_exists_Some in *. destruct inD1 as (binding1 & inD1). rewrite merge_with_Some_None_eq with (y1 := binding1). exists binding1. reflexivity. split; assumption.
Qed.

Lemma In_union_forward_r : forall (D1 D2 : ctx) (n : name), In n D2 -> In n (D1 ᴳ+ D2).
Proof.
  intros * inD2. destruct (In_dec n D1); unfold union.
  - rewrite In_iff_exists_Some in *. destruct inD2 as (binding2 & inD2); destruct H as (binding1 & inD1); rewrite merge_with_Some_Some_eq with (y1 := binding1) (y2 := binding2). exists ((match n as n0 return (binding_type_of n0 -> binding_type_of n0 -> binding_type_of n0) with
| ˣ _ => union_var
| ʰ _ => union_dh
end binding1 binding2)). reflexivity. split; assumption.
  - rewrite nIn_iff_nMapsTo in H. rewrite In_iff_exists_Some in *. destruct inD2 as (binding2 & inD2). rewrite merge_with_None_Some_eq with (y2 := binding2). exists binding2. reflexivity. split; assumption.
Qed.

Lemma In_stimes_backward : forall (D : ctx) (m : mode) (n : name), In n (m ᴳ· D) -> In n D.
Proof.
  intros * inStimes. unfold stimes in inStimes. destruct (In_dec n D).
  - assumption.
  - unfold stimes in H. apply In_map_iff in inStimes. congruence.
Qed.

Lemma nIn_iff_Disjoint_singleton : forall (G : ctx) (n : name) (binding : binding_type_of n), ~In n G <-> G # (ctx_singleton n binding).
Proof.
  intros *.
  split.
  - intros NotIn. unfold Disjoint. intros n'. intros InG. destruct (name_eq_dec n n'). rewrite e in *. congruence. intros inSing. unfold ctx_singleton in inSing. rewrite <- singleton_nMapsTo_iff with (x := n) (discr := name_eq_dec) (v := binding) in n0. rewrite In_iff_exists_Some in inSing. destruct inSing. congruence.
  - intros DisjointGSing. unfold Disjoint in DisjointGSing. intros InG.
    assert (In n (ctx_singleton n binding)). { apply In_singleton_iff; reflexivity. }
    specialize (DisjointGSing n InG H). assumption.
Qed.

Lemma nIn_union_forward: forall (G1 G2 : ctx) (n : name), ~In n G1 -> ~In n G2 -> ~In n (G1 ᴳ+ G2).
Proof.
  intros * NotIn1 NotIn2 InUnion. unfold union in InUnion. apply In_merge_iff in InUnion. destruct InUnion. all:congruence.
Qed.

Lemma DestOnly_wk_NoVar : forall (D : ctx), DestOnly D -> NoVar D.
Proof.
  intros * H. unfold DestOnly in H. unfold NoVar. intros nam b mapstoD. specialize (H nam b mapstoD). destruct nam. { inversion H. } { intros contra. inversion contra. }
Qed.

Lemma DisposableOnly_wk_VarOnly : forall (P : ctx), DisposableOnly P -> VarOnly P.
Proof.
  intros * H. unfold DisposableOnly in H. unfold VarOnly. intros nam b mapstoP. specialize (H nam b mapstoP). unfold IsDisposable in H. destruct nam. 2:{ contradiction. } unfold IsVar. tauto.
Qed.

Lemma nDisposable_in_DestOnly: forall (P D : ctx), DisposableOnly P -> DestOnly (P ᴳ+ D) -> (P ᴳ+ D) = D.
Proof.
  intros * DisposP DestOnlyPuD.
  assert (P = ᴳ{}) as Pempty.
  { apply ext_eq. intros n. destruct (In_dec n P) as [[y h_inP]|h_ninP].
    - unfold DisposableOnly in DisposP. specialize (DisposP n y h_inP). unfold IsDisposable in DisposP.
      unfold DestOnly in DestOnlyPuD. assert (In n P) as inP. { exists y. assumption. } assert (In n (P ᴳ+ D)) as InPuD. { apply In_union_forward_l. assumption. } destruct InPuD as (y' & mapstoPuD). specialize (DestOnlyPuD n y' mapstoPuD). unfold IsDest in DestOnlyPuD. destruct n; contradiction.
    - apply nIn_iff_nMapsTo. assumption.
  }
  rewrite Pempty. symmetry. apply union_empty_l_eq.
Qed.

Lemma VarOnly_union_DestOnly_is_Disjoint : forall (P1 G2 : ctx), VarOnly P1 -> NoVar G2 -> P1 # G2.
Proof.
  intros * VarOnlyP NoVarG. unfold Disjoint. intros nam inP1 inG2. unfold VarOnly, NoVar, Fun.In, IsVar in *. destruct inP1; specialize (VarOnlyP nam x H). destruct inG2; specialize (NoVarG nam x0 H0). destruct nam; simpl in *; congruence.
Qed.

Lemma DestOnly_nMapsTo_var : forall (D : ctx) (x : var), DestOnly D -> D (ˣ x) = None.
Proof.
  intros * DestOnlyD. unfold DestOnly in DestOnlyD. specialize (DestOnlyD (ˣ x)).
  destruct (List.In_dec name_eq_dec (ˣ x) (dom D)).
    2:{ rewrite dom_spec in n. rewrite nIn_iff_nMapsTo in n. assumption. }
    remember (dom D) as l in i. assert (ListSubset l (dom D)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    { inversion i. }
    { apply ListSubset_cons_iff in H. destruct H as [H1 H2]. apply List.in_inv in i. destruct i.
      { rewrite H in *. rewrite dom_spec, In_iff_exists_Some in H1. destruct H1 as (binding & mapsto). specialize (DestOnlyD binding mapsto). inversion DestOnlyD. }
      { specialize (IHl H H2). assumption. }
    }
Qed.

Lemma VarOnly_nMapsTo_hd : forall (P : ctx) (h : hvar), VarOnly P -> P (ʰ h) = None.
Proof.
  intros * VarOnlyP. unfold VarOnly in VarOnlyP. specialize (VarOnlyP (ʰ h)).
  destruct (List.In_dec name_eq_dec (ʰ h) (dom P)).
    2:{ rewrite dom_spec in n. rewrite nIn_iff_nMapsTo in n. assumption. }
    remember (dom P) as l in i. assert (ListSubset l (dom P)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    { inversion i. }
    { apply ListSubset_cons_iff in H. destruct H as [H1 H2]. apply List.in_inv in i. destruct i.
      { rewrite H in *. rewrite dom_spec, In_iff_exists_Some in H1. destruct H1 as (binding & mapsto). specialize (VarOnlyP binding mapsto). inversion VarOnlyP. }
      { specialize (IHl H H2). assumption. }
    }
Qed.

Lemma DestOnly_union_singleton_x_at_x : forall (D : ctx) (x : var) (m : mode) (T : type), DestOnly D -> (D ᴳ+ ᴳ{ x : m ‗ T}) (ˣ x) = Some (ₓ m ‗ T).
Proof.
  intros * DestOnlyD.
  unfold union. apply merge_with_None_Some_eq with (f := D). split.
  + apply DestOnly_nMapsTo_var. assumption.
  + apply singleton_MapsTo_at_elt.
Qed.

Lemma ModeSubtype_linnu_eq : forall (m : mode), ModeSubtype (¹ν) m <-> m = ¹ν.
Proof.
  intros m. split.
  - intros H. inversion H. inversion H2. inversion H4. reflexivity.
  - intros H. rewrite H. apply ModeSubtype_refl.
Qed.

Ltac hauto_ctx :=
  hauto
    depth: 3
    use:
        ValidOnly_cshift_iff,
        DestOnly_cshift_iff,
        LinNuOnly_cshift_iff,
        LinOnly_cshift_iff,
        FinAgeOnly_cshift_iff,
        cshift_by_Disjoint_eq,
        cshift_distrib_on_union,
        cshift_distrib_on_stimes,
        cshift_by_max_impl_HDisjoint,
        total_cshift_eq,
        cshift_distrib_on_hminus,
        cshift_distrib_on_hminus_inv,
        (* TyR_val_cshift,
        val_A_cshift, *)
        union_commutative,
        (* union_commutative', *)
        ValidOnly_union_backward,
        (* ValidOnly_union_backward', *)
        ValidOnly_union_forward,
        (* ValidOnly_union_forward', *)
        ValidOnly_singleton_iff,
        ValidOnly_stimes_backward,
        (* ValidOnly_stimes_backward', *)
        IsValid_times_iff,
        ValidOnly_stimes_forward,
        (* ValidOnly_stimes_forward', *)
        DestOnly_union_iff,
        DestOnly_stimes_iff,
        nIsLin_mode_plus,
        IsLinNu_wk_IsLin,
        (* IsLinNu_wk_IsLin', *)
        IsLin_wk_IsValid,
        (* IsLin_wk_IsValid', *)
        IsLinNu_mode_plus,
        LinOnly_union_iff,
        LinNuOnly_wk_LinOnly,
        LinOnly_wk_ValidOnly,
        LinNuOnly_union_iff,
        (* n_plus_n0_eq_0_implies_n0_eq_0, *)
        LinNuOnly_stimes_forward,
        (* LinNuOnly_stimes_forward', *)
        LinNuOnly_stimes_backward,
        (* LinNuOnly_stimes_backward', *)
        FinAgeOnly_union_backward,
        (* FinAgeOnly_union_backward', *)
        FinAgeOnly_union_forward,
        (* FinAgeOnly_union_forward', *)
        LinOnly_stimes_backward,
        (* LinOnly_stimes_backward', *)
        LinOnly_stimes_forward,
        (* LinOnly_stimes_forward', *)
        FinAgeOnly_stimes_backward,
        (* FinAgeOnly_stimes_backward', *)
        FinAgeOnly_stimes_forward,
        (* FinAgeOnly_stimes_forward', *)
        Disjoint_stimes_l_iff,
        Disjoint_stimes_r_iff,
        Disjoint_hminus_l_iff,
        Disjoint_hminus_inv_l_iff,
        Disjoint_hminus_r_iff,
        Disjoint_hminus_inv_r_iff,
        Disjoint_union_l_iff,
        Disjoint_union_r_iff,
        Disjoint_commutative,
        LinOnly_empty,
        FinAgeOnly_empty,
        DestOnly_empty,
        Disjoint_empty_l,
        Disjoint_empty_r,
        DisposableOnly_empty,
        stimes_empty_eq,
        hminus_empty_eq,
        hminus_inv_empty_eq,
        union_empty_r_eq,
        union_empty_l_eq,
        DestOnly_Disjoint_singleton_var,
        mode_plus_commutative,
        mode_plus_associative,
        union_associative,
        mode_times_commutative,
        mode_times_associative,
        mode_times_linnu_r_eq,
        mode_times_linnu_l_eq,
        stimes_is_action,
        mode_times_distrib_plus,
        stimes_distrib_union,
        hminus_distrib_union,
        hminus_inv_distrib_union,
        stimes_linnu_eq,
        hunion_hempty_l_eq,
        hunion_hempty_r_eq,
        (* ListSubset_refl,
        ListSubset_cons_iff, *)
        hvars_spec,
        HIn_union_iff,
        HIn_stimes_iff,
        HSubset_union_backward,
        (* HSubset_union_backward', *)
        HSubset_stimes_backward,
        (* HSubset_stimes_backward', *)
        hvars_minus_eq,
        hvars_hminus_inv_eq,
        hvars_C_wk_hvars_G,
        HDisjoint_to_Disjoint,
        Disjoint_to_HDisjoint,
        (* not_lt_le, *)
        HSubset_impl_lt_max,
        hvars_empty_is_hempty,
        HDisjoint_hempty_r,
        HDisjoint_hempty_l,
        ModeSubtype_refl,
        hminus_singleton,
        hminus_inv_singleton,
        stimes_singleton_var,
        stimes_singleton_dest,
        stimes_singleton_hole,
        hvars_singleton_dest,
        hvars_singleton_hole,
        DestOnly_singleton_dest,
        VarOnly_singleton_var,
        dom_nil_is_empty,
        HSubset_preserves_HDisjoint,
        In_union_forward_l,
        In_union_forward_r,
        In_stimes_backward,
        nIn_iff_Disjoint_singleton,
        nIn_union_forward,
        DestOnly_wk_NoVar,
        DisposableOnly_wk_VarOnly,
        VarOnly_union_DestOnly_is_Disjoint,
        nDisposable_in_DestOnly,
        DestOnly_nMapsTo_var,
        DestOnly_union_singleton_x_at_x,
        ModeSubtype_linnu_eq,
        (IsLinProof (Fin 0)),
        (IsLinProof (Fin 1)),
        (IsFinAgeProof Lin 0),
        (IsFinAgeProof Lin 1),
        (IsValidProof (Lin, (Fin 0))),
        (IsValidProof (Lin, (Fin 1)))
    .

Ltac term_Val_no_dispose D :=
  assert (DisposableOnly ᴳ{}) as DisposEmpty by (exact DisposableOnly_empty); rewrite union_empty_l_eq with (G := D); apply Ty_term_Val with (P := ᴳ{}); trivial.

(* Silly stuff to avoid matching hypotheses many times *)
Definition Blocked (P : Prop) : Prop := P.

Ltac saturate :=
  (* This is an annoying machinery to rewrite in each hypothesis once. May be slow 🙁 *)
  repeat match goal with
    | H : ?P |- _ =>
        lazymatch P with
        | Blocked _ => fail
        | _ =>
            (* Just rewrite once because otherwise would loop. *)
            (rewrite_strat outermost (hints saturate) in H);
            ( let P' := type of H in
              change P' with (Blocked P') in H)
        end
    end;
  repeat match goal with
    | H : context[Blocked ?P] |- _ =>
        change (Blocked P) with P in H
    end.

Ltac crush :=
  (* occasionally, we have an early solve. Since `propagate` actually
     loses information, better to try for it. *)
  let saturate' := (saturate; (solve[eauto] || autorewrite with propagate_down in *)) in
  let finisher := solve [ hauto lq: on | rewrite_db suffices; hauto lq:on ] in
  let workhorse :=
    solve
      [ trivial
      (* Saturate is slowish. So it's worth trying without it first. *)
      | autorewrite with propagate_down in *; finisher
      (* Saturate a second time because it isn't unlikely to uncover
         something new after simplification. *)
      | saturate'; solve [ finisher | saturate'; finisher ]
      (* ⬇️ should really be the last case because it can be quite slow. *)
      | hauto_ctx ]
  in
  solve
    [ trivial
    | autorewrite with canonalize in *; workhorse ].

Lemma TyR_val_NoVar : forall (G : ctx) (v : val) (T : type) (TyR: G ⫦ v : T), NoVar G.
Proof.
  intros * TyR. induction TyR; unfold NoVar; intros nam b mapstoG contra.
  - unfold ctx_singleton in mapstoG. rewrite singleton_MapsTo_iff in mapstoG. apply eq_sigT_fst in mapstoG; subst. inversion contra.
  - unfold ctx_singleton in mapstoG. rewrite singleton_MapsTo_iff in mapstoG. apply eq_sigT_fst in mapstoG; subst. inversion contra.
  - unfold ctx_empty in mapstoG. simpl in mapstoG. congruence.
  - unfold DestOnly in H. unfold NoVar in contra. specialize (H nam b mapstoG). destruct nam. { inversion H. } { inversion contra. }
  - unfold NoVar in IHTyR. specialize (IHTyR nam b mapstoG). congruence.
  - unfold NoVar in IHTyR. specialize (IHTyR nam b mapstoG). congruence.
  - assert (In nam (G1 ᴳ+ G2)). { apply In_iff_exists_Some; exists b; tauto. }
    apply In_merge_iff in H. destruct H.
    + destruct H. unfold NoVar in IHTyR1. specialize (IHTyR1 nam x H). unfold IsVar in IHTyR1. destruct nam. specialize (IHTyR1 I); assumption. inversion contra.
    + destruct H. unfold NoVar in IHTyR2. specialize (IHTyR2 nam x H). unfold IsVar in IHTyR2. destruct nam. specialize (IHTyR2 I); assumption. inversion contra.
  - apply map_MapsTo_iff in mapstoG. destruct mapstoG. destruct H.
    unfold NoVar in IHTyR. specialize (IHTyR nam x H). unfold IsVar in IHTyR. destruct nam. specialize (IHTyR I); assumption. inversion contra.
  - assert (In nam (D1 ᴳ+ D2)). { apply In_iff_exists_Some; exists b; tauto. }
    apply In_merge_iff in H. destruct H.
    + assert (In nam (¹↑ ᴳ· D1 ᴳ+ D3)). { apply In_iff_exists_Some. apply In_merge_iff. left. apply In_map_iff. assumption. }
      destruct H0. unfold NoVar in IHTyR1. specialize (IHTyR1 nam x H0). unfold IsVar in IHTyR1. destruct nam. specialize (IHTyR1 I); assumption. inversion contra.
    + assert (In nam (D2 ᴳ+ (ᴳ- D3))). { apply In_iff_exists_Some. apply In_merge_iff. left. assumption. }
      destruct H0. unfold NoVar in IHTyR2. specialize (IHTyR2 nam x H0). unfold IsVar in IHTyR2. destruct nam. specialize (IHTyR2 I); assumption. inversion contra.
Qed.

Lemma TyR_val_H_DestOnly_contra : forall (D : ctx) (h : hvar) (T : type), (D ⫦ ᵛ- h : T) -> DestOnly D -> False.
Proof.
  intros D h T TyRv DestOnlyD. inversion TyRv; subst.
  specialize (DestOnlyD (ʰ h)). unfold DestOnly, ctx_singleton in DestOnlyD. specialize (DestOnlyD (₋ T ‗ ¹ν)). rewrite singleton_MapsTo_iff in DestOnlyD. sfirstorder.
Qed.

Lemma Ty_ectxs_DestOnly : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), DestOnly D.
Proof.
  intros * TyC. induction TyC.
  all: crush.
Qed.

Lemma Ty_ectxs_HDisjoint_to_Disjoint : forall (C : ectxs) (D D' : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), hvars©(C) ## hvarsᴳ(D') -> D # D'.
Proof.
  intros * TyC hvarsDisjoint. pose proof TyC as TyC'.
  apply hvars_C_wk_hvars_G in TyC.
  assert (hvarsᴳ(D) ## hvarsᴳ( D')). { apply HSubset_preserves_HDisjoint with (H2 := hvars©(C)); assumption. }
  apply HDisjoint_to_Disjoint in H. assumption. apply Ty_ectxs_DestOnly in TyC'. assumption.
Qed.

Lemma Ty_ectxs_LinFinOnly : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), LinOnly D /\ FinAgeOnly D.
Proof.
  intros D C T U0 H. induction H.
  - split. apply LinOnly_empty. apply FinAgeOnly_empty.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - assert (LinOnly (¹↑ ᴳ· D1)).
      { hauto use: LinOnly_union_iff, LinOnly_stimes_forward, (IsLinProof (Fin 1)). }
    assert (FinAgeOnly (¹↑ ᴳ· D1)).
      { hauto use: FinAgeOnly_union_backward, FinAgeOnly_stimes_forward, (IsFinAgeProof Lin 1). }
    assert ((D1 ᴳ+ D2) # (ᴳ- D3)).
      { apply (Ty_ectxs_HDisjoint_to_Disjoint C (D1 ᴳ+ D2) (ᴳ- D3) (U ⧔ T') U0); tauto. }
    assert ((¹↑ ᴳ· D1) # D3).
      { sblast use: Disjoint_union_l_iff, Disjoint_hminus_r_iff, Disjoint_stimes_l_iff. }
    rewrite LinOnly_union_iff. repeat split. tauto. tauto. tauto. apply FinAgeOnly_union_forward. repeat split. all:tauto.
Qed.

Lemma Empty_dec : forall (G : ctx), { G = ᴳ{}} + { exists n binding, G n = Some binding }.
Proof.
  intros *. destruct (dom(G)) eqn:eDomG.
  - left. apply ext_eq. apply dom_nil_is_empty in eDomG. rewrite eDomG. intros x. trivial.
  - right. exists n. rewrite <- In_iff_exists_Some. apply dom_spec. rewrite eDomG. apply List.in_eq.
Qed.

Lemma LinOnly_stimes_dec : forall (D1: ctx) (m' : mode), IsValid m' -> LinOnly (m' ᴳ· D1) -> { IsLin m' } + { IsUr m' /\ D1 = ᴳ{} }.
Proof.
  intros * Validmp LinOnlyD.
  destruct (IsLin_dec m'). { left. assumption. }
  right. assert (IsUr m'). { destruct m'. destruct p. destruct m. specialize (n (IsLinProof a)). contradiction. constructor. inversion Validmp. }
  split. assumption.
  apply ext_eq. rename n into NotLin. intros n.
    assert (LinOnly (m' ᴳ· D1)). { crush. } unfold LinOnly in H0. destruct (Empty_dec D1).
    - rewrite e. cbn. reflexivity.
    - destruct e as (n' & mapstoD1). exfalso.
      unfold stimes in H0. specialize (H0 n').
      pose proof mapstoD1 as inD1. rewrite <- In_iff_exists_Some in inD1. apply In_map_iff with (m := (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
| ˣ _ => stimes_var m'
| ʰ _ => stimes_dh m'
end)) in inD1. rewrite In_iff_exists_Some in inD1. destruct inD1 as (binding & mapstoMap). specialize (H0 binding mapstoMap).
      destruct n'; unfold map, Fun.map in mapstoMap; simpl in mapstoMap; destruct mapstoD1 as (binding' & mapstoD1); rewrite mapstoD1 in mapstoMap; inversion mapstoMap.
      + inversion H0. inversion H2. destruct binding, binding'; unfold stimes_var, mode_times, mul_times in *; destruct m, m', m0; simpl in *; try congruence; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; trivial; try congruence. inversion H.
      + inversion H0. inversion H2. destruct binding, binding'; unfold stimes_dh, mode_times, mul_times in *; try destruct m; try destruct m'; try destruct m0; try destruct n1; simpl in *; try congruence; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; trivial; try congruence. all:inversion H.
Qed.

Lemma SplitDestOnlyVarOnly : forall (P1 P2 D1 D2 : ctx),
  VarOnly P1 ->
  VarOnly P2 ->
  DestOnly D1 ->
  DestOnly D2 ->
  (P1 ᴳ+ D1 = P2 ᴳ+ D2) ->
  (P1 = P2 /\ D1 = D2).
Proof.
  intros * VarOnlyP1 VarOnlyP2 DestOnlyD1 DestOnlyD2 UnionEq.
  split.
  - apply ext_eq. intros n. assert ((P1 ᴳ+ D1) n = (P2 ᴳ+ D2) n). { rewrite UnionEq. f_equal. } destruct n.
    + unfold union, merge_with, merge, Fun.merge, Fun.on_conflict_do in H; simpl in H. destruct (P1 (ˣ x)) eqn:P1x; rewrite (DestOnly_nMapsTo_var D1 x DestOnlyD1), (DestOnly_nMapsTo_var D2 x DestOnlyD2) in H; destruct (P2 (ˣ x)); assumption.
    + rewrite (VarOnly_nMapsTo_hd P1 h VarOnlyP1), (VarOnly_nMapsTo_hd P2 h VarOnlyP2). reflexivity.
  - apply ext_eq. intros n. assert ((P1 ᴳ+ D1) n = (P2 ᴳ+ D2) n). { rewrite UnionEq. f_equal. } destruct n.
    + rewrite (DestOnly_nMapsTo_var D1 x DestOnlyD1), (DestOnly_nMapsTo_var D2 x DestOnlyD2). reflexivity.
    + unfold union, merge_with, merge, Fun.merge, Fun.on_conflict_do in H; simpl in H. destruct (D1 (ʰ h)) eqn:D1x; rewrite (VarOnly_nMapsTo_hd P1 h VarOnlyP1), (VarOnly_nMapsTo_hd P2 h VarOnlyP2) in H; destruct (D2 (ʰ h)); assumption.
Qed.

Lemma TermSubLemma :
  forall (D1 D2 : ctx) (m' : mode) (T' U' : type) (te : term) (x' : var) (v' : val),
  IsValid m' ->
  DestOnly D1 ->
  DestOnly D2 ->
  LinOnly (m' ᴳ· D1 ᴳ+ D2) ->
  (D2 ᴳ+ ᴳ{ x' : m' ‗ T'} ⊢ te : U') ->
  (D1 ⊢ ᵥ₎ v' : T') ->
  (m' ᴳ· D1 ᴳ+ D2 ⊢ te ᵗ[ x' ≔ v'] : U').
Proof.
  intros * Validmp DestOnlyD1 DestOnlyD2 LinOnlyD Tyte Tyvp.
  dependent induction Tyte; simpl.
  - rename x into Hu.
    assert (P ᴳ+ D = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
    assert (P = ᴳ{ x' : m' ‗ T'} /\ D = D2) as UnionEqSplit.
      { rewrite union_commutative with (G1 := D2) in UnionEq.
        apply SplitDestOnlyVarOnly. apply DisposableOnly_wk_VarOnly. assumption. apply VarOnly_singleton_var. all:assumption.
      } destruct UnionEqSplit; subst.
    assert (ᴳ{ x' : m' ‗ T'} (ˣ x') = Some (ₓ m' ‗ T')) as mapstoSing.
      { unfold ctx_singleton. apply (@singleton_MapsTo_at_elt name binding_type_of). }
    assert (IsUr m'). { unfold DisposableOnly in DisposP. specialize (DisposP (ˣ x') (ₓ m' ‗ T') mapstoSing). simpl in DisposP. assumption. }
    assert (D1 = ᴳ{}). { assert (LinOnly (m' ᴳ· D1)) as LinOnlymD1. { crush. } destruct (LinOnly_stimes_dec D1 m' Validmp LinOnlymD1). inversion H0. inversion i. congruence. destruct a. assumption. }
    rewrite H1 in *. rewrite stimes_empty_eq. rewrite <- union_empty_l_eq. term_Val_no_dispose D2.
  - rename x into Hu, x0 into x.
    assert (P ᴳ+ (ᴳ{ x : m ‗ T}) = D2 ᴳ+ ᴳ{ x' : m' ‗ T'}) as UnionEq.
      { hauto l: on use: ext_eq. } clear Hu.
     give_up.
Admitted.

Lemma TermSubLemma2 :
  forall (D11 D12 D2 : ctx) (m' : mode) (T1' T2' U' : type) (te : term) (x1' x2' : var) (v1' v2' : val),
  IsValid m' ->
  DestOnly D11 ->
  DestOnly D12 ->
  DestOnly D2 ->
  LinOnly (m' ᴳ· (D11 ᴳ+ D12) ᴳ+ D2) ->
  (ᴳ{ x1' : m' ‗ T1'} # ᴳ{ x2' : m' ‗ T2'}) ->
  (D2 ᴳ+ ᴳ{ x1' : m' ‗ T1'} ᴳ+ ᴳ{ x2' : m' ‗ T2'} ⊢ te : U') ->
  (D11 ⊢ ᵥ₎ v1' : T1') ->
  (D12 ⊢ ᵥ₎ v2' : T2') ->
  (m' ᴳ· (D11 ᴳ+ D12) ᴳ+ D2 ⊢ te ᵗ[ x1' ≔ v1' ] ᵗ[ x2' ≔ v2' ] : U').
Proof. Admitted.

Lemma EctxsSubLemma : forall (D1 D2 D3: ctx) (h : hvar) (C : ectxs) (m n : mode) (T U U0 : type) (v : val),
  D1 # D2 ->
  D1 # D3 ->
  hvars©(C) ## hvarsᴳ(ᴳ- D3) ->
  DestOnly D1 ->
  DestOnly D2 ->
  DestOnly D3 ->
  LinOnly D3 ->
  FinAgeOnly D3 ->
  ValidOnly D3 ->
  D1 # ᴳ{+ h : m ⌊ U ⌋ n } ->
  D2 # ᴳ{+ h : m ⌊ U ⌋ n } ->
  D3 # ᴳ{+ h : m ⌊ U ⌋ n } ->
 D1 ᴳ+ (m · n) ᴳ· D2 ᴳ+ ᴳ{+ h : m ⌊ U ⌋ n } ⊣ C : T ↣ U0 ->
 D2 ᴳ+ (ᴳ- D3) ⫦ v : U ->
 D1 ᴳ+ m ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- D3))) ⊣ C ©️[ h ≔ hvarsᴳ(ᴳ- D3) ‗ v ] : T ↣ U0.
Proof. Admitted.

(* Could be an equivalence *)
Lemma empty_union : forall G1 G2, G1 ᴳ+ G2 = ᴳ{} -> G1 = ᴳ{} /\ G2 = ᴳ{}.
Proof. Admitted.

(* Could be an equivalence *)
Lemma empty_stimes : forall G m, m ᴳ· G = ᴳ{} -> G = ᴳ{}.
Proof. Admitted.

Theorem Preservation : forall (C C' : ectxs) (t t' : term) (T : type), ⊢ C ʲ[t] : T /\
  C ʲ[t] ⟶ C' ʲ[t'] -> ⊢ C' ʲ[t'] : T.
Proof.
    intros C C' t t' T (Tyj & Redj). destruct Tyj. destruct Redj.
    - (* Sem-eterm-AppFoc1 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := T) (t := t); swap 1 3. constructor 2 with (D2 := D2) (m := m) (t' := t') (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc1 *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻ t' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) t' U T); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻ t').
      all: crush.
    - (* Sem-eterm-AppFoc2 *)
      inversion Tyt; subst.
      rename Tyt into TyApp, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
        constructor 1 with (D := D2) (T := T ⁔ m → U) (t := t'); swap 1 3. constructor 3 with (D1 := D1) (m := m) (v := v) (T := T) (U := U).
      all: crush.
    - (* Sem-eterm-AppUnfoc2 *)
      inversion Tyt; subst. rename TyRv into TyRvp, TyC into TyCc, D0 into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename Tyt into Tytp, Tyv into Tyt, T0 into T.
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyD2) in *.
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻ ᵥ₎ v' : U) as TyApp.
        { apply (Ty_term_App m D1 D2 (ᵥ₎ v) (ᵥ₎ v') U T); tauto. }
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := (ᵥ₎ v) ≻ (ᵥ₎ v')).
      all: crush.
    - (* Sem-eterm-AppRed *)
      inversion Tyt; subst.
      assert (m = m0) as Eqmm0.
        { inversion_clear Tytp; inversion_clear TyRv; tauto. }
      rewrite <- Eqmm0 in *. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tytp; subst. clear H1. rename TyRv into TyRv', D into D2.
      assert (DestOnly (P ᴳ+ D2)) as DestOnlyPuD2. { crush. }
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyPuD2) in *.
      inversion TyRv'; subst. rename H1 into DestOnlyD2.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u ᵗ[ x ≔ v] : U) as Tyusub.
      { apply (TermSubLemma D1 D2 m T U u x v). all: crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u ᵗ[ x ≔ v]).
      all: crush.
    - (* Sem-eterm-PatUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into T2.
      assert (LinOnly (D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C T2 U0); tauto. }
        constructor 1 with (D := D1) (T := ①) (t := t); swap 1 3. constructor 4 with (D2 := D2) (U := T2) (u := u). all: crush.
    - (* Sem-eterm-PatUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename U into T2.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C T2 U0); tauto. }
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ v ᵗ; u : T2) as TyPat.
        { apply (Ty_term_PatU D1 D2 (ᵥ₎ v) u T2); tauto. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := T2) (t := ᵥ₎ v ᵗ; u). all: crush.
    - (* Sem-eterm-PatURed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into T2.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst.
      constructor 1 with (D := D2) (T := T2) (t := u). all: crush.
    - (* Sem-eterm-PatSFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨁ T2)) (t := t) ; swap 1 3. constructor 5 with (D1 := D1) (D2 := D2) (m := m) (u1 := u1) (x1 := x1) (u2 := u2) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatSUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2} : U) as TyPat.
        { apply (Ty_term_PatS m D1 D2 (ᵥ₎ v) x1 u1 x2 u2 U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2}). all: crush.
    - (* Sem-eterm-PatLRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, TyRv into TyRInlv1, D into D1.
      inversion TyRInlv1; subst.
      assert (DestOnly (P ᴳ+ D1)) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyPuD1) in *.
      assert (D1 ⊢ ᵥ₎ v1 : T1) as Tyt'.
        { term_Val_no_dispose D1. }
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u1 ᵗ[ x1 ≔ v1] : U) as Tyusub.
        { apply (TermSubLemma D1 D2 m T1 U u1 x1 v1); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u1 ᵗ[ x1 ≔ v1]). all: crush.
    - (* Sem-eterm-PatRRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, TyRv into TyRInlv2, D into D1.
      inversion TyRInlv2; subst.
      assert (DestOnly (P ᴳ+ D1)) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyPuD1) in *.
      assert (D1 ⊢ ᵥ₎ v2 : T2) as Tyt'.
        { term_Val_no_dispose D1. }
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ u2 ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (TermSubLemma D1 D2 m T2 U u2 x2 v2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := u2 ᵗ[ x2 ≔ v2]). all: crush.
    - (* Sem-eterm-PatPFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (T1 ⨂ T2)) (t := t) ; swap 1 3. constructor 6 with (D1 := D1) (D2 := D2) (u := u) (x1 := x1) (x2 := x2) (U := U). all: crush.
    - (* Sem-eterm-PatPUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u : U) as TyPat.
        { apply (Ty_term_PatP m D1 D2 (ᵥ₎ v) x1 x2 u U T1 T2); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻caseᵖ m ᵗ(x1 , x2) ⟼ u). all: crush.
    - (* Sem-eterm-PatPRed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U.
      inversion Tyt; subst. rename H1 into DestOnlyD1, D into D1.
      inversion TyRv; subst. rename G1 into D11, G2 into D12.
      assert (DestOnly (P ᴳ+ (D11 ᴳ+ D12))) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P (D11 ᴳ+ D12) DisposP DestOnlyPuD1) in *.
      assert (D11 ⊢ ᵥ₎ v1 : T1) as Tyt1.
        { term_Val_no_dispose D11. crush. }
      assert (D12 ⊢ ᵥ₎ v2 : T2) as Tyt2.
        { term_Val_no_dispose D12. crush. }
      assert (LinOnly (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2 ⊢ u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2] : U) as Tyusub.
        { apply (TermSubLemma2 D11 D12 D2 m T1 T2 U u x1 x2 v1 v2); crush. }
      constructor 1 with (D := (m ᴳ· (D11 ᴳ+ D12) ᴳ+ D2)) (T := U) (t := u ᵗ[ x1 ≔ v1] ᵗ[ x2 ≔ v2]). all: crush.
    - (* Sem-eterm-PatEFoc *)
      inversion Tyt; subst.
      rename Tyt into TyPat, Tyt0 into Tyt, P1 into D1, P2 into D2, T into U, T0 into T.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      constructor 1 with (D := D1) (T := (! n ⁔ T)) (t := t) ; swap 1 3. constructor 7 with (D1 := D1) (D2 := D2) (u := u) (x := x) (U := U). all: crush.
    - (* Sem-eterm-PatEUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (m ᴳ· D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· D1 ᴳ+ D2) C U U0); tauto. }
      assert (m ᴳ· D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻caseᵉ m ᴇ n ⁔ x ⟼ u : U) as TyPat.
        { apply (Ty_term_PatE m D1 D2 (ᵥ₎ v) n x u U T); crush. }
      constructor 1 with (D := (m ᴳ· D1 ᴳ+ D2)) (T := U) (t := ᵥ₎ v ≻caseᵉ m ᴇ n ⁔ x ⟼ u). all: crush.
    - (* Sem-eterm-PatERed *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyPat, Tyt0 into Tyt, T into U, T0 into T.
      inversion Tyt; subst. rename H1 into DestOnlyD1.
      inversion TyRv; subst. rename G into D1.
      assert (DestOnly (P ᴳ+ (n ᴳ· D1))) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P (n ᴳ· D1) DisposP DestOnlyPuD1) in *.
      assert (D1 ⊢ ᵥ₎ v' : T) as Tyt'.
        { term_Val_no_dispose D1. crush. }
      assert (LinOnly (m ᴳ· (n ᴳ· D1) ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (m ᴳ· (n ᴳ· D1) ᴳ+ D2) C U U0); tauto. }
      assert ((m · n) ᴳ· D1 ᴳ+ D2 ⊢ u ᵗ[ x ≔ v'] : U) as Tyusub.
        { apply (TermSubLemma D1 D2 (m · n) T U u x v'). all: crush. }
      constructor 1 with (D := (m ᴳ· (n ᴳ· D1) ᴳ+ D2)) (T := U) (t := u ᵗ[ x ≔ v']). all: crush.
    - (* Sem-eterm-MapFoc *)
      inversion Tyt; subst. rename T0 into T.
      rename Tyt into TyMap, Tyt0 into Tyt, P1 into D1, P2 into D2.
      assert (LinOnly (D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
      constructor 1 with (D := D1) (T := U ⧔ T) (t := t); swap 1 3. constructor 8 with (D1 := D1) (D2 := D2) (t' := t') (x := x) (T := T) (T' := T') (U := U). all: crush.
    - (* Sem-eterm-MapUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, D0 into D1, ValidOnlyD into ValidOnlyD1, DestOnlyD into DestOnlyD1. clear H1.
      inversion TyCc; subst. clear DestOnlyD0. rename T0 into T.
      rewrite (nDisposable_in_DestOnly P D1 DisposP DestOnlyD1) in *.
      assert (LinOnly (D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ v ≻map x ⟼ t' : U ⧔ T') as TyMap.
        { apply (Ty_term_Map D1 D2 (ᵥ₎ v) x t' U T' T); crush. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := U ⧔ T') (t := ᵥ₎ v ≻map x ⟼ t'). all: crush.
    - (* Sem-eterm-MapRedAOpenFoc *)
      inversion Tyt; subst.
      rename P1 into D1, P2 into D2. rename Tyt into TyMap, Tyt0 into Tyt, T0 into T.
      inversion Tyt; subst. rename H2 into DestOnlyD1.
      inversion TyRv; subst. rename D1 into D11, D0 into D12, D3 into D13, DestOnlyD0 into DestOnlyD11, DestOnlyD2 into DestOnlyD12, DestOnlyD3 into DestOnlyD13, LinOnlyD3 into LinOnlyD13, ValidOnlyD3 into ValidOnlyD13, DisjointD1D2 into DisjointD11D12, DisjointD1D3 into DisjointD11D13, DisjointD2D3 into DisjointD12D13, FinAgeOnlyD3 into FinAgeOnlyD13.
      assert (DestOnly (P ᴳ+ (D11 ᴳ+ D12))) as DestOnlyPuD1. { crush. }
      rewrite (nDisposable_in_DestOnly P (D11 ᴳ+ D12) DisposP DestOnlyPuD1) in *.
      assert ((D2 ᴳ+ D11) # (D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])) as DisjointD2uD11D13. {
          {  apply Disjoint_union_l_iff. assert (HVars.Subset hvarsᴳ(D11 ᴳ+ D12 ᴳ+ D2) hvars©(C)).
              { apply hvars_C_wk_hvars_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HVars.Subset hvarsᴳ(D2) hvars©(C)).
              { apply HSubset_union_backward with (G := D11 ᴳ+ D12) (G' := D2) (H := hvars©(C)). tauto. }
              assert (maxᴴ(hvarsᴳ(D2)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D2) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D2) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { unfold HDisjoint. rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
            { assert (HVars.Subset hvarsᴳ(D11) hvars©(C)).
              { apply HSubset_union_backward in H. destruct H. apply HSubset_union_backward in H. tauto. }
              assert (maxᴴ(hvarsᴳ(D11)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D11) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D11) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
          } }
      assert ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] ⊢ ᵥ₎ v1 ᵛ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] : T) as Tyt1.
        { term_Val_no_dispose ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]). apply TyR_val_cshift; trivial. apply DestOnly_cshift_iff; apply DestOnly_union_iff; split; try apply DestOnly_stimes_iff. crush. crush. }
          assert ((¹↑ ᴳ· (D2 ᴳ+ D11)) # (D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
          { apply Disjoint_stimes_l_iff. assumption. }
      constructor 1 with (D := ¹↑ ᴳ· (D2 ᴳ+ D11 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) (T := T') (t := t' ᵗ[ x ≔ v1 ᵛ[hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] ]); swap 3 4;
        assert (D11 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] = D11) as D11Eq by ( apply cshift_by_Disjoint_eq; crush );
        assert (D12 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] = D12) as D12Eq by ( apply cshift_by_Disjoint_eq; crush );
        rewrite D11Eq.
        { assert (ValidOnly (¹↑ ᴳ· (D2 ᴳ+ D11))).
          { apply ValidOnly_stimes_forward. split.
            - rewrite (union_commutative (D11 ᴳ+ D12) D2) in ValidOnlyD.
              rewrite union_associative in ValidOnlyD.
              apply ValidOnly_union_backward in ValidOnlyD.
              tauto.
            - exact (IsValidProof (Lin, Fin 1)).
          }
          assert (ValidOnly (D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
          { apply ValidOnly_cshift_iff; tauto. }

          apply ValidOnly_union_forward; crush.
        }
        { rewrite (union_commutative D2 D11). apply DestOnly_union_iff. split.
          { crush. }
          { crush. }
        }
        { assert (¹↑ ᴳ· (D2 ᴳ+ D11) ᴳ+ D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)] = (¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2) as ctxEq.
          { rewrite <- stimes_linnu_eq.
            rewrite cshift_distrib_on_union.
            rewrite cshift_distrib_on_stimes.
            rewrite D11Eq.
            rewrite union_commutative with (G2 := ¹↑ ᴳ· D2).
            rewrite union_associative.
            rewrite stimes_distrib_union. tauto. }
          rewrite ctxEq.
          assert (ValidOnly ((¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ( hvars©( C)) + 1)])).
            { apply ValidOnly_cshift_iff. apply ValidOnly_union_forward; trivial.
             { apply ValidOnly_stimes_forward; split; crush. }
             { crush. }
            }
          assert (LinOnly (D11 ᴳ+ D12 ᴳ+ D2)) as LinOnlyD.
            { apply (Ty_ectxs_LinFinOnly (D11 ᴳ+ D12 ᴳ+ D2) C (U ⧔ T') U0); tauto. }
          assert (LinOnly ((¹ν ᴳ· (¹↑ ᴳ· D11 ᴳ+ D13) ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) ᴳ+ ¹↑ ᴳ· D2)).
            { apply LinOnly_union_iff; repeat split.
              { apply LinOnly_stimes_forward. exact (IsLinProof (Fin 0)). apply LinOnly_cshift_iff. apply LinOnly_union_iff; repeat split. apply LinOnly_stimes_forward. exact (IsLinProof (Fin 1)). crush.
              assumption. crush. }
              { apply LinOnly_stimes_forward. exact (IsLinProof (Fin 1)). crush. }
              { apply Disjoint_stimes_l_iff. rewrite cshift_distrib_on_union. apply Disjoint_union_l_iff. split. rewrite cshift_distrib_on_stimes. rewrite cshift_by_Disjoint_eq. rewrite Disjoint_stimes_l_iff, Disjoint_stimes_r_iff. crush. crush. apply Disjoint_commutative. rewrite stimes_distrib_union, Disjoint_union_l_iff in H. destruct H as (H & H'). assumption. }
            }
          apply TermSubLemma with (T' := T) (D2 := ¹↑ ᴳ· D2).
          all: crush.
        }
      rewrite <- total_cshift_eq.
      rewrite cshift_distrib_on_hminus.
      assert (LinOnly (D11 ᴳ+ D12 ᴳ+ D2)) as LinOnlyD. { apply (Ty_ectxs_LinFinOnly (D11 ᴳ+ D12 ᴳ+ D2) C (U ⧔ T') U0). tauto. }
      assert (hvars©( C) ## hvarsᴳ( ᴳ- D13 ᴳ[ hvarsᴳ( ᴳ- D13) ⩲ (maxᴴ( hvars©( C)) + 1)])) as hvarsDisjoint.
        { rewrite <- cshift_distrib_on_hminus. rewrite total_cshift_eq. apply cshift_by_max_impl_HDisjoint with (h' := maxᴴ(hvars©(C)) + 1); rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; reflexivity. }
      constructor 19 with (D1 := D2 ᴳ+ D11) (D3 := D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) (C := C) (v2 := v2 ᵛ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)]) (T' := T') (U0 := U0) (U := U) (D2 :=
      D12).
        { apply LinOnly_union_iff. rewrite <- union_associative. rewrite union_commutative. tauto. }
        {
          {  apply Disjoint_union_l_iff. assert (HVars.Subset hvarsᴳ(D11 ᴳ+ D12 ᴳ+ D2) hvars©(C)).
              { apply hvars_C_wk_hvars_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HVars.Subset hvarsᴳ(D2) hvars©(C)).
              { apply HSubset_union_backward with (G := D11 ᴳ+ D12) (G' := D2) (H := hvars©(C)). tauto. }
              assert (maxᴴ(hvarsᴳ(D2)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D2) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D2) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
            { assert (HVars.Subset hvarsᴳ(D11) hvars©(C)).
              { apply HSubset_union_backward in H0. destruct H0. apply HSubset_union_backward in H0. tauto. }
              assert (maxᴴ(hvarsᴳ(D11)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D11) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D11) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint; crush.
            }
          } } { assert (HVars.Subset hvarsᴳ(D11 ᴳ+ D12 ᴳ+ D2) hvars©(C)).
              { apply hvars_C_wk_hvars_G with (U0 := U0) (T := U ⧔ T'). tauto. } 
            { assert (HVars.Subset hvarsᴳ(D12) hvars©(C)).
              { apply HSubset_union_backward with (G := D12) (G' := D2) (H := hvars©(C)). apply HSubset_union_backward with (G := D11). rewrite union_associative. assumption. }
              assert (maxᴴ(hvarsᴳ(D12)) <= maxᴴ(hvars©(C))).
              { apply HSubset_impl_lt_max. tauto. }
              assert (hvarsᴳ(D12) ## (hvarsᴳ(D13) ᴴ⩲ (maxᴴ(hvars©(C)) + 1))).
              { apply cshift_by_max_impl_HDisjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hvarsᴳ(D12) ## hvarsᴳ( D13 ᴳ[ hvarsᴳ(ᴳ- D13) ⩲ (maxᴴ(hvars©(C)) + 1)])).
              { unfold HDisjoint. rewrite hvars_minus_eq. rewrite total_cshift_eq. tauto. }
              apply HDisjoint_to_Disjoint. crush. assumption.
            } } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite union_commutative in TyC. rewrite union_associative in TyC. tauto. }
          { rewrite <- D12Eq. rewrite <- cshift_distrib_on_hminus. rewrite <- cshift_distrib_on_union. apply TyR_val_cshift. tauto.  } { assumption. }
    - (* Sem-eterm-AOpenUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, TyRv into TyRv1. clear H2.
      inversion TyCc; subst. rename H6 into hvarsDisjoint, D0 into D.
      rewrite <- (nDisposable_in_DestOnly P D DisposP DestOnlyD) in TyRv1.
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = P ᴳ+ D) as eqD1uD3PuD.
        { unfold union, merge_with, merge. apply ext_eq. intros n. all:simpl. rewrite H0. reflexivity. }
      rewrite <- eqD1uD3PuD in *. clear H0. clear eqD1uD3PuD. clear D.
      assert (D1 ᴳ+ D2 ⊢ ᵥ₎ hvarsᴳ(ᴳ- D3) ⟨ v2 ❟ v1 ⟩ : U ⧔ T) as TyA.
        { term_Val_no_dispose (D1 ᴳ+ D2). apply Ty_ectxs_HDisjoint_to_Disjoint with (D := D1 ᴳ+ D2) (D' := (ᴳ- D3)) (C := C) (T := U ⧔ T) (U0 := U0) in hvarsDisjoint. apply TyR_val_A. all: trivial. crush.
         }
      assert (LinOnly (D1 ᴳ+ D2)) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly (D1 ᴳ+ D2) C (U ⧔ T) U0). tauto. }
      constructor 1 with (D := (D1 ᴳ+ D2)) (T := U ⧔ T) (t := ᵥ₎ hvarsᴳ(ᴳ- D3) ⟨ v2 ❟ v1 ⟩). all: crush.
(*     - (* Sem-eterm-AllocRed *)
      inversion Tyt; subst.
      assert (hvarsᴳ(ᴳ- ᴳ{+ 1 : ¹ν ⌊ U ⌋ ¹ν }) = ᴴ{ 1}) as hvarsD3Eq.
        { cbn. reflexivity. }
      assert (ᴳ{} ⊢ ᵥ₎ ᴴ{ 1} ⟨ ᵛ- 1 ❟ ᵛ+ 1 ⟩ : U ⧔ ⌊ U ⌋ ¹ν) as Tytp.
        { rewrite <- hvarsD3Eq. apply Ty_term_Val. rewrite (union_empty_l_eq ᴳ{}). apply TyR_val_A.
          - crush.
          - crush.
          - intros n b. unfold ctx_singleton. rewrite singleton_MapsTo_iff. rewrite eq_sigT_iff_eq_dep.
            intros []. cbv. tauto.
          - intros n binding. unfold ctx_singleton. rewrite singleton_MapsTo_iff. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (binding = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n binding. unfold ctx_singleton. rewrite singleton_MapsTo_iff. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (binding = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n binding. unfold ctx_singleton. rewrite singleton_MapsTo_iff. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (binding = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - crush.
          - crush.
          - crush.
          - rewrite stimes_empty_eq. rewrite <- union_empty_l_eq. constructor. crush.
          - rewrite <- union_empty_l_eq. rewrite hminus_singleton. constructor.
          - crush.
        }
      constructor 1 with (D := ᴳ{}) (T := U ⧔ ⌊ U ⌋ ¹ν) (t := ᵥ₎ ᴴ{ 1} ⟨ ᵛ- 1 ❟ ᵛ+ 1 ⟩). all: crush. *)
    - (* Sem-eterm-ToAFoc *)
      inversion Tyt; subst.
      rename Tyt into TyToA.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C (U ⧔ ①) U0). tauto. }
      constructor 1 with (D := D) (t := u) (T := U); swap 1 3. constructor 9. all: crush.
    - (* Sem-eterm-ToAUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C (U ⧔ ①) U0). tauto. }
      assert (D ⊢ to⧔ ᵥ₎ v2 : U ⧔ ①) as TyToA.
        { apply (Ty_term_ToA D (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D) (T := U ⧔ ①) (t := to⧔ ᵥ₎ v2). all: crush.
    - (* Sem-eterm-ToARed *)
      inversion Tyt; subst.
      rename Tyt into TyToA, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      inversion Tyu; subst. rename D into D2.
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyD2) in *.
      assert (ᴳ{} ᴳ+ D2 ⊢ ᵥ₎ hvars_ nil ⟨ v2 ❟ ᵛ() ⟩ : U ⧔ ①).
        { term_Val_no_dispose (ᴳ{} ᴳ+ D2). assert (hvarsᴳ( (ᴳ- ᴳ{})) = hvars_ nil). { crush. } rewrite <- H. apply TyR_val_A; swap 1 11; swap 2 10.
          rewrite hminus_empty_eq. rewrite <- union_empty_r_eq; tauto.
          rewrite stimes_empty_eq. rewrite <- union_empty_r_eq. constructor.
          all:crush. }
      rewrite <- union_empty_l_eq in H.
      constructor 1 with (D := D2) (T := U ⧔ ①) (t := ᵥ₎ hvars_ nil ⟨ v2 ❟ ᵛ() ⟩). all: crush.
    - (* Sem-eterm-FromAFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFromA, T into U.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C U U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := U ⧔ ①); swap 1 3. constructor 10. all: crush.
    - (* Sem-eterm-FromAUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U, D0 into D. clear H1.
      inversion TyCc; subst. rename U1 into U, v into v2, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2.
      rewrite (nDisposable_in_DestOnly P D2 DisposP DestOnlyD2) in *.
      assert (LinOnly D2) as LinOnlyD2.
        { apply (Ty_ectxs_LinFinOnly D2 C U U0). tauto. }
      assert (D2 ⊢ from⧔ ᵥ₎ v2 : U) as TyFromA.
        { apply (Ty_term_FromA D2 (ᵥ₎ v2) U). tauto. }
      constructor 1 with (D := D2) (T := U) (t := from⧔ ᵥ₎ v2). all: crush.
    - (* Sem-eterm-FromARed *)
      inversion Tyt; subst.
      rename Tyt0 into Tytp, D into D2, ValidOnlyD into ValidOnlyD2, DestOnlyD into DestOnlyD2, T into U.
      inversion Tytp; subst.
      inversion TyRv; subst. rename DestOnlyD2 into DestOnlyPuD1uD2, DestOnlyD0 into DestOnlyD2.
      rewrite (nDisposable_in_DestOnly P (D1 ᴳ+ D2) DisposP DestOnlyPuD1uD2) in *.
      inversion TyRv1.
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = ᴳ{}) as empty.
      { apply ext_eq'. symmetry. exact H0. }
      apply empty_union in empty. destruct empty as [empty_D1 empty_D3].
      apply empty_stimes in empty_D1.
      rewrite empty_D3, hminus_empty_eq, <- union_empty_r_eq in TyRv2.
      assert (D2 ⊢ ᵥ₎ v2 : U).
        { term_Val_no_dispose D2. }
      constructor 1 with (D := D2) (T := U) (t := ᵥ₎ v2). all: crush.
    - (* Sem-eterm-FillUFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tyt.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C ① U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ ① ⌋ n); swap 1 3. constructor 11. all: crush.
    - (* Sem-eterm-FillUUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C ① U0). tauto. }
      assert (D ⊢ ᵥ₎ v⨞() : ①) as TyFillU.
        { apply (Ty_term_FillU D (ᵥ₎ v) n). tauto. }
      constructor 1 with (D := D) (T := ①) (t := ᵥ₎ v⨞()). all: crush.
    - (* Sem-eterm-FillURed *)
      inversion Tyt; subst.
      rename Tyt into TyFillU, Tyt0 into Tytp.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C ① U0). tauto. }
      inversion Tytp; subst. clear H1.
      inversion TyRv; subst.
      rewrite (nDisposable_in_DestOnly P ᴳ{+ h : ¹ν ⌊ ① ⌋ n} DisposP DestOnlyD) in *.
      assert (ᴳ{} ⊣ C ©️[ h ≔ hvars_ nil ‗ ᵛ()] : ① ↣ U0).
        { assert (ᴳ{} ᴳ+ ¹ν ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- ᴳ{}))) = ᴳ{}) as e1. { crush. }
          rewrite <- e1.
          assert (hvarsᴳ(ᴳ- ᴳ{}) = hvars_ nil) as e2. { crush. }
          rewrite <- e2.
          assert (ᴳ{} ᴳ+ (¹ν · n) ᴳ· ᴳ{} ᴳ+ ᴳ{+ h : ¹ν ⌊ ① ⌋ n} = ᴳ{+ h : ¹ν ⌊ ① ⌋ n}) as e3. { crush. }
          rewrite <- e3 in TyC.
          apply EctxsSubLemma with (D2 := ᴳ{}) (U := ①); swap 1 14.
          { rewrite <- union_empty_l_eq. rewrite hminus_empty_eq. apply TyR_val_U. }
          all: crush. }
      constructor 1 with (D := ᴳ{}) (T := ①) (t := ᵥ₎ ᵛ()); swap 1 4.
      term_Val_no_dispose (ᴳ{}). apply TyR_val_U. all: crush.
    - (* Sem-eterm-FillLFoc *)
      inversion Tyt; subst.
      rename Tyt into TyFillL, Tyt0 into Tyt.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      constructor 1 with (D := D) (t := t) (T := ⌊ T1 ⨁ T2 ⌋ n); swap 1 3. constructor 12. all: crush.
    - (* Sem-eterm-FillLUnfoc *)
      inversion Tyt; subst. rename TyC into TyCc, T into U. clear H1.
      inversion TyCc; subst. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      assert (LinOnly D) as LinOnlyD.
        { apply (Ty_ectxs_LinFinOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      assert (D ⊢ ᵥ₎ v ⨞Inl : ⌊ T1 ⌋ n) as TyFillL.
        { apply (Ty_term_FillL D (ᵥ₎ v) T1 n T2). tauto. }
      constructor 1 with (D := D) (T := ⌊ T1 ⌋ n) (t := ᵥ₎ v ⨞Inl). all: crush.
    - (* Sem-eterm-FillLRed *)
      inversion Tyt; revert hpMaxCh; subst.
      rename Tyt into TyFillL, Tyt0 into Tytp.
      assert (LinOnly D /\ FinAgeOnly D) as (LinOnlyD & FinAgeOnlyD).
        { apply (Ty_ectxs_LinFinOnly D C (⌊ T1 ⌋ n) U0). tauto. }
      inversion Tytp; subst. clear H1. rename D0 into D.
      rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
      inversion TyRv; subst; intros hpMaxCh.
      assert (ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1} ‗ Inl ᵛ- (h' + 1)] : ⌊ T1 ⌋ n ↣ U0).
        { assert (ᴳ{} ᴳ+ ¹ν ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν }))) = ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ n }) as e1.
            { rewrite <- union_empty_l_eq. rewrite <- stimes_linnu_eq. rewrite hminus_singleton. rewrite stimes_singleton_hole. rewrite hminus_inv_singleton. rewrite mode_times_linnu_l_eq. tauto. }
          rewrite <- e1.
          assert (hvarsᴳ(ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) = ᴴ{ h' + 1}) as e2. { crush. }
          rewrite <- e2.
          assert (ᴳ{} ᴳ+ (¹ν · n) ᴳ· ᴳ{} ᴳ+ ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n} = ᴳ{+ h : ¹ν ⌊ T1 ⨁ T2 ⌋ n}) as e3. { crush. } rewrite <- e3 in TyC.
          apply EctxsSubLemma with (D2 := ᴳ{}) (D3 := ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) (U := T1 ⨁ T2); swap 1 14.
          { rewrite <- union_empty_l_eq. rewrite hminus_singleton. apply TyR_val_L. constructor. }
          give_up.
    - give_up.
Admitted.

Theorem Progress : forall (C : ectxs) (t : term) (U0 : type), ⊢ C ʲ[t] : U0 -> ((exists v, t = ᵥ₎ v) -> C <> ©️⬜) -> exists (C' : ectxs) (t' : term), C ʲ[t] ⟶ C' ʲ[t'].
Proof.
  intros C t U0 Tyj CNilOrNotValt. inversion Tyj; subst. inversion Tyt; subst.
  inversion TyC; subst. all: try rename TyC into TyCc. all: try rename C0 into C. all: try rename TyC0 into TyC. all: try rename T0 into T. all: try rename D0 into D; try rewrite (nDisposable_in_DestOnly P D DisposP DestOnlyD) in *.
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
  - rename v into v1, TyRv into TyRv1. exists C, (ᵥ₎ hvarsᴳ(ᴳ- D3) ⟨ v2 ❟ v1 ⟩). constructor.
  - assert (P ᴳ+ ᴳ{ x : m ‗ T} = ᴳ{ x : m ‗ T}) as elimP. { apply nDisposable_in_DestOnly; tauto. } rewrite elimP in *.
    exfalso. unfold DestOnly in DestOnlyD. specialize (DestOnlyD (ˣ x) (ₓ m ‗ T)). unfold ctx_singleton in DestOnlyD. rewrite singleton_MapsTo_at_elt in DestOnlyD. specialize (DestOnlyD eq_refl). unfold IsDest in DestOnlyD. contradiction.
  - rename Tyt into TyApp, T into U, T0 into T, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2.
    destruct (NotVal_dec t). all: try destruct e; subst. all: try rename x into v.
    * destruct (NotVal_dec t'). all: try destruct e; subst. all: try rename x into v'.
      + inversion Tytp; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : T ⁔ m → U ‗ ¹ν}) (h := h) (T := T ⁔ m → U); tauto. }
      exists C, (u ᵗ[x ≔ v]). constructor.
      + exists (C ∘ (v ≻⬜)), t'. constructor; tauto.
    * exists (C ∘ ⬜≻ t'), t. constructor; tauto.
  - rename Tyt into TyPatU, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ① ‗ ¹ν}) (h := h) (T := ①); tauto. } exists C, u. constructor.
    * exists (C ∘ ⬜; u), t. constructor; tauto.
  - rename Tyt into TyPatS, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : T1 ⨁ T2 ‗ ¹ν}) (h := h) (T := T1 ⨁ T2); tauto. }
      { exists C, (u1 ᵗ[x1 ≔ v1]). constructor. }
      { exists C, (u2 ᵗ[x2 ≔ v2]). constructor. }
    * exists (C ∘ (⬜≻caseˢ m {Inl x1 ⟼ u1, Inr x2 ⟼ u2})), t. constructor; tauto.
  - rename Tyt into TyPatP, T into U, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : T1 ⨂ T2 ‗ ¹ν}) (h := h) (T := T1 ⨂ T2); tauto. }
      { exists C, (u ᵗ[x1 ≔ v1] ᵗ[x2 ≔ v2]). constructor. }
    * exists (C ∘ ⬜≻caseᵖ m ᵗ( x1, x2)⟼ u), t. constructor; tauto.
  - rename Tyt into TyPatE, T into U, T0 into T, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ! n ⁔ T ‗ ¹ν}) (h := h) (T := ! n ⁔ T); tauto. }
      { exists C, (u ᵗ[x ≔ v']). constructor. }
    * exists (C ∘ ⬜≻caseᵉ m ᴇ n ⁔ x ⟼ u), t. constructor; tauto.
  - rename Tyt into TyMap, t0 into t, Tyt0 into Tyt, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : U ⧔ T ‗ ¹ν}) (h := h) (T := U ⧔ T); tauto. }
      rename D2 into D', D0 into D2. assert (DestOnly (P ᴳ+ (D1 ᴳ+ D2))) as DestOnlyPuD1uD2. { crush. } rewrite (nDisposable_in_DestOnly P (D1 ᴳ+ D2) DisposP DestOnlyPuD1uD2) in *.
      exists (C ∘ hvarsᴳ(ᴳ- D3) ᴴ⩲ (maxᴴ(hvars©(C)) + 1) ᵒᵖ⟨ v2 ᵛ[hvarsᴳ(ᴳ- D3) ⩲ (maxᴴ(hvars©(C)) + 1)] ❟⬜), (t' ᵗ[x ≔ v1 ᵛ[hvarsᴳ(ᴳ- D3) ⩲ (maxᴴ(hvars©(C)) + 1)]]). constructor; tauto.
    * exists (C ∘ ⬜≻map x ⟼ t'), t. constructor; tauto.
  - rename Tyt into TyToA. destruct (NotVal_dec u).
    * destruct e; subst. rename x into v2. exists C, (ᵥ₎ HVars.empty ⟨ v2 ❟ ᵛ() ⟩ ). constructor.
    * exists (C ∘ to⧔⬜), u. constructor; tauto.
  - rename Tyt into TyToA, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : T ⧔ ① ‗ ¹ν}) (h := h) (T := T ⧔ ①); tauto. }
      inversion TyRv1; subst. { assert (DestOnly (¹↑ ᴳ· D1 ᴳ+ D3)). { crush. } exfalso. apply TyR_val_H_DestOnly_contra with (D := (¹↑ ᴳ· D1 ᴳ+ D3)) (h := h) (T := ①). all:tauto. }
      assert (¹↑ ᴳ· D1 ᴳ+ D3 = ᴳ{}) as Empty.
      { apply ext_eq'. symmetry. apply H0. }
      apply empty_union in Empty. destruct Empty as [_ EmptyD3].
      subst. rewrite hvars_minus_eq, hvars_empty_is_hempty.
      exists C, (ᵥ₎ v2). constructor.
    * exists (C ∘ from⧔⬜), t. constructor; tauto.
  - rename Tyt into TyFillU, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ ① ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ① ⌋ n); tauto. }
      exists (C ©️[ h ≔ HVars.empty ‗ ᵛ()]), (ᵥ₎ ᵛ()). constructor.
    * exists (C ∘ ⬜⨞()), t. constructor; tauto.
  - rename Tyt into TyFillL, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ Inl ᵛ- (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ+ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inl), t. constructor; tauto.
  - rename Tyt into TyFillR, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ Inr ᵛ- (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ+ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inr), t. constructor; tauto.
  - rename Tyt into TyFillP, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ T1 ⨂ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨂ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1 , maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 2} ‗ ᵛ( ᵛ- (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1), ᵛ- (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 2))]), (ᵥ₎ ᵛ( ᵛ+ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1), ᵛ+ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 2))). constructor; tauto.
    * exists (C ∘ ⬜⨞(,)), t. constructor; tauto.
  - rename Tyt into TyFillE, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ ! n' ⁔ T ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ! n' ⁔ T ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ ᴇ n' ⁔ ᵛ- (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ+ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞ᴇ n'), t. constructor; tauto.
  - rename Tyt into TyFillF, Tyt0 into Tyt, t0 into t. destruct (NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ T ⁔ m → U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T ⁔ m → U ⌋ n); tauto. }
    exists (C ©️[ h ≔ HVars.empty ‗ λᵛ x ⁔ m ⟼ u ]), (ᵥ₎ ᵛ()). constructor; tauto.
    * exists (C ∘ ⬜⨞(λ x ⁔ m ⟼ u)), t. constructor; tauto.
  - rename Tyt into TyFillC, Tyt0 into Tyt, t0 into t, P1 into D1, P2 into D2. destruct (NotVal_dec t).
    * destruct e; subst. rename x into v. destruct (NotVal_dec t').
      + destruct e; subst. rename x into v'. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h : ⌊ U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ U ⌋ n); tauto. } rename H1 into DestOnlyD'. inversion Tytp; subst. rename TyRv0 into TyRvp. inversion TyRvp; subst. { exfalso. apply TyR_val_H_DestOnly_contra with (D := ᴳ{- h0 : U ⧔ T ‗ ¹ν}) (h := h0) (T := U ⧔ T); tauto. } assert (DestOnly (P0 ᴳ+ (D1 ᴳ+ D2))) as DestOnlyP0uD1uD2. { crush. } rewrite (nDisposable_in_DestOnly P0 (D1 ᴳ+ D2) DisposP0 DestOnlyP0uD1uD2) in *.
      exists
        ( C ©️[ h ≔ hvarsᴳ(ᴳ- D3) ᴴ⩲ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1) ‗  v2 ᵛ[hvarsᴳ(ᴳ- D3) ⩲ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1)] ] ),
        (ᵥ₎ v1 ᵛ[hvarsᴳ(ᴳ- D3) ⩲ (maxᴴ( hvars©(C) ∪ ᴴ{ h}) + 1)]).
      constructor; tauto.
      + exists (C ∘ v ⨞·⬜), t'. constructor; tauto.
    * exists (C ∘ ⬜⨞· t'), t. constructor; tauto.
Qed.

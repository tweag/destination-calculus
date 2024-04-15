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

Lemma gt_S_max : forall h H, HdnsM.mem h H = true -> h < ʰmax(H) + 1.
Proof.
  intros * h_H. unfold hdns_max.
  destruct (HdnsM.max_elt H) eqn:h_max_elt.
  2:{ apply HdnsM.max_elt_spec3 in h_max_elt. unfold HdnsM.Empty in *.
      sfirstorder use: HdnsFactsM.mem_iff. }
  apply HdnsM.max_elt_spec2  with (y:=h) in h_max_elt.
  - sfirstorder.
  - sfirstorder use: HdnsFactsM.mem_iff.
Qed.

Lemma preshift_surjective : forall H h' x, exists x', preshift H h' x' = x.
Proof.
  intros *. unfold preshift.
  destruct x as [xx|h].
  { exists (ˣ xx). reflexivity. }
  eexists (ʰ _). f_equal.
  eapply Permutation.pre_inverse.
Qed.

Lemma ValidOnlyHdnShiftEquiv: forall (G : ctx) (H : hdns) (h' : hdn), ctx_ValidOnly G <-> ctx_ValidOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_ValidOnly, ctx_hdn_shift.
  rewrite map_propagate_both with (Q := fun x b => mode_IsValid (tyb_mode b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: preshift_surjective.
Qed.
Hint Rewrite <- ValidOnlyHdnShiftEquiv : propagate_down.

Lemma DestOnlyHdnShiftEquiv: forall (G : ctx) (H : hdns) (h' : hdn), ctx_DestOnly G <-> ctx_DestOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_DestOnly, ctx_hdn_shift.
  rewrite map_propagate_both with (Q := fun x b => IsDest _ b).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: preshift_surjective.
Qed.
Hint Rewrite <- DestOnlyHdnShiftEquiv : propagate_down.

Lemma LinNuOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_LinNuOnly G <-> ctx_LinNuOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_LinNuOnly, ctx_hdn_shift.
  rewrite map_propagate_both with (Q := fun x b => mode_IsLinNu (tyb_mode b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: preshift_surjective.
Qed.
Hint Rewrite <- LinNuOnlyHdnShiftEquiv : propagate_down.

Lemma LinOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_LinOnly G <-> ctx_LinOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_LinOnly, ctx_hdn_shift.
  rewrite map_propagate_both with (Q := fun x b => mode_IsLin (tyb_mode b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: preshift_surjective.
Qed.
Hint Rewrite <- LinOnlyHdnShiftEquiv : propagate_down.

Lemma FinAgeOnlyHdnShiftEquiv : forall (G : ctx) (H : hdns) (h' : hdn), ctx_FinAgeOnly G <-> ctx_FinAgeOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_FinAgeOnly, ctx_hdn_shift.
  rewrite map_propagate_both with (Q := fun x b => mode_IsFinAge (tyb_mode b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: preshift_surjective.
Qed.
Hint Rewrite <- FinAgeOnlyHdnShiftEquiv : propagate_down.

(* TODO: Not necessarily true if `h\in D'` and `h+h' \in D`. *)
Lemma DisjointHdnShiftEq : forall (D D': ctx) (h': hdn), ctx_Disjoint D D' -> D ᴳ[ hnamesᴳ( D' ) ⩲ h' ] = D.
Proof. Admitted.

(* Sometimes bijections are beautiful *)
Lemma HdnShiftEq_preserves_Disjoint : forall D1 D2 H h', ctx_Disjoint D1 D2 <-> ctx_Disjoint (D1 ᴳ[ H ⩲ h']) (D2 ᴳ[ H ⩲ h']).
Proof. Admitted.

(* TODO: Annoying reasoning on supports. May work in setoid form though. But worth trying to do as an equality. *)
Lemma UnionHdnShiftEq : forall (G1 G2 : ctx) (H : hdns) (h' : hdn), (G1 ⨄ G2)ᴳ[ H⩲h' ] = G1 ᴳ[ H⩲h' ] ⨄ G2 ᴳ[ H⩲h' ].
Proof. Admitted.
(* TODO: add to canonalize? *)

Lemma StimesHdnShiftEq : forall (m : mode) (G : ctx) (H : hdns) (h' : hdn), (m ᴳ· G)ᴳ[ H⩲h' ] = m ᴳ· (G ᴳ[ H⩲h' ]).
Proof. Admitted.
(* TODO: add to canonalize? *)

(* TODO: not true, requires h' to be bigger than the max of H' as well, I believe. *)
Lemma hdns_max_hdns_Disjoint : forall (H H' : hdns) (h' : hdn), ʰmax(H) < h' -> hdns_Disjoint H (H' ᴴ⩲ h').
Proof. Admitted.

Lemma hnamesFullShiftEq : forall (G : ctx) (h' : hdn), hnamesᴳ(G ᴳ[ hnamesᴳ( G ) ⩲ h' ]) = hnamesᴳ(G) ᴴ⩲ h'.
Proof. Admitted.
Lemma MinusHdnShiftEq : forall (G : ctx) (H : hdns) (h' : hdn), (ᴳ- G) ᴳ[ H ⩲ h' ] = ᴳ- (G ᴳ[ H ⩲ h' ]).
Proof. Admitted.
Lemma InvMinusHdnShiftEq : forall (G : ctx) (H : hdns) (h' : hdn), (ᴳ-⁻¹ G) ᴳ[ H ⩲ h' ] = ᴳ-⁻¹ (G ᴳ[ H ⩲ h' ]).
Proof. Admitted.

(* Could really be generalised to any var-only context. *)
Lemma shift_single_variable : forall H h' x m T, ᴳ{ x : m ‗ T}ᴳ[ H ⩲ h'] = ᴳ{ x : m ‗ T}.
Proof. Admitted.
Lemma TyR_v_hdn_shift : forall (G : ctx) (v : val) (T : type) (H: hdns) (h': hdn), (G ⫦ v : T) -> (G ᴳ[ H⩲h' ] ⫦ v ᵛ[H⩲h'] : T)
with TyR_t_hdn_shift : forall (G : ctx) (t : term) (T : type) (H: hdns) (h': hdn), (G ⊢ t : T) -> (G ᴳ[ H⩲h' ] ⊢ term_hdn_shift t H h' : T).
Proof.
  - destruct 1.
    + cbn. unfold ctx_hdn_shift, hdn_shift, ctx_singleton, singleton.
      give_up . (* some extensionality required *)
    + give_up . (* I want to see a recursive case first *)
    + give_up . (* some extensionality required *)
    + cbn.
      constructor.
      * assumption.
      * erewrite <- shift_single_variable, <- UnionHdnShiftEq.
        auto.
      * hauto l: on use: DestOnlyHdnShiftEquiv.
    + cbn.
      constructor. auto.
    + cbn.
      constructor. auto.
    + cbn. rewrite UnionHdnShiftEq.
      constructor. all: auto.
    + cbn. rewrite StimesHdnShiftEq.
      constructor. all: auto.
    + cbn. rewrite UnionHdnShiftEq.
      constructor.
      (* 11 goals *)
      all: auto.
      (* 7 goals *)
      * hauto l: on use: DestOnlyHdnShiftEquiv.
      * hauto l: on use: DestOnlyHdnShiftEquiv.
      * hauto l: on use: HdnShiftEq_preserves_Disjoint.
      * give_up. (* arnaud: I'm worried about this one. I think we need an extra condition *)
      * give_up. (* arnaud: basically same *)
      * try rewrite <- StimesHdnShiftEq, <- UnionHdnShiftEq.
        (* TODO: I don't know how to prove that goal yet. Why doesn't D3 have a shift to it? *)
        give_up.
      * (* same as above *)
        give_up.
  - (* TODO *) give_up.
Admitted.

(* ========================================================================= *)

(* =========================================================================
 * Not provable with the current implementation as the support is a list 
 * whose order depends on the order of insertion.
 * ========================================================================= *)
Lemma UnionCommutative : forall (G1 G2 : ctx), G1 ⨄ G2 = G2 ⨄ G1.
Proof. Admitted.
(* ========================================================================= *)

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

Lemma ValidOnlyUnionForward' : forall (G1 G2 : ctx), Basics.impl (ctx_ValidOnly G1 /\ ctx_ValidOnly G2 /\ ctx_Disjoint G1 G2) (ctx_ValidOnly (G1 ⨄ G2)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: ValidOnlyUnionForward.
Qed.
Hint Rewrite <- ValidOnlyUnionForward' : suffices.

Lemma ValidOnlySingletonVar : forall x m T, ctx_ValidOnly ᴳ{ x : m ‗ T} <-> mode_IsValid m.
Proof.
  intros *. unfold ctx_ValidOnly.
  split.
  - intros h.
    specialize (h (ˣ x) (ₓ m ‗ T)). cbn in h.
    apply h.
    rewrite Fun.singleton_spec_1. reflexivity.
  - intros h x' tyb hx'. unfold ctx_singleton in hx'. cbn.
    rewrite singleton_mapsto in hx'.
    rewrite eq_sigT_iff_eq_dep in hx'.
    destruct hx'. cbn.
    assumption.
Qed.
Hint Rewrite ValidOnlySingletonVar : propagate_down.

Lemma ValidOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_ValidOnly (m ᴳ· G) -> ctx_ValidOnly G.
Proof.
  intros *.
  intros validmG.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_tyb_var m
      | ʰ _ => stimes_tyb_dh m
      end)
    as mf.
  unfold ctx_ValidOnly in *. intros n tyb mapstoG. specialize (validmG n (mf n tyb)).
  assert ((m ᴳ· G) n = Some (mf n tyb)).
    { eapply map_mapsto. exists tyb. split. tauto. tauto. }
  specialize (validmG H).
  destruct n, tyb; cbn in validmG; try rename n into m0; cbn; destruct m0; try constructor; unfold mode_times in validmG; destruct m in validmG; cbn in validmG; try destruct p as (_, _) in validmG; tauto.
Qed.

Lemma ValidOnlyStimesBackward' : forall (m : mode) (G : ctx), Basics.impl (ctx_ValidOnly (m ᴳ· G)) (ctx_ValidOnly G).
Proof.
  exact ValidOnlyStimesBackward.
Qed.
Hint Rewrite ValidOnlyStimesBackward' : propagate_down.

Lemma TimesIsValidEquiv : forall (m1 m2 : mode), mode_IsValid (m1 · m2) <-> mode_IsValid m1 /\ mode_IsValid m2.
Proof.
  intros [[p1 a1]|] [[p2 a2]|]. all: cbn.
  all: sfirstorder.
Qed.
Hint Rewrite TimesIsValidEquiv : propagate_down.

Lemma ValidOnlyStimesForward : forall (m : mode) (G : ctx), ctx_ValidOnly G /\ mode_IsValid m -> ctx_ValidOnly (m ᴳ· G).
Proof.
  intros * [validG validm]. unfold ctx_ValidOnly, ctx_stimes in *.
  apply map_propagate_forward'.
  - eauto.
  - intros [xx|xh] []. all: cbn.
    all: sfirstorder use: TimesIsValidEquiv.
Qed.

Lemma ValidOnlyStimesForward' : forall (m : mode) (G : ctx), Basics.impl (ctx_ValidOnly G /\ mode_IsValid m) (ctx_ValidOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: ValidOnlyStimesForward.
Qed.
Hint Rewrite <- ValidOnlyStimesForward' : suffices.

Lemma DestOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_DestOnly (G1 ⨄ G2) <-> ctx_DestOnly G1 /\ ctx_DestOnly G2.
Proof.
  intros *. unfold ctx_DestOnly, ctx_union.
  apply merge_with_propagate_both.
  intros [xx|xh]. all: cbn. { sfirstorder. }
  intros b1 b2. unfold union_tyb_dh. destruct b1, b2;
  destruct (type_eq_dec T T0), (mode_eq_dec n n0). all:sfirstorder.
Qed.
Hint Rewrite DestOnlyUnionEquiv : propagate_down.
Lemma DestOnlyStimesEquiv : forall (m : mode) (G : ctx), ctx_DestOnly G <-> ctx_DestOnly (m ᴳ· G).
Proof.
  intros *. unfold ctx_DestOnly, ctx_stimes.
  rewrite map_propagate_both'.
  { sfirstorder. }
  unfold IsDest.
  hauto lq: on.
Qed.
Hint Rewrite <- DestOnlyStimesEquiv : propagate_down.

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

Lemma IsLinNuWkIsLin : forall (m : mode), mode_IsLinNu m -> mode_IsLin m.
Proof.
  intros *.
  sauto lq: on.
Qed.

Lemma IsLinNuWkIsLin' : forall (m : mode), Basics.impl (mode_IsLinNu m) (mode_IsLinNu m /\ mode_IsLin m).
Proof.
  sfirstorder use: IsLinNuWkIsLin.
Qed.
Hint Rewrite IsLinNuWkIsLin' : saturate.

Lemma IsLinWkIsValid : forall (m : mode), mode_IsLin m -> mode_IsValid m.
Proof.
  intros m H. destruct H. apply (mode_IsValidProof (Lin, a)).
Qed.

Lemma IsLinWkIsValid' : forall (m : mode), Basics.impl (mode_IsLin m) (mode_IsLin m /\ mode_IsValid m).
Proof.
  sfirstorder use: IsLinWkIsValid.
Qed.
Hint Rewrite IsLinWkIsValid' : saturate.

Lemma mode_plus_not_lin_nu : forall b1 b2, ~mode_IsLinNu (mode_plus b1 b2).
Proof.
  intros b1 b2 h.
  apply IsLinNuWkIsLin in h.
  sfirstorder use: mode_plus_not_lin.
Qed.

Lemma LinOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinOnly (G1 ⨄ G2) <-> ctx_LinOnly G1 /\ ctx_LinOnly G2 /\ ctx_Disjoint G1 G2.
Proof.
  intros *.
  apply merge_with_propagate_both_disjoint.
  intros [xx|xh]. all: cbn.
  - intros [? ?] [? ?]. cbn.
    match goal with
    |  |- context [if ?x then _ else _] => destruct x
    end.
    (* 2 goals *)
    all: sauto lq: on use: mode_plus_not_lin.
  - intros [? ? ?|? ?] [? ? ?|? ?]. all: cbn.
    all: repeat match goal with
    |  |- context [if ?x then _ else _] => destruct x
           end.
    (* 7 goals *)
    all: sauto lq: on use: mode_plus_not_lin.
Qed.
Hint Rewrite LinOnlyUnionEquiv : propagate_down.

Lemma LinNuOnlyWkLinOnly : forall (G : ctx), ctx_LinNuOnly G -> ctx_LinOnly G.
Proof.
  intros *.
  sfirstorder use: IsLinNuWkIsLin.
Qed.

Lemma LinOnlyWkValidOnly : forall (G : ctx), ctx_LinOnly G -> ctx_ValidOnly G.
Proof.
  intros *.
  sfirstorder use: IsLinWkIsValid.
Qed.

Lemma LinNuOnlyUnionEquiv : forall (G1 G2 : ctx), ctx_LinNuOnly (G1 ⨄ G2) <-> ctx_LinNuOnly G1 /\ ctx_LinNuOnly G2 /\ ctx_Disjoint G1 G2.
Proof.
  intros *.
  split.
  - intros h.
    assert (ctx_Disjoint G1 G2) as disj.
    { hauto lq: on use: LinOnlyUnionEquiv, LinNuOnlyWkLinOnly. }
    assert (ctx_LinNuOnly G1 /\ ctx_LinNuOnly G2).
    2:{ hauto lq: on. }
    unfold ctx_LinNuOnly, ctx_union in *.
    eapply merge_with_propagate_backward_disjoint'.
    { apply disj. }
    eauto.
  - intros h. unfold ctx_LinNuOnly, ctx_union in *.
    apply merge_with_propagate_forward_disjoint.
    all: sfirstorder.
Qed.
Hint Rewrite LinNuOnlyUnionEquiv : propagate_down.

Lemma LinNuOnlyStimesForward : forall (m : mode) (G : ctx), mode_IsLinNu m -> ctx_LinNuOnly G -> ctx_LinNuOnly (m ᴳ· G).
Proof.
  intros * linm linG.
  unfold ctx_LinNuOnly in *.
  intros n b h.
  unfold ctx_stimes in h.
  rewrite map_mapsto in h. destruct h. destruct H.
  specialize (linG n x H). destruct n.
  - unfold stimes_tyb_var in H0. destruct x. subst. unfold tyb_mode in *. unfold mode_IsLinNu in *. subst. unfold mode_times. cbn. reflexivity.
  - unfold stimes_tyb_dh in H0. destruct x; subst.
    + unfold tyb_mode in *. unfold mode_IsLinNu in *. subst. unfold mode_times. cbn. reflexivity.
    + unfold tyb_mode in *. unfold mode_IsLinNu in *. subst. unfold mode_times. cbn. reflexivity.
Qed.
Lemma LinNuOnlyStimesForward' : forall (m : mode) (G : ctx), Basics.impl (mode_IsLinNu m /\ ctx_LinNuOnly G) (ctx_LinNuOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: LinNuOnlyStimesForward.
Qed.
Hint Rewrite <- LinNuOnlyStimesForward' : suffices.

Lemma n_plus_n0_eq_0_implies_n0_eq_0 : forall n n0 : nat,
  n + n0 = 0 -> n0 = 0.
Proof.
  intros n n0 H.
  apply Nat.eq_add_0 in H. (* Definition of zero *)
  destruct H. tauto.
Qed.

Lemma LinNuOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_LinNuOnly (m ᴳ· G) -> ctx_LinNuOnly G.
Proof.
  intros *.
  intros islinNu.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_tyb_var m
      | ʰ _ => stimes_tyb_dh m
      end)
    as mf.
    unfold ctx_LinNuOnly in *. intros n tyb mapstoG. specialize (islinNu n (mf n tyb)).
  assert ((m ᴳ· G) n = Some (mf n tyb)).
    { eapply map_mapsto. exists tyb. split. tauto. tauto. }
  specialize (islinNu H). unfold ctx_stimes in H. rewrite map_mapsto in H. destruct H. destruct H. destruct n; cbn in *. all: rewrite H in mapstoG; inversion mapstoG; subst. all:clear mf.
  - destruct tyb. unfold stimes_tyb_var in *. unfold mode_times, mode_IsLinNu in *. destruct m, m0; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m, m0, a, a0; cbn; inversion islinNu; subst. rewrite H2, (n_plus_n0_eq_0_implies_n0_eq_0 n n0). all:trivial. }
    all: try congruence.
  - destruct tyb; unfold stimes_tyb_dh in *; unfold mode_times, mode_IsLinNu in *; try rename n into m0; destruct m; destruct m0; cbn; try destruct p; try destruct p0; unfold mul_times, age_times, ext_plus in *; try rename n into m0; try destruct m; try destruct m0; try destruct a; try destruct a0; cbn; inversion islinNu; subst; rewrite H2.
    + rewrite (n_plus_n0_eq_0_implies_n0_eq_0 n0 n1). all:trivial.
    + rewrite (n_plus_n0_eq_0_implies_n0_eq_0 n n0). all:trivial.
Qed.
Lemma LinNuOnlyStimesBackward' : forall (m : mode) (G : ctx), Basics.impl (ctx_LinNuOnly (m ᴳ· G)) (ctx_LinNuOnly G).
Proof.
  exact LinNuOnlyStimesBackward.
Qed.
Hint Rewrite LinNuOnlyStimesBackward' : propagate_down.

Lemma FinAgeOnlyUnionBackward : forall (G1 G2 : ctx), ctx_FinAgeOnly (G1 ⨄ G2) -> ctx_FinAgeOnly G1 /\ ctx_FinAgeOnly G2.
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
Lemma FinAgeOnlyUnionBackward' : forall (G1 G2 : ctx), Basics.impl (ctx_FinAgeOnly (G1 ⨄ G2)) (ctx_FinAgeOnly G1 /\ ctx_FinAgeOnly G2).
Proof.
  exact FinAgeOnlyUnionBackward.
Qed.
Hint Rewrite FinAgeOnlyUnionBackward' : propagate_down.

Lemma FinAgeOnlyUnionForward : forall (G1 G2 : ctx), (ctx_FinAgeOnly G1 /\ ctx_FinAgeOnly G2 /\ ctx_Disjoint G1 G2) -> ctx_FinAgeOnly (G1 ⨄ G2).
Proof.
  intros * h. unfold ctx_union, ctx_FinAgeOnly.
  apply merge_with_propagate_forward_disjoint.
  all: sfirstorder.
Qed.
Lemma FinAgeOnlyUnionForward' : forall (G1 G2 : ctx), Basics.impl (ctx_FinAgeOnly G1 /\ ctx_FinAgeOnly G2 /\ ctx_Disjoint G1 G2) (ctx_FinAgeOnly (G1 ⨄ G2)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: FinAgeOnlyUnionForward.
Qed.
Hint Rewrite <- FinAgeOnlyUnionForward' : suffices.

Lemma LinOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_LinOnly (m ᴳ· G) -> ctx_LinOnly G.
Proof.
  intros *.
  intros islin.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_tyb_var m
      | ʰ _ => stimes_tyb_dh m
      end)
    as mf.
    unfold ctx_LinOnly in *. intros n tyb mapstoG. specialize (islin n (mf n tyb)).
  assert ((m ᴳ· G) n = Some (mf n tyb)).
    { eapply map_mapsto. exists tyb. split. tauto. tauto. }
  specialize (islin H). unfold ctx_stimes in H. rewrite map_mapsto in H. destruct H. destruct H. destruct n; cbn in *. all: rewrite H in mapstoG; inversion mapstoG; subst. all:clear mf.
  - destruct tyb. unfold stimes_tyb_var in *. unfold mode_times in *. destruct m eqn:em, m0 eqn:em0; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion islin. }
    all: inversion islin.
  - destruct tyb; unfold stimes_tyb_dh in *; unfold mode_times in *; try destruct m eqn:em; try destruct m0 eqn:em0; try destruct n eqn:en; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion islin. }
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion islin. }
    all: inversion islin.
    { unfold mul_times, age_times, ext_plus in *. destruct m0, m1, a, a0; cbn; try constructor. all: inversion islin. }
Qed.
Lemma LinOnlyStimesBackward' : forall (m : mode) (G : ctx), Basics.impl (ctx_LinOnly (m ᴳ· G)) (ctx_LinOnly G).
Proof.
  exact LinOnlyStimesBackward.
Qed.
Hint Rewrite LinOnlyStimesBackward' : propagate_down.

Lemma LinOnlyStimesForward : forall (m : mode) (G : ctx), mode_IsLin m -> ctx_LinOnly G -> ctx_LinOnly (m ᴳ· G).
Proof.
  intros * validm linG.
  unfold ctx_LinOnly in *.
  intros n b h.
  unfold ctx_stimes in h.
  rewrite map_mapsto in h. destruct h. destruct H.
  specialize (linG n x H). destruct n.
  - unfold stimes_tyb_var in H0. destruct x. subst. unfold tyb_mode in *. destruct m, m0; try destruct p; try destruct p0; try destruct m; try destruct m0; unfold mode_times, mul_times in *; cbn; try constructor; try inversion linG; try inversion validm.
  - unfold stimes_tyb_dh in H0. destruct x; subst; unfold tyb_mode in *; try rename n into m0; destruct m, m0; try destruct p; try destruct p0; try destruct m; try destruct m0; unfold mode_times, mul_times in *; cbn; try constructor; try inversion linG; try inversion validm.
Qed.
Lemma LinOnlyStimesForward' : forall (m : mode) (G : ctx), Basics.impl (mode_IsLin m /\ ctx_LinOnly G) (ctx_LinOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: LinOnlyStimesForward.
Qed.
Hint Rewrite <- LinOnlyStimesForward' : suffices.

Lemma FinAgeOnlyStimesBackward : forall (m : mode) (G : ctx), ctx_FinAgeOnly (m ᴳ· G) -> ctx_FinAgeOnly G.
Proof.
  intros *.
  intros isfinAge.
  pose (fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
      | ˣ _ => stimes_tyb_var m
      | ʰ _ => stimes_tyb_dh m
      end)
    as mf.
    unfold ctx_FinAgeOnly in *. intros n tyb mapstoG. specialize (isfinAge n (mf n tyb)).
  assert ((m ᴳ· G) n = Some (mf n tyb)).
    { eapply map_mapsto. exists tyb. split. tauto. tauto. }
  specialize (isfinAge H). unfold ctx_stimes in H. rewrite map_mapsto in H. destruct H. destruct H. destruct n; cbn in *. all: rewrite H in mapstoG; inversion mapstoG; subst. all:clear mf.
  - destruct tyb. unfold stimes_tyb_var in *. unfold mode_times in *. destruct m eqn:em, m0 eqn:em0; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion isfinAge. }
    all: inversion isfinAge.
  - destruct tyb; unfold stimes_tyb_dh in *; unfold mode_times in *; try destruct m eqn:em; try destruct m0 eqn:em0; try destruct n eqn:en; cbn; try destruct p; try destruct p0.
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion isfinAge. }
    { unfold mul_times, age_times, ext_plus in *. destruct m1, m2, a, a0; cbn; try constructor. all: inversion isfinAge. }
    all: inversion isfinAge.
    { unfold mul_times, age_times, ext_plus in *. destruct m0, m1, a, a0; cbn; try constructor. all: inversion isfinAge. }
Qed.
Lemma FinAgeOnlyStimesBackward' : forall (m : mode) (G : ctx), Basics.impl (ctx_FinAgeOnly (m ᴳ· G)) (ctx_FinAgeOnly G).
Proof.
  exact FinAgeOnlyStimesBackward.
Qed.
Hint Rewrite FinAgeOnlyStimesBackward' : propagate_down.

Lemma FinAgeOnlyStimesForward : forall (m : mode) (G : ctx), mode_IsFinAge m -> ctx_FinAgeOnly G -> ctx_FinAgeOnly (m ᴳ· G).
Proof.
  intros * validm finAgeG.
  unfold ctx_FinAgeOnly in *.
  intros n b h.
  unfold ctx_stimes in h.
  rewrite map_mapsto in h. destruct h. destruct H.
  specialize (finAgeG n x H). destruct n.
  - unfold stimes_tyb_var in H0. destruct x. subst. unfold tyb_mode in *. destruct m, m0; try destruct p; try destruct p0; try destruct a; try destruct a0; unfold mode_times, age_times in *; cbn; try constructor; try inversion finAgeG; try inversion validm.
  - unfold stimes_tyb_dh in H0. destruct x; subst; unfold tyb_mode in *; try rename n into m0; destruct m, m0; try destruct p; try destruct p0; try destruct a; try destruct a0; unfold mode_times, age_times in *; cbn; try constructor; try inversion finAgeG; try inversion validm.
Qed.
Lemma FinAgeOnlyStimesForward' : forall (m : mode) (G : ctx), Basics.impl (mode_IsFinAge m /\ ctx_FinAgeOnly G) (ctx_FinAgeOnly (m ᴳ· G)).
Proof.
  intros *. unfold Basics.impl.
  hauto lq: on use: FinAgeOnlyStimesForward.
Qed.
Hint Rewrite <- FinAgeOnlyStimesForward' : suffices.

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

Lemma DisjointInvMinusLeftEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint (ᴳ-⁻¹D) D'.
Proof.
  intros *. unfold ctx_Disjoint, ctx_invminus.
  split.
  - intros h x.
    rewrite <- map_In.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite <- map_In in h.
    trivial.
Qed.

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

Lemma DisjointInvMinusRightEquiv : forall (D D' : ctx), ctx_Disjoint D D' <-> ctx_Disjoint D (ᴳ-⁻¹D').
Proof.
  intros *. unfold ctx_Disjoint, ctx_invminus.
  split.
  - intros h x.
    rewrite <- map_In.
    eauto.
  - intros h x.
    specialize (h x).
    rewrite <- map_In in h.
    trivial.
Qed.

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
Hint Rewrite StimesEmptyEq : canonalize.

Lemma MinusEmptyEq : ᴳ- ᴳ{} = ᴳ{}.
Proof.
  apply Finitely.ext_eq.
  all: sfirstorder.
Qed.
Hint Rewrite MinusEmptyEq : canonalize.

Lemma InvMinusEmptyEq : ᴳ-⁻¹ ᴳ{} = ᴳ{}.
Proof.
  unfold ctx_invminus, empty, map. cbn.
  apply ext_eq.
  all: sfirstorder.
Qed.
Hint Rewrite InvMinusEmptyEq : canonalize.

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
Hint Rewrite <- UnionIdentityRight : canonalize.

Lemma UnionIdentityLeft : forall (G : ctx), G = ᴳ{} ⨄ G.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros x. unfold ctx_union.
    destruct (In_dec x G) as [[y h_inG]|h_ninG]. all: rewrite ?In_None2 in *.
    + erewrite merge_with_spec_3.
      2:{ eauto. }
      eauto.
    + erewrite merge_with_spec_4.
      all: eauto.
  - unfold ctx_union. destruct G. cbn.
    reflexivity.
Qed.
Hint Rewrite <- UnionIdentityLeft : canonalize.

Lemma DisjointDestOnlyVar : forall (G : ctx) (x : var) (m : mode) (T : type), ctx_DestOnly G -> ctx_Disjoint G (ᴳ{ x : m ‗ T}).
Proof.
  intros * destonly.
  unfold ctx_DestOnly, ctx_Disjoint in *.
  intros n inG inSing.
  unfold In, Fun.In in *.
  destruct inG as (tyb & mapsto).
  specialize (destonly n tyb mapsto).
  unfold ctx_singleton in inSing. destruct inSing. rewrite singleton_mapsto in H.
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

Lemma UnionCommutative' : forall (G1 G2 : ctx) x, (G1 ⨄ G2) x = (G2 ⨄ G1) x.
Proof.
  intros *. unfold ctx_union.
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

Lemma UnionAssociative : forall (G1 G2 G3 : ctx), G1 ⨄ (G2 ⨄ G3) = (G1 ⨄ G2) ⨄ G3.
Proof.
  intros *. unfold ctx_union.
  apply merge_with_associative.
  intros [xx|xh].
  - intros [? ?] [? ?] [? ?]. cbn. unfold union_tyb_var.
    repeat match goal with
           |  |- context [if ?x then _ else _] => destruct x
           end.
    { rewrite mode_plus_associative. reflexivity. }
    all: try sfirstorder.
    (* 3 goals left *)
    all: destruct m as [[? ?]|]; cbn.
    all: sfirstorder.
  - intros [? ? ?|? ?] [? ? ?|? ?] [? ? ?|? ?]. all: cbn. all: unfold union_tyb_dh.
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
    all: sfirstorder.
Qed.
Hint Rewrite UnionAssociative : canonalize.

Lemma TimesCommutative : forall (m n : mode), m · n = n · m.
Proof.
  intros [[p1 a1]|] [[p2 a2]|]. cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct a1 as [?|]; destruct a2 as [?|].
  all: cbn.
  all: sfirstorder use: PeanoNat.Nat.add_comm.
Qed.

Lemma TimesAssociative : forall (m1 m2 m3 : mode), m1 · (m2 · m3) = (m1 · m2) · m3.
Proof.
  intros [[p1 a1]|] [[p2 a2]|] [[p3 a3]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct p3 as [|]; destruct a1 as [?|]; destruct a2 as [?|]; destruct a3 as [?|]. all: cbn.
  all: sfirstorder use: PeanoNat.Nat.add_assoc.
Qed.
Hint Rewrite TimesAssociative : canonalize.

Lemma TimesIdentityRight : forall (m : mode), m · ¹ν = m.
Proof.
  intros [[p a]|]. all: cbn.
  2:{ trivial. }
  destruct p as [|]; destruct a as [?|]. all: cbn.
  all: hauto lq: on use: PeanoNat.Nat.add_0_r.
Qed.
Hint Rewrite TimesIdentityRight : canonalize.

Lemma TimesIdentityLeft : forall (m : mode), ¹ν · m = m.
Proof.
  intros [[p a]|]. all: cbn.
  2:{ trivial. }
  destruct p as [|]; destruct a as [?|]. all: cbn.
  all: hauto lq: on use: PeanoNat.Nat.add_0_l.
Qed.
Hint Rewrite TimesIdentityLeft : canonalize.

Lemma StimesIsAction : forall (m n : mode) (G : ctx), m ᴳ· (n ᴳ· G) = (m · n) ᴳ· G.
Proof.
  intros *.
  apply ext_eq.
  2:{ reflexivity. }
  intros x. unfold ctx_stimes.
  rewrite map_comp.
  apply map_ext. clear x.
  intros [xx|xh].
  - apply functional_extensionality. cbn.
    intros [? ?]. cbn.
    sfirstorder use: TimesAssociative.
  - apply functional_extensionality. cbn.
    intros [? ? ?|? ?]. all: cbn.
    all: sfirstorder use: TimesAssociative.
Qed.
Hint Rewrite StimesIsAction : canonalize.

Lemma TimesDistributeOverPlus : forall (m n o : mode), m · (mode_plus n o) = mode_plus (m · n) (m · o).
Proof.
  intros [[p1 a1]|] [[p2 a2]|] [[p3 a3]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct p3 as [|]; destruct a1 as [?|]; destruct a2 as [?|]; destruct a3 as [?|]. all: unfold mul_plus, mul_times, age_plus, age_times, ext_plus; repeat destruct age_eq_dec. all: trivial; try congruence; try reflexivity.
  all: exfalso; assert (n0 <> n1) as Hneq by (intros H; apply n2; rewrite H; constructor);
                  assert (n + n0 = n + n1) as Heq by (injection e; auto);
                  apply Hneq; rewrite Nat.add_cancel_l with (p := n) in Heq; assumption.
Qed.

Lemma StimesUnionDistributive : forall (m : mode) (G1 G2 : ctx),  m ᴳ· (G1 ⨄ G2) = m ᴳ· G1 ⨄ m ᴳ· G2.
Proof.
  intros *.
  apply Finitely.ext_eq.
  2:{ reflexivity. }
  intros n. unfold ctx_stimes, ctx_union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.merge_fun_of_with.
  assert (exists e, age_eq_dec Inf Inf = left e) as eq_inf_inf.
    { destruct age_eq_dec. exists e; reflexivity. congruence. } destruct eq_inf_inf as (eqrefl & eq_inf_inf).
  destruct (In_dec n G1), (In_dec n G2), n.
  - destruct H as (tyb1 & mapstoG1), H0 as (tyb2 & mapstoG2); cbn; rewrite mapstoG1; rewrite mapstoG2; cbn.
    f_equal. unfold stimes_tyb_var, union_tyb_var.
    destruct tyb1, tyb2, (type_eq_dec T T0).
    { rewrite TimesDistributeOverPlus; reflexivity. }
    { unfold mode_times. destruct m. destruct p. all: tauto. }
  - destruct H as (tyb1 & mapstoG1), H0 as (tyb2 & mapstoG2); cbn; rewrite mapstoG1; rewrite mapstoG2; cbn.
    f_equal. unfold stimes_tyb_dh, union_tyb_dh.
    destruct tyb1, tyb2, (type_eq_dec T T0); try destruct (mode_eq_dec n n0).
    all: try rewrite TimesDistributeOverPlus; try reflexivity.
    all: unfold mode_times; destruct m; try destruct p. all: tauto.
  - destruct H as (tyb1 & mapstoG1); cbn; rewrite mapstoG1; cbn. rewrite In_None2 in H0. rewrite H0. reflexivity.
  - destruct H as (tyb1 & mapstoG1); cbn; rewrite mapstoG1; cbn. rewrite In_None2 in H0. rewrite H0. reflexivity.
  - destruct H0 as (tyb2 & mapstoG2); cbn; rewrite mapstoG2; cbn. rewrite In_None2 in H. rewrite H. reflexivity.
  - destruct H0 as (tyb2 & mapstoG2); cbn; rewrite mapstoG2; cbn. rewrite In_None2 in H. rewrite H. reflexivity.
  - cbn. rewrite In_None2 in H. rewrite H. rewrite In_None2 in H0. rewrite H0. reflexivity.
  - cbn. rewrite In_None2 in H. rewrite H. rewrite In_None2 in H0. rewrite H0. reflexivity.
Qed.
Hint Rewrite StimesUnionDistributive : canonalize.

Lemma MinusUnionDistributive : forall (G1 G2 : ctx), ctx_Disjoint G1 G2 ->ᴳ- (G1 ⨄ G2) = ᴳ-G1 ⨄ ᴳ-G2.
Proof.
  intros * Disjoint.
  apply Finitely.ext_eq.
  2:{ reflexivity. }
  intros n. unfold ctx_minus, ctx_union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.merge_fun_of_with.
  destruct (In_dec n G1), (In_dec n G2).
  { unfold ctx_Disjoint in Disjoint. specialize (Disjoint n H H0). contradiction. }
  all: destruct n; try destruct H as (tyb1 & mapstoG1); try destruct H0 as (tyb2 & mapstoG2); cbn; try rewrite In_None2 in H; try rewrite In_None2 in H0; try rewrite mapstoG1; try rewrite mapstoG2; try rewrite H; try rewrite H0; cbn; trivial.
Qed.

Lemma InvMinusUnionDistributive : forall (G1 G2 : ctx), ctx_Disjoint G1 G2 ->ᴳ-⁻¹ (G1 ⨄ G2) = ᴳ-⁻¹G1 ⨄ ᴳ-⁻¹G2.
Proof.
  intros * Disjoint.
  apply Finitely.ext_eq.
  2:{ reflexivity. }
  intros n. unfold ctx_invminus, ctx_union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.merge_fun_of_with.
  destruct (In_dec n G1), (In_dec n G2).
  { unfold ctx_Disjoint in Disjoint. specialize (Disjoint n H H0). contradiction. }
  all: destruct n; try destruct H as (tyb1 & mapstoG1); try destruct H0 as (tyb2 & mapstoG2); cbn; try rewrite In_None2 in H; try rewrite In_None2 in H0; try rewrite mapstoG1; try rewrite mapstoG2; try rewrite H; try rewrite H0; cbn; trivial.
Qed.

Lemma StimesIdentity :  forall (G: ctx), G = ¹ν ᴳ· G.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros x. unfold ctx_stimes.
    destruct x as [xx|xh].
    + destruct (In_dec (ˣ xx) G) as [[tyb mapsto]|notinG].
      * rewrite mapsto. symmetry. apply map_mapsto. exists tyb. split; trivial.
        unfold stimes_tyb_var, mode_times. destruct tyb, m; try destruct p; try destruct m, a; unfold mul_times, age_times, ext_plus; rewrite? Nat.add_0_l; reflexivity.
      * rewrite In_None2 in notinG. rewrite notinG. symmetry. rewrite map_mapsto_None; tauto.
    + destruct (In_dec (ʰ xh) G) as [[tyb mapsto]|notinG].
      * rewrite mapsto. symmetry. apply map_mapsto. exists tyb. split; trivial.
        unfold stimes_tyb_dh, mode_times. destruct tyb; try rename n into m; destruct m; try destruct p; try destruct m, a; unfold mul_times, age_times, ext_plus; rewrite? Nat.add_0_l; reflexivity.
      * rewrite In_None2 in notinG. rewrite notinG. symmetry. rewrite map_mapsto_None; tauto.
  - unfold ctx_stimes. unfold map. simpl. reflexivity.
Qed.
Hint Rewrite <- StimesIdentity : canonalize.

Lemma HdnsUnionIdentityLeft : forall (H : hdns), H = (HdnsM.union HdnsM.empty H).
Proof.
  intros H.
  apply HdnsM.eq_leibniz. unfold HdnsM.eq.
  intros h. rewrite HdnsFactsM.union_iff. (* Definition of set equality *)
  split.
  - right; tauto.
  - intros [H1 | H2]. (* By definition of union, we can prove any goal if it is in one of the two sets *)
    + inversion H1.
    + tauto.
Qed.

Lemma HdnsUnionIdentityRight : forall (H : hdns), H = (HdnsM.union H HdnsM.empty).
Proof.
  intros H.
  apply HdnsM.eq_leibniz. unfold HdnsM.eq.
  intros h. rewrite HdnsFactsM.union_iff. (* Definition of set equality *)
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

Lemma ListSubset_cons {A : Type} : forall (l1 l2 : list A) (x : A), ListSubset (x :: l1) l2 <-> List.In x l2 /\ ListSubset l1 l2.
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

Lemma hnames_spec : forall (G : ctx) (h : hdn), HdnsM.In h (hnamesᴳ(G)) <-> exists x, G (name_DH h) = Some x.
Proof.
  intros *. split.
  - intros Hin. unfold hdns_from_ctx, hdns_from_ctxdom in Hin. remember (dom(G)) as l in Hin. assert (ListSubset l (dom G)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    * inversion Hin.
    * rename a into n, l into ns.
      rewrite ListSubset_cons in H; destruct H; rewrite dom_spec in H; rewrite In_spec in H. destruct ((fix hdns_from_ctxdom (dom : list name) : HdnsM.t := match dom with
| ©️⬜ => HdnsM.empty
| xs ∘ ˣ _ => hdns_from_ctxdom xs
| xs ∘ ʰ h => HdnsM.add h (hdns_from_ctxdom xs)
end) ns).
      destruct n.
      + specialize (IHl Hin H0). assumption.
      + destruct (Nat.eq_dec h h0).
        { rewrite e in *; assumption. }
        { assert (HdnsM.In h {| HdnsM.this := this; HdnsM.is_ok := is_ok |}).
          { rewrite HdnsM.add_spec in Hin. destruct Hin. congruence. assumption. }
          specialize (IHl H1 H0). assumption.
        }
  - intros Hin. rewrite <- In_spec in Hin. apply dom_spec in Hin. unfold hdns_from_ctx, hdns_from_ctxdom. remember (dom(G)) as l. assert (ListSubset l (dom G)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    * inversion Hin.
    * rename a into n, l into ns.
      destruct n.
      { rewrite ListSubset_cons in H; destruct H.
        assert (List.In (ʰ h) ns).
        { destruct Hin. congruence. assumption. }
        specialize (IHl H1 H0). assumption.
      }
      { destruct (Nat.eq_dec h h0).
        { rewrite e in *. apply HdnsM.add_spec. left. congruence. }
        { assert (List.In (ʰ h) ns).
          { destruct Hin. inversion H0. congruence. assumption. }
          apply ListSubset_cons in H; destruct H. specialize (IHl H0 H1). apply HdnsM.add_spec. right. assumption.
        }
      }
Qed.

Lemma HdnsInCtxUnionEquiv : forall (G G': ctx) (h: hdn), HdnsM.In h hnamesᴳ(G ⨄ G') <-> HdnsM.In h hnamesᴳ(G) \/ HdnsM.In h hnamesᴳ(G').
Proof.
  intros *. split.
  - intros Hin. apply hnames_spec in Hin. rewrite hnames_spec, hnames_spec. destruct Hin as [x Hin]. destruct (In_dec (name_DH h) G) as [inG|notinG], (In_dec (name_DH h) G') as [inG'|notinG']; try unfold In, Fun.In in inG; try unfold In, Fun.In in inG'.
    + left. assumption.
    + left. assumption.
    + right. assumption.
    + assert (In (ʰ h) (G ⨄ G')). { unfold In, Fun.In. exists x. assumption. } apply merge_with_spec_5 in H. unfold In, Fun.In in H. assumption.
  - intros [inG|inG'].
    + apply hnames_spec. rewrite hnames_spec in inG. destruct inG as [x inG]. destruct (In_dec (ʰ h) G').
      * unfold In, Fun.In in H. destruct H as (y & H). exists (union_tyb_dh x y). apply merge_with_spec_1. split; assumption.
      * rewrite In_None2 in H. exists x. apply merge_with_spec_2. split; assumption.
    + apply hnames_spec. rewrite hnames_spec in inG'. destruct inG' as [x inG']. destruct (In_dec (ʰ h) G).
      * unfold In, Fun.In in H. destruct H as (y & H). exists (union_tyb_dh y x). apply merge_with_spec_1. split; assumption.
      * rewrite In_None2 in H. exists x. apply merge_with_spec_3. split; assumption.
Qed.

Lemma HdnsInCtxStimesEquiv : forall (m : mode) (G : ctx) (h: hdn), HdnsM.In h hnamesᴳ(m ᴳ· G) <-> HdnsM.In h hnamesᴳ(G).
Proof.
  sauto lq: on use: hnames_spec, map_mapsto.
Qed.

Lemma HdnsSubsetCtxUnionBackward : forall (G G': ctx) (H: hdns), HdnsM.Subset hnamesᴳ(G ⨄ G') H -> HdnsM.Subset hnamesᴳ(G) H /\ HdnsM.Subset hnamesᴳ(G') H.
Proof.
  unfold HdnsM.Subset in *. intros *. intros Hyp. split.
  - intros h Hin. specialize (Hyp h). apply Hyp, HdnsInCtxUnionEquiv. left. assumption.
  - intros h Hin. specialize (Hyp h). apply Hyp, HdnsInCtxUnionEquiv. right. assumption.
Qed.

Lemma HdnsSubsetCtxStimesBackward : forall (m : mode) (G : ctx) (H: hdns), HdnsM.Subset hnamesᴳ(m ᴳ· G) H -> HdnsM.Subset hnamesᴳ(G) H.
Proof.
  unfold HdnsM.Subset in *. intros *. intros Hyp h Hin. specialize (Hyp h). apply Hyp, HdnsInCtxStimesEquiv. assumption.
Qed.

Lemma hnamesMinusEq : forall (D : ctx), (hnamesᴳ( ᴳ- D)) = hnamesᴳ( D).
Proof.
  intros D. apply HdnsM.eq_leibniz. unfold HdnsM.eq. intros h. rewrite! hnames_spec. split.
  - intros Hin. rewrite <- In_spec in Hin. unfold ctx_minus in Hin. rewrite <- map_In in Hin. rewrite <- In_spec. assumption.
  - intros Hin. rewrite <- In_spec in Hin. unfold ctx_minus. rewrite <- In_spec. rewrite <- map_In. assumption.
Qed.

Lemma hnamesInvMinusEq : forall (D : ctx), hnamesᴳ( ᴳ-⁻¹ D) = hnamesᴳ( D).
Proof.
  intros D. apply HdnsM.eq_leibniz. unfold HdnsM.eq. intros h. rewrite! hnames_spec. split.
  - intros Hin. rewrite <- In_spec in Hin. unfold ctx_invminus in Hin. rewrite <- map_In in Hin. rewrite <- In_spec. assumption.
  - intros Hin. rewrite <- In_spec in Hin. unfold ctx_invminus. rewrite <- In_spec. rewrite <- map_In. assumption.
Qed.

Lemma hnames_CWkhnames_G : forall (C : ectxs) (D : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), HdnsM.Subset hnamesᴳ(D) hnames©(C).
Proof.
  intros * TyC. induction TyC.
  { cbn. reflexivity. }
  all:
      try (cbn; unfold HdnsM.Subset; apply HdnsSubsetCtxUnionBackward in IHTyC; destruct IHTyC as (IHTyC1 & IHTyC2);  try apply HdnsSubsetCtxStimesBackward in IHTyC1; unfold HdnsM.Subset in IHTyC1 ; intros h Hin; specialize (IHTyC1 h Hin); apply HdnsFactsM.union_iff; right; assumption);
      try (cbn; unfold HdnsM.Subset; apply HdnsSubsetCtxUnionBackward in IHTyC; destruct IHTyC as (IHTyC1 & IHTyC2); try apply HdnsSubsetCtxStimesBackward in IHTyC2; unfold HdnsM.Subset in IHTyC2; intros h Hin; specialize (IHTyC2 h Hin); apply HdnsFactsM.union_iff; right; assumption);
      try (cbn; unfold HdnsM.Subset in * ; intros h Hin; specialize (IHTyC h Hin); apply HdnsFactsM.union_iff; right; assumption).
  simpl. unfold HdnsM.Subset in *. intros h Hin. apply HdnsFactsM.union_iff. apply HdnsInCtxUnionEquiv in Hin. destruct Hin as [inD1|inD3].
  - right. apply HdnsInCtxStimesEquiv in inD1. assert (HdnsM.In h hnamesᴳ( D1 ⨄ D2)).
    { apply HdnsInCtxUnionEquiv. left. assumption. }
    specialize (IHTyC h H0). assumption.
  - left. rewrite hnamesMinusEq. assumption.
Qed.

Lemma hnames_DisjointToDisjoint : forall (D D' : ctx), ctx_DestOnly D -> hdns_Disjoint hnamesᴳ(D) hnamesᴳ(D') -> ctx_Disjoint D D'.
Proof.
  intros * DestOnlyD hdnsDisjoint.
  unfold ctx_Disjoint. intros n inD inD'. unfold In, Fun.In in *. destruct n.
  - unfold ctx_DestOnly, IsDest in DestOnlyD. destruct inD as (tyb & inD); specialize (DestOnlyD (name_Var x) tyb inD); cbn in DestOnlyD. assumption.
  - rewrite <- hnames_spec in inD, inD'. unfold hdns_Disjoint in hdnsDisjoint.
    assert (HdnsM.In h (HdnsM.inter hnamesᴳ(D) hnamesᴳ(D'))).
      { apply HdnsM.inter_spec. split; assumption. }
    unfold HdnsM.Empty in hdnsDisjoint. specialize (hdnsDisjoint h). congruence.
Qed.

Lemma DisjointTohdns_Disjoint : forall (D D' : ctx), ctx_Disjoint D D' -> hdns_Disjoint hnamesᴳ(D) hnamesᴳ(D').
Proof.
  intros * Disjoint.
  unfold hdns_Disjoint. unfold HdnsM.Empty. intros h HinInter.
  rewrite HdnsFactsM.inter_iff in HinInter. destruct HinInter as (inD & inD').
  rewrite hnames_spec in inD, inD'. rewrite <- In_spec in inD, inD'.
  unfold ctx_Disjoint in Disjoint. specialize (Disjoint (name_DH h) inD inD'). assumption.
Qed.

Lemma not_lt_le : forall (x y : nat),
  ~ x < y -> y <= x.
Proof.
  sfirstorder.
Qed.

Lemma HmaxSubset : forall (H H' : hdns), HdnsM.Subset H H' -> ʰmax(H) <= ʰmax(H').
Proof.
  intros *. unfold HdnsM.Subset. intros Hyp. unfold hdns_max. destruct (HdnsM.max_elt H) as [h|] eqn:eMax.
    - apply HdnsM.max_elt_spec1 in eMax. specialize (Hyp h eMax).
      destruct (HdnsM.max_elt H') as [h'|] eqn:eMax'.
      + assert (~(h'<h)). { apply HdnsM.max_elt_spec2 with (s := H'). all:assumption. }
        apply not_lt_le; assumption.
      + apply HdnsM.max_elt_spec3 in eMax'. unfold HdnsM.Empty in eMax'. specialize (eMax' h). congruence.
    - apply Nat.le_0_l.
Qed.

Lemma hnamesEmpty : hnamesᴳ(ᴳ{}) = HdnsM.empty.
Proof.
  unfold hdns_from_ctx, hdns_from_ctxdom, ctx_empty. rewrite dom_empty. reflexivity.
Qed.

Lemma EmptyIshdns_DisjointRight : forall (H : hdns), hdns_Disjoint H HdnsM.empty.
Proof.
  intros H. unfold hdns_Disjoint. unfold HdnsM.Empty. intros h Hin. rewrite HdnsM.inter_spec in Hin. destruct Hin. inversion H1.
Qed.
Lemma EmptyIshdns_DisjointLeft : forall (H : hdns), hdns_Disjoint HdnsM.empty H.
Proof.
  intros H. unfold hdns_Disjoint. unfold HdnsM.Empty. intros h Hin. rewrite HdnsM.inter_spec in Hin. destruct Hin. inversion H0.
Qed.

Lemma IsSubtype_refl : forall (m : mode), mode_IsSubtype m m.
Proof.
  intros m. sauto lq: on.
Qed.

Lemma CompatibleDestSingleton : forall (h : hdn) (m : mode) (T : type) (n : mode), ctx_CompatibleDH (ᴳ{+ h : m ⌊ T ⌋ n}) h (₊ m ⌊ T ⌋ n).
Proof.
  intros *.
  unfold ctx_CompatibleDH. split.
  + unfold ctx_singleton. apply in_singleton. reflexivity.
  + unfold ctx_singleton. intros nam tyb Hin. rewrite singleton_mapsto in Hin. pose proof Hin as Hin'. apply eq_sigT_fst in Hin; subst. apply inj_pair2_eq_dec in Hin'; subst.
    simpl. destruct (HdnsFactsM.eq_dec h h).
    - repeat split. apply IsSubtype_refl.
    - congruence.
    - exact (name_eq_dec).
Qed.

Lemma IncompatibleVarDestOnly : forall (D : ctx) (x : var) (m : mode) (T : type), ctx_DestOnly D -> ~ctx_CompatibleVar D x (ₓ m ‗ T).
Proof.
  intros * DestOnly CompatibleVar. destruct CompatibleVar as (inD & CompatibleVar).
  unfold ctx_DestOnly, IsDest in DestOnly. unfold ctx_CompatibleVar in CompatibleVar. destruct (dom(D)) eqn:eDomD.
  - rewrite <- dom_spec in inD. rewrite eDomD in inD. inversion inD.
  - assert (List.In n (dom D)). { rewrite eDomD. apply in_eq. }
    rewrite dom_spec in H. destruct H as (tyb & mapstoD). destruct n. specialize (DestOnly (ˣ x0) tyb mapstoD). assumption. apply In_spec in inD; destruct inD as (tyb' & mapstoD'). specialize (DestOnly (ˣ x) tyb' mapstoD'). simpl in DestOnly. assumption.
Qed.

Lemma MinusSingletonEq : forall (h : hdn) (T : type) (n : mode), ᴳ- ᴳ{+ h : ¹ν ⌊ T ⌋ n} = ᴳ{- h : T ‗ n }.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros n'. unfold ctx_minus, ctx_singleton.
    destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
    { rewrite singleton_spec_1. apply map_mapsto. rewrite singleton_spec_1. simpl. exists (₊ ¹ν ⌊ T ⌋ n). split; tauto. }
    { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ ¹ν ⌊ T ⌋ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      rewrite H0 in *. apply map_mapsto_None. assumption. }
  - unfold ctx_minus.
    sfirstorder.
Qed.

Lemma InvMinusSingletonEq : forall (h : hdn) (T : type) (n : mode), ᴳ-⁻¹ ᴳ{- h : T ‗ n} = ᴳ{+ h : ¹ν ⌊ T ⌋ n }.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros n'. unfold ctx_invminus, ctx_singleton.
    destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
    { rewrite singleton_spec_1. apply map_mapsto. rewrite singleton_spec_1. simpl. exists (₋ T ‗ n). split; tauto. }
    { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ ¹ν ⌊ T ⌋ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      rewrite H in *. apply map_mapsto_None. assumption. }
  - unfold ctx_invminus.
    sfirstorder.
Qed.

Lemma StimesSingletonVar : forall (x : var) (m : mode) (T : type) (m' : mode), m' ᴳ· ᴳ{ x : m ‗ T} = ᴳ{ x : (m · m') ‗ T}.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros n. unfold ctx_stimes, ctx_singleton.
    destruct (name_eq_dec n (ˣ x)); rewrite? e in *.
    { rewrite singleton_spec_1. apply map_mapsto. rewrite singleton_spec_1. simpl. exists (ₓ m ‗ T). split. tauto. unfold stimes_tyb_var. rewrite TimesCommutative. reflexivity. }
    { assert (@singleton name binding_type_of (ˣ x) name_eq_dec (ₓ m ‗ T) n = None). { apply singleton_spec_2. symmetry. assumption. }
      assert (@singleton name binding_type_of (ˣ x) name_eq_dec (ₓ (m · m') ‗ T) n = None). { apply singleton_spec_2. symmetry. assumption. }
      rewrite H0 in *. apply map_mapsto_None. assumption. }
  - unfold ctx_stimes.
    sfirstorder.
Qed.

Lemma StimesSingletonDest : forall (h : hdn) (m n : mode) (T : type) (m': mode), m' ᴳ· ᴳ{+ h : m ⌊ T ⌋ n} = ᴳ{+ h : (m · m') ⌊ T ⌋ n}.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros n'. unfold ctx_stimes, ctx_singleton.
    destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
    { rewrite singleton_spec_1. apply map_mapsto. rewrite singleton_spec_1. simpl. exists (₊ m ⌊ T ⌋ n). split. tauto. unfold stimes_tyb_dh. rewrite TimesCommutative. reflexivity. }
    { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ m ⌊ T ⌋ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ (m · m') ⌊ T ⌋ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      rewrite H0 in *. apply map_mapsto_None. assumption. }
  - unfold ctx_stimes.
    sfirstorder.
Qed.
Lemma StimesSingletonHole : forall (h : hdn) (T : type) (n : mode) (m': mode), m' ᴳ· ᴳ{- h : T ‗ n} = ᴳ{- h : T ‗ (n · m') }.
Proof.
  intros *.
  apply Finitely.ext_eq.
  - intros n'. unfold ctx_stimes, ctx_singleton.
    destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
    { rewrite singleton_spec_1. apply map_mapsto. rewrite singleton_spec_1. simpl. exists (₋ T ‗ n). split. tauto. unfold stimes_tyb_dh. rewrite TimesCommutative. reflexivity. }
    { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ n) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ T ‗ (n · m')) n' = None). { apply singleton_spec_2. symmetry. assumption. }
      rewrite H0 in *. apply map_mapsto_None. assumption. }
  - unfold ctx_stimes.
    sfirstorder.
Qed.

Lemma hnamesSingletonDestEq : forall (h : hdn) (m n : mode) (T : type), hnamesᴳ( ᴳ{+ h : m ⌊ T ⌋ n} ) = ᴴ{ h }.
Proof.
  intros *.
  unfold hdns_from_ctx, hdns_from_ctxdom, hdns_from_list, ctx_singleton.
  rewrite dom_singleton. reflexivity.
Qed.

Lemma hnamesSingletonHoleEq : forall (h : hdn) (T : type) (n : mode), hnamesᴳ( ᴳ{- h : T ‗ n} ) = ᴴ{ h }.
Proof.
  intros *.
  unfold hdns_from_ctx, hdns_from_ctxdom, hdns_from_list, ctx_singleton.
  rewrite dom_singleton. reflexivity.
Qed.

Lemma empty_support_Empty : forall (G : ctx), support G = nil -> G = ᴳ{}.
Proof.
  intros * h.
  apply ext_eq.
  2:{ cbn. trivial. }
  intros x. cbn.
  destruct (In_dec x G) as [[y h_inG]|h_ninG]. all: rewrite ?In_None2 in *.
  - apply support_supports in h_inG.
    sauto q: on use: in_nil.
  - trivial.
Qed.

Lemma SubsetDisjoint : forall (H1 H2 H3 : hdns), HdnsM.Subset H1 H2 -> hdns_Disjoint H2 H3 -> hdns_Disjoint H1 H3.
Proof.
  intros * H1H2 H2H3. unfold hdns_Disjoint, HdnsM.Subset, HdnsM.Empty in *.
  intros h. specialize (H1H2 h). specialize (H2H3 h).
  intros HinInter. apply HdnsM.inter_spec in HinInter. destruct HinInter as [H1h H3h]. specialize (H1H2 H1h). destruct H2H3. apply HdnsM.inter_spec. split; assumption.
Qed.

Lemma CompatibleLinFinOnlyIsExact : forall (D : ctx) (h : hdn) (T : type) (n : mode), ctx_LinOnly D -> ctx_FinAgeOnly D -> ctx_CompatibleDH D h (₊ ¹ν ⌊ T ⌋ n) -> (forall x, D x = ᴳ{+ h : ¹ν ⌊ T ⌋ n} x).
Proof.
  intros * LinOnly FinAgeOnly CompatibleDH.
  unfold ctx_CompatibleDH in CompatibleDH. destruct CompatibleDH as (inD & CompatibleDH).
  intros nam. destruct (name_eq_dec nam (ʰ h)).
    + rewrite e in *. unfold ctx_singleton. rewrite singleton_spec_1. rewrite In_spec in inD.
      destruct inD as (tyb & inD). specialize (CompatibleDH (ʰ h) tyb inD). simpl in CompatibleDH. destruct (HdnsFactsM.eq_dec h h) in CompatibleDH.
      2:{ congruence. }
      destruct tyb eqn: etyb in CompatibleDH.
      { destruct CompatibleDH as (sub & e1 & e2). subst. 
        assert (¹ν = m). { inversion sub. inversion H1. inversion H3. reflexivity. }
        rewrite <- H in inD; assumption.
      }
      { contradiction. }
    + specialize (CompatibleDH nam). destruct (D nam) eqn:mapsto.
      { specialize (CompatibleDH b eq_refl). destruct nam.
        { unfold ctx_LinOnly in LinOnly. specialize (LinOnly (ˣ x) b mapsto). inversion LinOnly. inversion CompatibleDH. destruct b; congruence. }
        { destruct (HdnsFactsM.eq_dec h h0).
          congruence.
          unfold ctx_LinOnly in LinOnly. specialize (LinOnly (ʰ h0) b mapsto). inversion LinOnly. inversion CompatibleDH. destruct b; congruence.
        }
      }
      { unfold ctx_singleton. symmetry. apply singleton_spec_2. symmetry. assumption. }
Qed.

Ltac hauto_ctx :=
  hauto
    depth: 3
    use: ValidOnlyUnionBackward, ValidOnlyUnionForward, ValidOnlyStimesBackward, ValidOnlyStimesForward, ValidOnlyHdnShiftEquiv, DestOnlyUnionEquiv, DestOnlyStimesEquiv, DestOnlyHdnShiftEquiv, LinNuOnlyUnionEquiv, LinNuOnlyStimesBackward, LinNuOnlyStimesForward, LinNuOnlyHdnShiftEquiv, LinOnlyUnionEquiv, LinOnlyStimesBackward, LinOnlyStimesForward, LinOnlyHdnShiftEquiv, LinNuOnlyWkLinOnly, LinOnlyWkValidOnly, IsLinNuWkIsLin, IsLinWkIsValid, DisjointStimesLeftEquiv, DisjointStimesRightEquiv, DisjointMinusLeftEquiv, DisjointInvMinusLeftEquiv, DisjointMinusRightEquiv, DisjointInvMinusRightEquiv, DisjointNestedLeftEquiv, DisjointNestedRightEquiv, DisjointHdnShiftEq, DisjointCommutative, EmptyIsLinOnly, EmptyIsDestOnly, EmptyIsDisjointLeft, EmptyIsDisjointRight, StimesEmptyEq, MinusEmptyEq, InvMinusEmptyEq, UnionIdentityRight, UnionIdentityLeft, DisjointDestOnlyVar, UnionCommutative', UnionAssociative, UnionHdnShiftEq, StimesHdnShiftEq, StimesIsAction, StimesUnionDistributive, StimesIdentity, TimesCommutative, TimesAssociative, TimesIdentityRight, TimesIdentityLeft, hnames_CWkhnames_G, hnames_DisjointToDisjoint, DisjointTohdns_Disjoint, hdns_max_hdns_Disjoint, UnionIdentityRight, UnionIdentityLeft, HdnsSubsetCtxUnionBackward, HmaxSubset, MinusUnionDistributive, InvMinusUnionDistributive, hnamesMinusEq, hnamesInvMinusEq, hnamesFullShiftEq, hnamesEmpty, EmptyIshdns_DisjointRight, EmptyIshdns_DisjointLeft, MinusHdnShiftEq, InvMinusHdnShiftEq, CompatibleDestSingleton, IncompatibleVarDestOnly, MinusSingletonEq, InvMinusSingletonEq, FinAgeOnlyUnionBackward, FinAgeOnlyUnionForward, FinAgeOnlyStimesBackward, FinAgeOnlyStimesForward, FinAgeOnlyHdnShiftEquiv, EmptyIsFinAgeOnly, StimesSingletonVar, StimesSingletonDest, StimesSingletonHole, hnamesSingletonDestEq, hnamesSingletonHoleEq, ValidOnlySingletonVar, ValidOnlySingletonVar.

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

Lemma Ty_ectxs_DestOnlyD : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), ctx_DestOnly D.
Proof.
  intros * TyC. induction TyC.
  all: crush.
Qed.

Lemma Ty_ectxs_hnames_Disjoint : forall (C : ectxs) (D D' : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), hdns_Disjoint hnames©(C) hnamesᴳ(D') -> ctx_Disjoint D D'.
Proof.
  intros * TyC hdnsDisjoint. pose proof TyC as TyC'.
  apply hnames_CWkhnames_G in TyC.
  assert (hdns_Disjoint hnamesᴳ(D) hnamesᴳ( D')). { apply SubsetDisjoint with (H2 := hnames©(C)); assumption. }
  apply hnames_DisjointToDisjoint in H. assumption. apply Ty_ectxs_DestOnlyD in TyC'. assumption.
Qed.

Lemma Ty_ectxs_LinFinOnlyD : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), ctx_LinOnly D /\ ctx_FinAgeOnly D.
Proof.
  intros D C T U0 H. induction H.
  - split. apply EmptyIsLinOnly. apply EmptyIsFinAgeOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - hauto lq: on use: LinOnlyUnionEquiv, LinOnlyStimesBackward, FinAgeOnlyUnionBackward, FinAgeOnlyStimesBackward, LinOnlyWkValidOnly.
  - assert (ctx_LinOnly (¹↑ ᴳ· D1)).
      { hauto use: LinOnlyUnionEquiv, LinOnlyStimesForward, (mode_IsLinProof (Fin 1)). }
    assert (ctx_FinAgeOnly (¹↑ ᴳ· D1)).
      { hauto use: FinAgeOnlyUnionBackward, FinAgeOnlyStimesForward, (mode_IsFinAgeProof Lin 1). }
    assert (ctx_Disjoint (D1 ⨄ D2) (ᴳ-D3)).
      { apply (Ty_ectxs_hnames_Disjoint C (D1 ⨄ D2) (ᴳ-D3) (U ⧔ T') U0); tauto. }
    assert (ctx_Disjoint (¹↑ ᴳ· D1) D3).
      { sblast use: DisjointNestedLeftEquiv, DisjointMinusRightEquiv, DisjointStimesLeftEquiv. }
    rewrite LinOnlyUnionEquiv. repeat split. tauto. tauto. tauto. apply FinAgeOnlyUnionForward. repeat split. all:tauto.
Qed.

Lemma tSubLemma : forall (D1 D2 : ctx) (m : mode) (T U : type) (u : term) (x : var) (v : val), ctx_DestOnly D1 -> ctx_DestOnly D2 -> (D2 ⨄ ᴳ{ x : m ‗ T} ⊢ u : U) -> (D1 ⊢ ᵥ₎ v : T) -> (m ᴳ· D1 ⨄ D2 ⊢ u ᵗ[ x ≔ v] : U).
Proof. Admitted.

Lemma tSubLemma2 : forall (D11 D12 D2 : ctx) (m : mode) (T1 T2 U : type) (u : term) (x1 x2 : var) (v1 v2 : val), ctx_DestOnly D11 -> ctx_DestOnly D12 -> ctx_DestOnly D2 -> (ctx_Disjoint ᴳ{ x1 : m ‗ T1} ᴳ{ x2 : m ‗ T2}) -> (D2 ⨄ ᴳ{ x1 : m ‗ T1} ⨄ ᴳ{ x2 : m ‗ T2} ⊢ u : U) -> (D11 ⊢ ᵥ₎ v1 : T1) -> (D12 ⊢ ᵥ₎ v2 : T2) -> (m ᴳ· (D11 ⨄ D12) ⨄ D2 ⊢ u ᵗ[ x1 ≔ v1 ] ᵗ[ x2 ≔ v2 ] : U).
Proof. Admitted.

Lemma ectxsSubLemma : forall (D1 D2 D3 D : ctx) (h : hdn) (C : ectxs) (m n : mode) (T U U0 : type) (v : val),
  (forall x, D x = (ᴳ{+ h : m ⌊ U ⌋ n }) x) ->
  ctx_Disjoint D1 D2 ->
  ctx_Disjoint D1 D3 ->
  hdns_Disjoint hnames©(C) hnamesᴳ(ᴳ- D3) ->
  ctx_DestOnly D1 ->
  ctx_DestOnly D2 ->
  ctx_DestOnly D3 ->
  ctx_LinOnly D3 ->
  ctx_FinAgeOnly D3 ->
  ctx_ValidOnly D3 ->
  ctx_Disjoint D1 D ->
  ctx_Disjoint D2 D ->
  ctx_Disjoint D3 D ->
 D1 ⨄ (m · n) ᴳ· D2 ⨄ D ⊣ C : T ↣ U0 ->
 D2 ⨄ ᴳ- D3 ⫦ v : U ->
 D1 ⨄ m ᴳ· ᴳ-⁻¹ (n ᴳ· ᴳ- D3) ⊣ C ©️[ h ≔ hnamesᴳ(ᴳ- D3) ‗ v ] : T ↣ U0.
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
      rewrite <- Eqmm0 in *. clear Eqmm0. clear m0. rename P1 into D1, P2 into D2. rename Tyt into TyApp, Tyt0 into Tyt, T into U, T0 into T.
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
      assert ((¹↑ ᴳ· D11 ⨄ D13) ᴳ[hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)] ⊢ ᵥ₎ v1 ᵛ[hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)] : T) as Tyt1.
        { apply Ty_term_Val. apply TyR_v_hdn_shift. all: crush. }
      constructor 1 with (D := ¹↑ ᴳ· (D2 ⨄ D11 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)]) ⨄ D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)]) (T := T') (t := t' ᵗ[ x ≔ v1 ᵛ[hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)] ]); swap 3 4;
        assert (D11 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)] = D11) as D11Eq by ( apply DisjointHdnShiftEq; crush );
        assert (D12 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)] = D12) as D12Eq by ( apply DisjointHdnShiftEq; crush );
        rewrite D11Eq.
        { assert (ctx_ValidOnly (¹↑ ᴳ· (D2 ⨄ D11))).
          { apply ValidOnlyStimesForward. split.
            - rewrite (UnionCommutative (D11 ⨄ D12) D2) in ValidOnlyD.
              rewrite UnionAssociative in ValidOnlyD.
              apply ValidOnlyUnionBackward in ValidOnlyD.
              tauto.
            - exact (mode_IsValidProof (Lin, Fin 1)).
          }
          assert (ctx_ValidOnly (D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])).
          { apply ValidOnlyHdnShiftEquiv; tauto. }
          assert (ctx_Disjoint (¹↑ ᴳ· (D2 ⨄ D11)) (D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])).
          { apply DisjointStimesLeftEquiv.
            assert (ctx_Disjoint (D2 ⨄ D11) (D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])). {
          {  apply DisjointNestedLeftEquiv. assert (HdnsM.Subset hnamesᴳ(D11 ⨄ D12 ⨄ D2) hnames©(C)).
              { apply hnames_CWkhnames_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HdnsM.Subset hnamesᴳ(D2) hnames©(C)).
              { apply HdnsSubsetCtxUnionBackward with (G := D11 ⨄ D12) (G' := D2) (H := hnames©(C)). tauto. }
              assert (ʰmax(hnamesᴳ(D2)) <= ʰmax(hnames©(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2) (hnamesᴳ(D13) ᴴ⩲ (ʰmax(hnames©(C)) + 1))).
              { apply hdns_max_hdns_Disjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])).
              { unfold hdns_Disjoint. rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
            { assert (HdnsM.Subset hnamesᴳ(D11) hnames©(C)).
              { apply HdnsSubsetCtxUnionBackward in H1. destruct H1. apply HdnsSubsetCtxUnionBackward in H1. tauto. }
              assert (ʰmax(hnamesᴳ(D11)) <= ʰmax(hnames©(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11) (hnamesᴳ(D13) ᴴ⩲ (ʰmax(hnames©(C)) + 1))).
              { apply hdns_max_hdns_Disjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])).
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
        { assert (¹↑ ᴳ· (D2 ⨄ D11) ⨄ D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)] = (¹ν ᴳ· (¹↑ ᴳ· D11 ⨄ D13) ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)]) ⨄ ¹↑ ᴳ· D2) as ctxEq.
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
      constructor 19 with (D1 := D2 ⨄ D11) (D3 := D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)]) (C := C) (v2 := v2 ᵛ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)]) (T' := T') (U0 := U0) (U := U) (D2 :=
      D12).
        { apply LinOnlyUnionEquiv. rewrite <- UnionAssociative. rewrite UnionCommutative. tauto. }
        {
          {  apply DisjointNestedLeftEquiv. assert (HdnsM.Subset hnamesᴳ(D11 ⨄ D12 ⨄ D2) hnames©(C)).
              { apply hnames_CWkhnames_G with (U0 := U0) (T := U ⧔ T'). tauto. } split.
            { assert (HdnsM.Subset hnamesᴳ(D2) hnames©(C)).
              { apply HdnsSubsetCtxUnionBackward with (G := D11 ⨄ D12) (G' := D2) (H := hnames©(C)). tauto. }
              assert (ʰmax(hnamesᴳ(D2)) <= ʰmax(hnames©(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2) (hnamesᴳ(D13) ᴴ⩲ (ʰmax(hnames©(C)) + 1))).
              { apply hdns_max_hdns_Disjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hdns_Disjoint hnamesᴳ(D2)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
            { assert (HdnsM.Subset hnamesᴳ(D11) hnames©(C)).
              { apply HdnsSubsetCtxUnionBackward in H. destruct H. apply HdnsSubsetCtxUnionBackward in H. tauto. }
              assert (ʰmax(hnamesᴳ(D11)) <= ʰmax(hnames©(C))).
              { apply HmaxSubset. tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11) (hnamesᴳ(D13) ᴴ⩲ (ʰmax(hnames©(C)) + 1))).
              { apply hdns_max_hdns_Disjoint; rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; tauto. }
              assert (hdns_Disjoint hnamesᴳ(D11)  hnamesᴳ( D13 ᴳ[ hnamesᴳ( ᴳ- D13) ⩲ (ʰmax(hnames©(C)) + 1)])).
              { rewrite hnamesMinusEq. rewrite hnamesFullShiftEq. tauto. }
              apply hnames_DisjointToDisjoint; crush.
            }
          } } { crush. } { crush. } { crush. } { crush. } { crush. } { crush. } { rewrite UnionCommutative in TyC. rewrite UnionAssociative in TyC. tauto. }
          { rewrite <- D12Eq. rewrite <- MinusHdnShiftEq. rewrite <- UnionHdnShiftEq. apply TyR_v_hdn_shift. tauto.  }
          { rewrite <- MinusHdnShiftEq. rewrite hnamesFullShiftEq. apply hdns_max_hdns_Disjoint with (h' := ʰmax(hnames©(C)) + 1); rewrite Nat.add_comm; unfold lt, plus; apply le_n_S; reflexivity. }
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
          - intros n b. unfold ctx_singleton. rewrite singleton_mapsto. rewrite eq_sigT_iff_eq_dep.
            intros []. cbv. tauto.
          - intros n tyb. unfold ctx_singleton. rewrite singleton_mapsto. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (tyb = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n tyb. unfold ctx_singleton. rewrite singleton_mapsto. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
          assert (tyb = ₊ ¹ν ⌊ U ⌋ ¹ν); subst. { apply inj_pair2_eq_dec. exact name_eq_dec. apply eq_sym; tauto. }
            constructor.
          - intros n tyb. unfold ctx_singleton. rewrite singleton_mapsto. intros H. remember H as H'; clear HeqH'. apply eq_sigT_fst in H; subst.
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
        { apply Ty_term_Val. assert (hnamesᴳ( ᴳ- ᴳ{}) = hdns_from_list nil). { crush. } rewrite <- H. apply TyR_val_A; swap 1 11; swap 2 10.
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
      assert (ᴳ{} ⊣ C ©️[ h ≔ hdns_from_list nil ‗ ᵛ()] : ① ↣ U0).
        { assert (ᴳ{} ⨄ ¹ν ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- ᴳ{}))) = ᴳ{}) as e1. { crush. }
          rewrite <- e1.
          assert (hnamesᴳ(ᴳ- ᴳ{}) = hdns_from_list nil) as e2. { crush. }
          rewrite <- e2.
          assert (ᴳ{} ⨄ (¹ν · n) ᴳ· ᴳ{} ⨄ D = D) as e3. { crush. }
          rewrite <- e3 in TyC.
          apply ectxsSubLemma with (D2 := ᴳ{}) (U := ①) (D := D); swap 1 15; swap 2 15.
          { rewrite <- UnionIdentityLeft. rewrite MinusEmptyEq. apply TyR_val_U. }
          { apply CompatibleLinFinOnlyIsExact; tauto. }
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
      assert (ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ n} ⊣ C ©️[ h ≔ ᴴ{ h' + 1} ‗ Inl ᵛ- (h' + 1)] : ⌊ T1 ⌋ n ↣ U0).
        { assert (ᴳ{} ⨄ ¹ν ᴳ· (ᴳ-⁻¹ (n ᴳ· (ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν }))) = ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ n }) as e1.
            { rewrite <- UnionIdentityLeft. rewrite <- StimesIdentity. rewrite MinusSingletonEq. rewrite StimesSingletonHole. rewrite InvMinusSingletonEq. rewrite TimesIdentityLeft. tauto. }
          rewrite <- e1.
          assert (hnamesᴳ(ᴳ- ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) = ᴴ{ h' + 1}) as e2. { crush. }
          rewrite <- e2.
          assert (ᴳ{} ⨄ (¹ν · n) ᴳ· ᴳ{} ⨄ D = D) as e3. { crush. } rewrite <- e3 in TyC.
          apply ectxsSubLemma with (D2 := ᴳ{}) (D3 := ᴳ{+ (h' + 1) : ¹ν ⌊ T1 ⌋ ¹ν}) (U := T1 ⨁ T2) (D := D); swap 1 15; swap 2 15.
          { rewrite <- UnionIdentityLeft. rewrite MinusSingletonEq. apply TyR_val_L. constructor. }
          { apply CompatibleLinFinOnlyIsExact; tauto. }
          give_up.
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
  specialize (DestOnlyD (ʰ h)). unfold ctx_DestOnly, ctx_singleton in DestOnlyD. specialize (DestOnlyD (₋ T ‗ ¹ν)). rewrite singleton_mapsto in DestOnlyD. sfirstorder.
Qed.

Lemma term_NotVal_dec : forall (t : term), {exists v, t = ᵥ₎ v} + {term_NotVal t}.
Proof.
  intros t. destruct t.
  { left. exists v; tauto. }
  all: right; congruence.
Qed.

Theorem Progress : forall (C : ectxs) (t : term) (U0 : type), ⊢ C ʲ[t] : U0 -> ((exists v, t = ᵥ₎ v) -> C <> ©️⬜) -> exists (C' : ectxs) (t' : term), C ʲ[t] ⟶ C' ʲ[t'].
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
      exists (C ∘ hnamesᴳ( ᴳ- D3) ᴴ⩲ (ʰmax(hnames©(C)) + 1) ᵒᵖ⟨ v2 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ (ʰmax(hnames©(C)) + 1)] ❟⬜), (t' ᵗ[x ≔ v1 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ (ʰmax(hnames©(C)) + 1)]]). constructor; tauto.
    * exists (C ∘ ⬜≻map x ⟼ t'), t. constructor; tauto.
  - rename Tyt into TyToA. destruct (term_NotVal_dec u).
    * destruct e; subst. rename x into v2. exists C, (ᵥ₎ HdnsM.empty ⟨ v2 ❟ ᵛ() ⟩ ). constructor.
    * exists (C ∘ to⧔⬜), u. constructor; tauto.
  - rename Tyt into TyToA, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : T ⧔ ① ‗ ¹ν}) (h := h) (T := T ⧔ ①); tauto. }
      inversion TyRv1; subst. { assert (ctx_DestOnly (¹↑ ᴳ· D1 ⨄ D3)). { crush. } exfalso. apply DestOnlyValHole with (D := (¹↑ ᴳ· D1 ⨄ D3)) (h := h) (T := ①). all:tauto. }
      assert (D3 = ᴳ{}) as EmptyD3. { apply eq_sym in H2. apply (app_eq_nil (support D1) (support D3)) in H2. destruct H2. apply empty_support_Empty in H, H2. tauto. } subst. rewrite hnamesMinusEq, hnamesEmpty.
      exists C, (ᵥ₎ v2). constructor.
    * exists (C ∘ from⧔⬜), t. constructor; tauto.
  - rename Tyt into TyAlloc. exists C, (ᵥ₎ ᴴ{ 1 } ⟨ ᵛ-1 ❟ ᵛ+1 ⟩ ). constructor.
  - rename Tyt into TyFillU, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ ① ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ① ⌋ n); tauto. }
      exists (C ©️[ h ≔ HdnsM.empty ‗ ᵛ()]), (ᵥ₎ ᵛ()). constructor.
    * exists (C ∘ ⬜⨞()), t. constructor; tauto.
  - rename Tyt into TyFillL, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ Inl ᵛ- (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ+ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inl), t. constructor; tauto.
  - rename Tyt into TyFillR, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T1 ⨁ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨁ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ Inr ᵛ- (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ+ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞Inr), t. constructor; tauto.
  - rename Tyt into TyFillP, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T1 ⨂ T2 ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T1 ⨂ T2 ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1 , ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 2} ‗ ᵛ( ᵛ- (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1), ᵛ- (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 2))]), (ᵥ₎ ᵛ( ᵛ+ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1), ᵛ+ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 2))). constructor; tauto.
    * exists (C ∘ ⬜⨞(,)), t. constructor; tauto.
  - rename Tyt into TyFillE, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ ! n' ⁔ T ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ ! n' ⁔ T ⌋ n); tauto. }
    exists (C ©️[ h ≔ ᴴ{ ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1} ‗ ᴇ n' ⁔ ᵛ- (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)]), (ᵥ₎ ᵛ+ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1 + 1)). constructor; tauto.
    * exists (C ∘ ⬜⨞ᴇ n'), t. constructor; tauto.
  - rename Tyt into TyFillF, Tyt0 into Tyt, t0 into t. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x0 into v. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ T ⁔ m → U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ T ⁔ m → U ⌋ n); tauto. }
    exists (C ©️[ h ≔ HdnsM.empty ‗ λᵛ x ⁔ m ⟼ u ]), (ᵥ₎ ᵛ()). constructor; tauto.
    * exists (C ∘ ⬜⨞(λ x ⁔ m ⟼ u)), t. constructor; tauto.
  - rename Tyt into TyFillC, Tyt0 into Tyt, t0 into t, P1 into D1, P2 into D2. destruct (term_NotVal_dec t).
    * destruct e; subst. rename x into v. destruct (term_NotVal_dec t').
      + destruct e; subst. rename x into v'. inversion Tyt; subst. inversion TyRv; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h : ⌊ U ⌋ n ‗ ¹ν}) (h := h) (T := ⌊ U ⌋ n); tauto. } rename H1 into DestOnlyD'. inversion Tytp; subst. rename TyRv0 into TyRvp. inversion TyRvp; subst. { exfalso. apply DestOnlyValHole with (D := ᴳ{- h0 : U ⧔ T ‗ ¹ν}) (h := h0) (T := U ⧔ T); tauto. } rename D1 into D', D0 into D1, D3 into D2, D4 into D3.
      exists
        ( C ©️[ h ≔ hnamesᴳ( ᴳ- D3) ᴴ⩲ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1) ‗  v2 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1)] ] ),
        (ᵥ₎ v1 ᵛ[hnamesᴳ( ᴳ- D3) ⩲ (ʰmax( hnames©(C) ∪ ᴴ{ h}) + 1)]).
      constructor; tauto.
      + exists (C ∘ v ⨞·⬜), t'. constructor; tauto.
    * exists (C ∘ ⬜⨞· t'), t. constructor; tauto.
Qed.

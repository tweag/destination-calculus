Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.Notations.
Require Import Dest.ExtNat.
Require Import Coq.Program.Equality.
Require Import Dest.Finitely.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Require Coq.Program.Basics.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Compare_dec.
Require Import Arith.
Require Import Lia.

(*----------------------------------------------------------------------------*)
(* Small, general lemmas that don't relate to something specific *)
(*----------------------------------------------------------------------------*)
Lemma option_eta : forall A (o:option A), match o with Some x => Some x | None => None end = o.
Proof.
  hauto lq: on.
Qed.

Lemma n_plus_n0_eq_0_implies_n0_eq_0 : forall n n0 : nat,
  n + n0 = 0 -> n0 = 0.
Proof.
  intros n n0 H.
  apply Nat.eq_add_0 in H. (* Definition of zero *)
  destruct H. tauto.
Qed.

Theorem func_eq_on_arg : forall (n : name) (f g : T name binding_type_of), f = g -> f n = g n.
Proof.
  intros * H.
  (* Apply the hypothesis H to the argument x *)
  rewrite H.
  (* This simplifies the goal to g x = g x, which is trivial *)
  reflexivity.
Qed.

Lemma not_lt_le : forall (x y : nat),
  ~ x < y -> y <= x.
Proof.
  sfirstorder.
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

(* TODO: revisit if stuff breaks *)
Lemma dom_nil_is_empty : forall (G : ctx), dom G = nil -> G = ᴳ{}.
Proof.
  apply Finitely.dom_nil_is_empty.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* HNames.t is a MSetList of hole names. *)
(* We sometimes need to iterate on the names contained in a HNames.t, and for that, we prove several correspondances between the domain of the MSetList (i.e. a list) and the MSetList itself. *)
(*----------------------------------------------------------------------------*)
Lemma hnames_dom_spec : forall (l:list name) h, HNames.In h (hnames_dom l) <-> List.In (ʰ h) l.
Proof.
  induction l as [|[xx|xh] l ih].
  - cbn. sauto q: on.
  - cbn. hauto lq: on.
  - hauto q: on use: HNames.add_spec.
Qed.

Lemma hnames_spec : forall (G : ctx) (h : hname), HNames.In h (hnamesᴳ(G)) <-> exists x, G (name_DH h) = Some x.
Proof.
  intros *. split.
  - intros Hin. unfold hnames_ctx, hnames_dom in Hin. remember (dom(G)) as l in Hin. assert (ListSubset l (dom G)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    * inversion Hin.
    * rename a into n, l into ns.
      rewrite ListSubset_cons_iff in H; destruct H; rewrite dom_spec in H; rewrite In_iff_exists_Some in H. destruct ((fix hnames_dom (dom : list name) : HNames.t := match dom with
| nil => HNames.empty
| cons (ˣ _) xs => hnames_dom xs
| cons (ʰ h) xs => HNames.add h (hnames_dom xs)
end) ns).
      destruct n.
      + specialize (IHl Hin H0). assumption.
      + destruct (Nat.eq_dec h h0).
        { rewrite e in *; assumption. }
        { assert (HNames.In h {| HNames.this := this; HNames.is_ok := is_ok |}).
          { rewrite HNames.add_spec in Hin. destruct Hin. congruence. assumption. }
          specialize (IHl H1 H0). assumption.
        }
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. apply dom_spec in Hin. unfold hnames_ctx, hnames_dom. remember (dom(G)) as l. assert (ListSubset l (dom G)). { rewrite Heql. apply ListSubset_refl. } clear Heql. induction l.
    * inversion Hin.
    * rename a into n, l into ns.
      destruct n.
      { rewrite ListSubset_cons_iff in H; destruct H.
        assert (List.In (ʰ h) ns).
        { destruct Hin. congruence. assumption. }
        specialize (IHl H1 H0). assumption.
      }
      { destruct (Nat.eq_dec h h0).
        { rewrite e in *. apply HNames.add_spec. left. congruence. }
        { assert (List.In (ʰ h) ns).
          { destruct Hin. inversion H0. congruence. assumption. }
          apply ListSubset_cons_iff in H; destruct H. specialize (IHl H0 H1). apply HNames.add_spec. right. assumption.
        }
      }
Qed.

Lemma in_hnames : forall (C:ctx) h, HNames.In h (hnamesᴳ( C)) <-> Finitely.In (ʰ h) C.
Proof.
  hauto lq: on unfold: hnames_ctx use: hnames_dom_spec, Finitely.dom_spec.
Qed.

Lemma InA_eq_eq : forall A (x:A) l, SetoidList.InA eq x l <-> List.In x l.
Proof.
  intros *. rewrite SetoidList.InA_alt.
  hauto lq: on.
Qed.

Lemma in_hnames_dom : forall h G, List.In (ʰ h) (dom G) <-> List.In h (HNames.elements (hnamesᴳ( G))).
Proof.
  intros *. unfold hnames_ctx, hnames_dom.
  rewrite <- InA_eq_eq with (x:=h). rewrite HNames.elements_spec1.
  induction (dom G) as [|h' G_elts].
  - compute. sauto lq: on.
  - cbn. split.
    * intros [-> | h_in].
      + rewrite HNames.add_spec. sfirstorder.
      + destruct h' as [x'|h'].
        { sfirstorder. }
        rewrite HNames.add_spec. sfirstorder.
    * destruct h' as [x'|h'].
      { sfirstorder. }
      rewrite HNames.add_spec.
      sfirstorder.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* We use max(H) + 1 as a shift value for H to generate fresh hole names. We need a few lemmas to prove that, indeed, the generated names are fresh. *)
(*----------------------------------------------------------------------------*)
Lemma gt_S_max : forall h H, HNames.mem h H = true -> h < maxᴴ(H) + 1.
Proof.
  intros * h_H. unfold hname_max.
  destruct (HNames.max_elt H) eqn:h_max_elt.
  2:{ apply HNames.max_elt_spec3 in h_max_elt. unfold HNames.Empty in *.
      sfirstorder use: HNamesFacts.mem_iff. }
  apply HNames.max_elt_spec2  with (y:=h) in h_max_elt.
  - sfirstorder.
  - sfirstorder use: HNamesFacts.mem_iff.
Qed.

Lemma gt_max_not_in : forall (h : HNames.elt) (H : HNames.t), maxᴴ(H) < h -> ~(HNames.In h H).
Proof.
  intros * h_max h_in.
  rewrite <- HNames.mem_spec in h_in.
  apply gt_S_max in h_in.
  lia.
Qed.

Lemma different_than_gt_max : forall (h h1 h2 : hname) (H H': HNames.t), (0 < h1) -> HNames.In h H' -> ʰ (maxᴴ( H ∪ H') + h1 + h2) <> ʰ h.
Proof.
  intros *.
  intros h1notnull inhH' contra. injection contra. intros contra'. unfold hname_max in *. destruct (HNames.max_elt (H ∪ H')) eqn:edestr. 2:{ apply HNames.max_elt_spec3 in edestr. unfold HNames.Empty in edestr. specialize (edestr h). assert (HNames.In h (H ∪ H')). apply HNames.union_spec. right. assumption. contradiction. } apply HNames.max_elt_spec2 with (y := h) in edestr. rewrite <- contra' in edestr. contradiction edestr. rewrite <- Nat.add_assoc. lia. apply HNames.union_spec. right. assumption.
Qed.

Lemma hname_max_list_max : forall H, maxᴴ( H) = list_max (HNames.elements H).
Proof.
  intros *.
  assert (forall n, maxᴴ( H) <= n <-> list_max (HNames.elements H) <= n).
  2:{ sauto l: on. }
  intros n.
  rewrite List.list_max_le. rewrite Forall_forall. unfold hname_max.
  destruct (HNames.max_elt H) as [h'|] eqn:h_max.
  - split.
    * intros h_le h h_in. rewrite <- InA_eq_eq, HNames.elements_spec1 in h_in.
      sfirstorder use: HNames.max_elt_spec2.
    * intros h_le. apply h_le.
      rewrite <- InA_eq_eq, HNames.elements_spec1.
      sfirstorder use: HNames.max_elt_spec1.
  - hauto l: on use: HNames.max_elt_spec3, InA_eq_eq, HNames.elements_spec1 unfold: HNames.Empty.
Qed.

Lemma gt_list_max_not_in : forall l x, list_max l < x -> ~List.In x l.
Proof.
  intros * h_max h_in.
  induction l.
  - sfirstorder.
  - simpl in *.
    destruct h_in as [->|h_in].
    * lia.
    * hauto l: on.
Qed.

Lemma HdRel_lt_not_in : forall l x, Sorted.HdRel lt x l -> Sorted.Sorted lt l -> ~List.In x l.
Proof.
  intros * h h_sorted.
  induction l as [|y l ih].
  - cbn. sfirstorder.
  - cbn. apply Sorted.HdRel_inv in h.
    intros [-> | h_in].
    * lia.
    * apply Sorted.Sorted_inv in h_sorted.
      sfirstorder.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Actually we implement hole renaming as permutations (see Permutation.v). That's because our typing context type is a total function from names to optionals, instead of being a real collection of bindings. So we cannot easily iterate on the elements of the typing context and shift the names, instead we must map old names to new ones. Doing so with permutations make it easier to prove properties about the support of the function representing the typing context.
  Of course, we need a few constraint on holes names present in a typing context if we want permutations to behave the same as our hole name shift/cshift, which is described in the paper as just increasing the value of (some) hole names (represented by naturals) by a given natural. *)
(* pre_shift and ctx_shift are defined in destination_calculus_ott.v *)
(*----------------------------------------------------------------------------*)
Lemma pre_cshift_surjective : forall p x, exists x', pre_shift p x' = x.
Proof.
  intros *. unfold pre_shift.
  destruct x as [xx|h].
  { exists (ˣ xx). reflexivity. }
  eexists (ʰ _). f_equal.
  eapply Permutation.pre_inverse.
Qed.

Lemma shift_post_inverse : forall p G, ctx_shift (List.rev p) (ctx_shift p G) = G.
Proof.
  intros *.
  apply ext_eq. intros [xx|xh].
  {  cbn. unfold Fun.map. cbn. hauto lq: on. }
  cbn. unfold Fun.map. cbn. rewrite Permutation.pre_inverse.
  hauto lq: on.
Qed.

Definition fixes (p:Permutation.T) (l:list name) : Prop :=
  forall xh, List.In (ʰ xh) l -> Permutation.sem p xh = xh.

Lemma fixes_inverse_fixes : forall p l, fixes p l -> fixes (List.rev p) l.
Proof.
  intros *. unfold fixes. intros h xh h_in.
  apply Permutation.eqn_inverse.
  sfirstorder.
Qed.

Lemma fixes_untouched : forall p l, (forall t, List.In t p -> ~List.In (ʰ t.(Permutation.Transposition.from)) l /\ ~List.In (ʰ t.(Permutation.Transposition.to)) l) -> fixes p l.
Proof.
  intros *. induction p as [|t p ih].
  - intros _. sfirstorder.
  - intros h. cbn in *.
    unfold fixes. intros xh. cbn. fold (Permutation.sem p xh). intros h_in.
    rewrite ih.
    2:{ sfirstorder. }
    2:{ trivial. }
    generalize (h t (or_introl eq_refl)). intros [h_from h_to].
    destruct t as [from to]. unfold Permutation.Transposition.sem. cbn in *.
    hauto q: on.
Qed.

Lemma shift_pre_inverse : forall p G, ctx_shift p (ctx_shift (List.rev p) G) = G.
Proof.
  intros *.
  apply ext_eq. intros [xx|xh].
  {  cbn. unfold Fun.map. cbn. hauto lq: on. }
  cbn. unfold Fun.map. cbn. rewrite Permutation.post_inverse.
  hauto lq: on.
Qed.

Lemma In_shift : forall p G x, In x (ctx_shift p G) <-> In (pre_shift p x) G.
Proof.
  intros *. unfold ctx_shift.
  rewrite In_map_iff, In_precomp_iff.
  reflexivity.
Qed.

Lemma perm_support_fixes : forall (p:Permutation.T) (l:list name) (C:ctx), Finitely.Fun.Support l C -> fixes p l -> ctx_shift p C = C.
Proof.
  intros * h_supp h_fixes. unfold ctx_shift.
  apply support_ext_eq with (l:=l).
  { unfold Fun.Support. cbn. intros [xx|xh] b.
    - unfold Fun.map. cbn. rewrite option_eta.
      sfirstorder.
    - unfold Fun.map. cbn. rewrite option_eta.
      intros h.
      assert (List.In (ʰ Permutation.sem p xh) l) as h'.
      { sfirstorder. }
      rewrite <- (Permutation.post_inverse p xh).
      hauto l: on use: fixes_inverse_fixes.
  }
  { trivial. }
  intros [xx|xh]. all: cbn.
  - intros _. compute. hauto lq: on.
  - intros h. unfold Fun.map. cbn. rewrite option_eta.
    rewrite h_fixes.
    + trivial.
    + trivial.
Qed.

Lemma perm_support_fixes' : forall (p:Permutation.T) (C:ctx), fixes p (Finitely.dom C) -> ctx_shift p C = C.
Proof.
  intros *.
  apply perm_support_fixes.
  apply Finitely.Support_dom.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* We also need a few more technical lemmas about (conditional) name shift before we can state the main properties of conditional name shift that we need for the type safety proof. *)
(*----------------------------------------------------------------------------*)
Lemma merge_with_cshift :
  forall (G1 G2 : ctx) H h' (f_var : binding_var -> binding_var -> binding_var) (f_dh : binding_dh -> binding_dh -> binding_dh) ,
    (merge_with (fsimple (fun t => t -> t -> t) f_var f_dh) G1 G2) ᴳ[ H⩲h' ]
    = merge_with (fsimple (fun t => t -> t -> t) f_var f_dh) (G1 ᴳ[ H⩲h' ]) (G2 ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_cshift, ctx_shift.
  apply ext_eq. intros [xx|xh]. all: cbn.
  { compute. hauto lq: on. }
  unfold Fun.map, Fun.merge. cbn. rewrite !option_eta.
  sfirstorder.
Qed.

Lemma map_cshift : forall G H h' (f_var : binding_var -> binding_var) (f_dh : binding_dh -> binding_dh),
    (map (fsimple (fun t => t -> t) f_var f_dh) G) ᴳ[ H⩲h' ]
    = map (fsimple (fun t => t -> t) f_var f_dh) (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ctx_cshift, ctx_shift.
  apply ext_eq. intros [xx|xh]. all: cbn.
  { compute. hauto lq: on. }
  unfold Fun.map, Fun.merge. cbn. rewrite !option_eta.
  sfirstorder.
Qed.

Lemma shift_spec : forall (h : HNames.elt) (H : HNames.t) (h' : nat), HNames.In h (H ᴴ⩲ h') <-> (exists h'' : HNames.elt, HNames.In h'' H /\ h = h'' + h').
Proof.
  assert (forall (h : HNames.elt) (H : HNames.t) (h' : nat) , HNames.In h (H ᴴ⩲ h') <-> (exists h'' : HNames.elt , List.In h'' (List.rev (HNames.elements H)) /\ h = h'' + h')) as main.
  { intros *. unfold hnames_shift.
    rewrite HNames.fold_spec, <- List.fold_left_rev_right.
    induction (rev (HNames.elements H)) as [ | h'' elems ih ].
    - cbn. sauto q: on.
    - cbn. rewrite HNames.add_spec. rewrite ih. clear ih.
      sfirstorder.
  }
  (* Needs some wrangling a bit because rewrites don't work well under exists. *)
  intros *. split.
  - intros hh. apply main in hh. destruct hh as [h'' hh].
    exists h''.
    sauto use: in_rev.
  - intros [h'' hh].
    apply main. exists h''. rewrite <- List.in_rev, <- InA_eq_eq, HNames.elements_spec1.
    sfirstorder.
Qed.

Lemma in_cshift : forall G h' H h, Finitely.In (ʰ h) (G ᴳ[ H ⩲ h' ]) <-> Finitely.In (ʰ Permutation.sem (List.rev (shift_perm H h')) h) G.
Proof.
  intros *. unfold ctx_cshift, ctx_shift, Finitely.In, Fun.In. cbn. unfold Fun.map. cbn.
  rewrite option_eta.
  reflexivity.
Qed.

(* This is a technical lemma which appears in the proof of other shift_perm_spec* lemmas. *)
Lemma shift_perm_spec3' : forall  H (h' h: hname), Sorted.Sorted lt H -> list_max H < h' -> ~List.In h H -> (forall h'', h''+h' = h -> ~List.In h'' H) -> fold_right Permutation.Transposition.sem h (rev (List.map (shift_one h') H)) = h.
Proof.
  intros * h_sorted h_max h_nin h_nin'.
  induction H as [|h'' H' ih].
  - cbn. reflexivity.
  - cbn. rewrite List.fold_right_app. cbn. unfold shift_one at 1, Permutation.Transposition.sem at 2. cbn.
    assert (h <> h'') as h_ne.
    { cbn in h_nin. clear -h_nin. sfirstorder. }
    destruct (HNamesFacts.eq_dec h h'') as [-> | _].
    1:{ sfirstorder. }
    assert (h <> h''+h') as h_ne'.
    { hauto lq: on. }
    destruct (HNamesFacts.eq_dec h (h'' + h')) as [->|_].
    1:{ sfirstorder. }
    apply ih.
    all: qblast.
Qed.

Lemma shift_perm_spec3 : forall  H (h' h: hname), maxᴴ( H) < h' -> ~HNames.In h H -> (forall h'', h''+h' = h -> ~HNames.In h'' H) -> Permutation.sem (rev (shift_perm H h')) h = h.
Proof.
  assert (forall  H (h' h: hname), list_max (HNames.elements H) < h' -> ~List.In h (HNames.elements H) -> (forall h'', h''+h' = h -> ~List.In h'' (HNames.elements H)) -> Permutation.sem (rev (shift_perm H h')) h = h).
  2:{ hauto l: on use: hname_max_list_max, InA_eq_eq, HNames.elements_spec1. }
  intros * h_max h_nin h_nin'. unfold shift_perm.
  generalize (HNames.elements_spec2 H). intros h_sorted.
  apply shift_perm_spec3'.
  all: trivial.
Qed.

Lemma shift_perm_spec1 : forall  H (h' h: hname), maxᴴ( H) < h' -> HNames.In h H -> Permutation.sem (rev (shift_perm H h')) h = h+h'.
Proof.
  intros * h_max h_in.
  unfold shift_perm. rewrite hname_max_list_max in h_max. rewrite <- HNames.elements_spec1, InA_eq_eq in h_in.
  generalize (HNames.elements_spec2 H). intros h_sorted.
  induction (HNames.elements H) as [|h'' H' ih].
  - cbn in *. lia.
  - cbn in *.
    rewrite fold_right_app. cbn.
    destruct h_in as [-> | h_in].
    * unfold shift_one at 1, Permutation.Transposition.sem at 2. cbn.
      destruct (HNamesFacts.eq_dec h h) as [_|h_ne].
      2:{ congruence. }
      fold (Permutation.sem (rev (shift_perm H h')) (h+h')).
      apply shift_perm_spec3'.
      + sauto lq: on.
      + sfirstorder unfold: list_max.
      + assert (list_max H' < h+h') as h_more_max.
        { fold (list_max H') in h_max. lia. }
        sfirstorder use: gt_list_max_not_in.
      + intros h'' h_h''.
        assert (h'' = h) as ->.
        { lia. }
        clear h_h''.
        apply Sorted.Sorted_inv in h_sorted. destruct h_sorted as [h_sorted h_lt].
        sfirstorder use: HdRel_lt_not_in.
   * unfold shift_one at 1, Permutation.Transposition.sem at 2. cbn. fold (list_max H') in h_max.
     assert (~List.In h'' H') as h__nin.
     { apply Sorted.Sorted_inv in h_sorted.
       sfirstorder use: HdRel_lt_not_in. }
     assert (h <> h'') as h_ne.
     { intros <-. sfirstorder. }
     destruct (HNamesFacts.eq_dec h h'') as [<- | _].
     1:{ congruence. }
     assert (~List.In (h''+h') H') as h_nin'.
     { apply gt_list_max_not_in.
       lia. }
     assert (h <> h'' + h') as h_ne'.
     { intros ->. sfirstorder. }
     destruct (HNamesFacts.eq_dec h (h'' + h')) as [-> | _].
     1:{ congruence. }
     apply ih.
      + lia.
      + assumption.
      + hauto lq: on use: Sorted.Sorted_inv.
Qed.

Lemma shift_perm_spec2 : forall  H (h' h: hname), maxᴴ( H) < h' -> HNames.In h H -> Permutation.sem (rev (shift_perm H h')) (h+h') = h.
Proof.
  intros * h_max h_in.
  unfold shift_perm. rewrite hname_max_list_max in h_max. rewrite <- HNames.elements_spec1, InA_eq_eq in h_in.
  generalize (HNames.elements_spec2 H). intros h_sorted.
  induction (HNames.elements H) as [|h'' H' ih].
  - cbn in *. lia.
  - cbn in *.
    rewrite fold_right_app. cbn.
    destruct h_in as [-> | h_in].
    * unfold shift_one at 1, Permutation.Transposition.sem at 2. cbn.
      destruct (HNamesFacts.eq_dec (h+h') h) as [e|h_ne].
      { lia. }
      destruct (HNamesFacts.eq_dec (h+h') (h+h')) as [_|h_ne'].
      2:{ lia. }
      apply shift_perm_spec3'.
      + sauto lq: on.
      + sfirstorder unfold: list_max.
      + hauto lq: on use: Sorted.Sorted_inv, HdRel_lt_not_in.
      + intros h'' <-.
        lia.
    * unfold shift_one at 1, Permutation.Transposition.sem at 2. cbn. fold (list_max H') in h_max.
      destruct (HNamesFacts.eq_dec (h + h') h'') as [e|h_ne].
      1:{ lia. }
      destruct (HNamesFacts.eq_dec (h + h') (h'' + h')) as [e|h_ne'].
      1:{ apply Sorted.Sorted_inv in h_sorted.
          assert (~List.In h'' H').
          { sfirstorder use: HdRel_lt_not_in. }
          assert (h=h'') as <-.
          { lia. }
          sfirstorder. }
      apply ih.
      + lia.
      + assumption.
      + sauto lq: on.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties and predicates on modes *)
(*----------------------------------------------------------------------------*)
Lemma IsValid_times_backward : forall (m1 m2 : mode), IsValid (m1 · m2) -> IsValid m1 /\ IsValid m2.
Proof.
  intros * Validm1m2. split.
  - destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion Validm1m2; try constructor.
  - destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion Validm1m2; try constructor.
Qed.
Lemma IsValid_times_backward' : forall (m1 m2 : mode), Basics.impl (IsValid (m1 · m2)) (IsValid m1 /\ IsValid m2).
Proof.
  exact IsValid_times_backward.
Qed.
Hint Rewrite IsValid_times_backward' : propagate_down.

Lemma IsValid_plus_backward : forall (m1 m2 : mode), IsValid (mode_plus m1 m2) -> IsValid m1 /\ IsValid m2.
Proof.
  intros * Validm1m2. split.
  - destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion Validm1m2; try constructor.
  - destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion Validm1m2; try constructor.
Qed.

Lemma IsValid_plus_backward' : forall (m1 m2 : mode), Basics.impl (IsValid (mode_plus m1 m2)) (IsValid m1 /\ IsValid m2).
Proof.
  exact IsValid_plus_backward.
Qed.
Hint Rewrite IsValid_plus_backward' : propagate_down.

Lemma IsValid_times_iff : forall (m1 m2 : mode), IsValid (m1 · m2) <-> IsValid m1 /\ IsValid m2.
Proof.
  intros [[p1 a1]|] [[p2 a2]|]. all: cbn.
  all: sfirstorder.
Qed.
Hint Rewrite IsValid_times_iff : propagate_down.

Lemma IsValid_linnu : True <-> IsValid (¹ν).
Proof. split. intros _. exact (IsValidProof (Lin, (Fin 0))). intros _. tauto. Qed.
Hint Rewrite <- IsValid_linnu : propagate_down.

Lemma IsValid_linup : True <-> IsValid (¹↑).
Proof. split. intros _. exact (IsValidProof (Lin, (Fin 1))). intros _. tauto. Qed.
Hint Rewrite <- IsValid_linup : propagate_down.

Lemma IsValid_linnu' : IsValid (¹ν).
Proof. exact (IsValidProof (Lin, (Fin 0))). Qed.
Hint Resolve IsValid_linnu' : autolemmas.

Lemma IsValid_linup' : IsValid (¹↑).
Proof. exact (IsValidProof (Lin, (Fin 1))). Qed.
Hint Resolve IsValid_linup' : autolemmas.

Lemma IsLin_times_iff : forall (m1 m2 : mode), IsLin (mode_times m1 m2) <-> IsLin m1 /\ IsLin m2.
Proof.
  intros *.
  split.
  - intros IsLinm1m2. split.
    + destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion IsLinm1m2; try constructor.
    + destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion IsLinm1m2; try constructor.
  - intros (IsLinm1 & IsLinm2). destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion IsLinm1; try inversion IsLinm2; try constructor.
Qed.

Lemma IsLin_plus_backward : forall (m1 m2 : mode), IsLin (mode_plus m1 m2) -> IsLin m1 /\ IsLin m2.
Proof.
  intros * IsLinm1m2. destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion IsLinm1m2; try constructor.
Qed.

Lemma IsLin_plus_backward' : forall (m1 m2 : mode), Basics.impl (IsLin (mode_plus m1 m2)) (IsLin m1 /\ IsLin m2).
Proof.
  exact IsLin_plus_backward.
Qed.
Hint Rewrite IsLin_plus_backward' : propagate_down.

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

Lemma IsLin_linnu : True <-> IsLin (¹ν).
Proof. split. intros _. exact (IsLinProof (Fin 0)). intros _. tauto. Qed.
Hint Rewrite <- IsLin_linnu : propagate_down.

Lemma IsLin_linup : True <-> IsLin (¹↑).
Proof. split. intros _. exact (IsLinProof (Fin 1)). intros _. tauto. Qed.
Hint Rewrite <- IsLin_linup : propagate_down.

Lemma IsLin_linnu' : IsLin (¹ν).
Proof. exact (IsLinProof (Fin 0)). Qed.
Hint Resolve IsLin_linnu' : autolemmas.

Lemma IsLin_linup' : IsLin (¹↑).
Proof. exact (IsLinProof (Fin 1)). Qed.
Hint Resolve IsLin_linup' : autolemmas.

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

Lemma IsLinNu_wk_IsFinAge : forall (m : mode), IsLinNu m -> IsFinAge m.
Proof.
  intros *.
  sauto lq: on.
Qed.

Lemma IsLinNu_wk_IsFinAge' : forall (m : mode), Basics.impl (IsLinNu m) (IsLinNu m /\ IsFinAge m).
Proof.
  sfirstorder use: IsLinNu_wk_IsFinAge.
Qed.
Hint Rewrite IsLinNu_wk_IsFinAge' : saturate.

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

Lemma IsFinAge_times_iff : forall (m1 m2 : mode), IsFinAge (mode_times m1 m2) <-> IsFinAge m1 /\ IsFinAge m2.
Proof.
  intros *.
  split.
  - intros IsFinAgem1m2. split.
    + destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct a; try destruct a0; try destruct a1; simpl in *; try assumption; try inversion IsFinAgem1m2; try constructor.
    + destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct a; try destruct a0; try destruct a1; simpl in *; try assumption; try inversion IsFinAgem1m2; try constructor.
  - intros (IsFinAgem1 & IsFinAgem2). destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct m; try destruct m0; try destruct m1; simpl in *; try assumption; try inversion IsFinAgem1; try inversion IsFinAgem2; try constructor.
Qed.

Lemma IsFinAge_plus_backward : forall (m1 m2 : mode), IsFinAge (mode_plus m1 m2) -> IsFinAge m1 /\ IsFinAge m2.
Proof.
  intros * IsFinAgem1m2. destruct m1, m2; simpl in *; try destruct p; try destruct p0; try destruct p1; try destruct a; try destruct a0; try destruct a1; simpl in *; try assumption; try inversion IsFinAgem1m2; try constructor; try constructor.
Qed.
Lemma IsFinAge_plus_backward' : forall (m1 m2 : mode), Basics.impl (IsFinAge (mode_plus m1 m2)) (IsFinAge m1 /\ IsFinAge m2).
Proof.
  exact IsFinAge_plus_backward.
Qed.
Hint Rewrite IsFinAge_plus_backward' : propagate_down.

Lemma IsFinAge_linnu : True <-> IsFinAge (¹ν).
Proof. split. intros _. exact (IsFinAgeProof Lin 0). intros _. tauto. Qed.
Hint Rewrite <- IsFinAge_linnu : propagate_down.

Lemma IsFinAge_linup : True <-> IsFinAge (¹↑).
Proof. split. intros _. exact (IsFinAgeProof Lin 1). intros _. tauto. Qed.
Hint Rewrite <- IsFinAge_linup : propagate_down.

Lemma IsFinAge_linnu' : IsFinAge (¹ν).
Proof. exact (IsFinAgeProof Lin 0). Qed.
Hint Resolve IsFinAge_linnu' : autolemmas.

Lemma IsFinAge_linup' : IsFinAge (¹↑).
Proof. exact (IsFinAgeProof Lin 1). Qed.
Hint Resolve IsFinAge_linup' : autolemmas.

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

Lemma mode_times_distrib_on_plus : forall (m n o : mode), m · (mode_plus n o) = mode_plus (m · n) (m · o).
Proof.
  intros [[p1 a1]|] [[p2 a2]|] [[p3 a3]|]. all: cbn.
  all: trivial.
  (* 1 goal left *)
  destruct p1 as [|]; destruct p2 as [|]; destruct p3 as [|]; destruct a1 as [?|]; destruct a2 as [?|]; destruct a3 as [?|]. all: unfold mul_plus, mul_times, age_plus, age_times, ext_plus; repeat destruct age_eq_dec. all: trivial; try congruence; try reflexivity.
  all: exfalso; assert (n0 <> n1) as Hneq by (intros H; apply n2; rewrite H; constructor);
                  assert (n + n0 = n + n1) as Heq by (injection e; auto);
                  apply Hneq; rewrite Nat.add_cancel_l with (p := n) in Heq; assumption.
Qed.

Lemma ModeSubtype_refl : forall (m : mode), ModeSubtype m m.
Proof.
  intros m. sauto lq: on.
Qed.

Lemma IsSubtype_mode_plus: forall (m m' : mode), m ⥶ mode_plus m m'.
Proof.
  intros *. destruct m, m'; unfold mode_plus; try destruct p; try destruct p0; try destruct m; try destruct a; try destruct m0; try destruct a0; unfold mul_plus, age_plus; try destruct (age_eq_dec (Fin n) (Fin n0)); try destruct (age_eq_dec (Fin n) Inf); try destruct (age_eq_dec Inf (Fin n)); try congruence; try repeat constructor.
Qed.

Lemma IsSubtype_refl : forall (m : mode), m ⥶ m.
Proof.
  intros m. destruct m. destruct p, m, a; try destruct n. all: try repeat constructor.
Qed.

Lemma IsSubtype_union : forall (P D : ctx) (n : name) (b b' : binding_type_of n), P n = Some b -> (P ᴳ+ D) n = Some b' -> (mode_of b) ⥶ (mode_of b').
Proof.
  intros * mapstoP mapstoPuD. unfold union in mapstoPuD. destruct (In_dec n D).
  - rewrite In_iff_exists_Some in H. destruct H as (b'' & mapstoD). rewrite merge_with_Some_Some_eq with (y1 := b) (y2 := b'') in mapstoPuD. destruct n, b, b', b''; unfold union_var in *; unfold union_dh in *; cbn in *; try destruct (type_eq_dec T T1); try destruct (mode_eq_dec n n1); inversion mapstoPuD; subst; try apply IsSubtype_mode_plus; try constructor. tauto.
  - rewrite nIn_iff_nMapsTo in H. rewrite merge_with_Some_None_eq with (y1 := b) in mapstoPuD. inversion mapstoPuD. apply IsSubtype_refl. tauto.
Qed.

Lemma ModeSubtype_linnu_eq : forall (m : mode), m ⥶ ¹ν <-> m = ¹ν.
Proof.
  intros m. split.
  - intros H. inversion H. inversion H2. inversion H4. reflexivity.
  - intros H. rewrite H. apply ModeSubtype_refl.
Qed.

Lemma ModeSubtype_linnu_stimes : forall (m1 m2 : mode), ¹ν ⥶ m1 -> ¹ν ⥶ m2 -> ¹ν ⥶ m1 · m2.
Proof.
  intros * Subtypem1 Subtypem2. destruct m1, m2; try destruct p; try destruct p0; try destruct m; try destruct m0; try destruct a; try destruct a0; try destruct n; try destruct a0; simpl in *; try constructor; try inversion Subtypem1; try inversion Subtypem2; try inversion H4; try congruence; try inversion H4.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of union *)
(*----------------------------------------------------------------------------*)
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

(* Could be an equivalence *)
Lemma union_empty_iff : forall G1 G2, G1 ᴳ+ G2 = ᴳ{} <-> G1 = ᴳ{} /\ G2 = ᴳ{}.
Proof.
  intros *.
  split.
  - intros union_empty. split; apply ext_eq; intros n; unfold union in union_empty; apply func_eq_on_arg with (n := n) in union_empty; cbn in *; unfold Fun.merge in union_empty; destruct (G2 n), (G1 n), n; cbn in *; trivial; try congruence; destruct b, b0; unfold union_var, union_dh in *; try destruct (type_eq_dec T0 T); try destruct (mode_eq_dec n0 n); cbn; trivial.
  - intros [empty1 empty2]. rewrite empty1, empty2. symmetry. apply union_empty_r_eq.
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
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* We don't have AAC instantiated for our union operation on contexts, so instead, we use the following lemmas... Really not ideal. *)
(*----------------------------------------------------------------------------*)
Lemma union_swap_1_2_l3 : forall (G1 G2 G3 : ctx), G1 ᴳ+ G2 ᴳ+ G3 = G2 ᴳ+ G1 ᴳ+ G3.
Proof. intros *. rewrite union_commutative with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_3_l3 : forall (G1 G2 G3 : ctx), G1 ᴳ+ G2 ᴳ+ G3 = G3 ᴳ+ G2 ᴳ+ G1.
Proof. intros *. rewrite union_commutative. rewrite union_commutative with (G1 := G1). rewrite union_associative. reflexivity. Qed.
Lemma union_swap_2_3_l3 : forall (G1 G2 G3 : ctx), G1 ᴳ+ G2 ᴳ+ G3 = G1 ᴳ+ G3 ᴳ+ G2.
Proof. intros *. rewrite <- union_associative. rewrite union_commutative with (G1 := G2). rewrite union_associative. reflexivity. Qed.

Lemma union_swap_1_2_l4 : forall (G1 G2 G3 G4 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 = G2 ᴳ+ G1 ᴳ+ G3 ᴳ+ G4.
Proof. intros *. rewrite union_commutative with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_3_l4 : forall (G1 G2 G3 G4 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 = G3 ᴳ+ G2 ᴳ+ G1 ᴳ+ G4.
Proof. intros *. rewrite union_swap_1_3_l3 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_4_l4 : forall (G1 G2 G3 G4 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 = G4 ᴳ+ G2 ᴳ+ G3 ᴳ+ G1.
Proof. intros *. rewrite union_swap_1_3_l3 with (G1 := G1). rewrite union_swap_1_3_l3 with (G1 := G3 ᴳ+ G2). rewrite <- union_associative. rewrite union_commutative with (G1 := G1). rewrite union_commutative with (G1 := G3). repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_2_3_l4 : forall (G1 G2 G3 G4 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 = G1 ᴳ+ G3 ᴳ+ G2 ᴳ+ G4.
Proof. intros *. rewrite union_swap_2_3_l3 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_2_4_l4 : forall (G1 G2 G3 G4 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 = G1 ᴳ+ G4 ᴳ+ G3 ᴳ+ G2.
Proof. intros *. rewrite <- 2 union_associative. rewrite union_associative with (G1 := G2). rewrite union_swap_1_3_l3 with (G1 := G2). repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_3_4_l4 : forall (G1 G2 G3 G4 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 = G1 ᴳ+ G2 ᴳ+ G4 ᴳ+ G3.
Proof. intros *. rewrite union_swap_2_3_l3 with (G1 := G1 ᴳ+ G2). reflexivity. Qed.

Lemma union_swap_1_2_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G2 ᴳ+ G1 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5.
Proof. intros *. rewrite union_commutative with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_3_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G3 ᴳ+ G2 ᴳ+ G1 ᴳ+ G4 ᴳ+ G5.
Proof. intros *. rewrite union_swap_1_3_l4 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_4_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G4 ᴳ+ G2 ᴳ+ G3 ᴳ+ G1 ᴳ+ G5.
Proof. intros *. rewrite union_swap_1_4_l4 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_5_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G5 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G1.
Proof. intros *. rewrite union_swap_1_4_l4 with (G1 := G1). rewrite union_swap_1_4_l4 with (G1 := G4 ᴳ+ G2). rewrite <- union_associative. rewrite union_commutative with (G1 := G1). rewrite union_commutative with (G1 := G4). repeat rewrite union_associative. rewrite union_swap_2_3_l3 with (G1 := G5). reflexivity. Qed.
Lemma union_swap_2_3_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G1 ᴳ+ G3 ᴳ+ G2 ᴳ+ G4 ᴳ+ G5.
Proof. intros *. rewrite union_swap_2_3_l4 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_2_4_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G1 ᴳ+ G4 ᴳ+ G3 ᴳ+ G2 ᴳ+ G5.
Proof. intros *. rewrite union_swap_2_4_l4 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_2_5_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G1 ᴳ+ G5 ᴳ+ G3 ᴳ+ G4 ᴳ+ G2.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_swap_1_4_l4. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_3_4_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G1 ᴳ+ G2 ᴳ+ G4 ᴳ+ G3 ᴳ+ G5.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_swap_2_3_l4. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_3_5_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G1 ᴳ+ G2 ᴳ+ G5 ᴳ+ G4 ᴳ+ G3.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_swap_2_4_l4. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_4_5_l5 : forall (G1 G2 G3 G4 G5 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 = G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G5 ᴳ+ G4.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_commutative with (G1 := G4). reflexivity. Qed.

Lemma union_swap_1_2_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G2 ᴳ+ G1 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6.
Proof. intros *. rewrite union_commutative with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_3_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G3 ᴳ+ G2 ᴳ+ G1 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6.
Proof. intros *. rewrite union_swap_1_3_l5 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_4_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G4 ᴳ+ G2 ᴳ+ G3 ᴳ+ G1 ᴳ+ G5 ᴳ+ G6.
Proof. intros *. rewrite union_swap_1_4_l5 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_5_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G5 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G1 ᴳ+ G6.
Proof. intros *. rewrite union_swap_1_5_l5 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_1_6_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G6 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G1.
Proof. intros *. rewrite union_swap_1_5_l5 with (G1 := G1 ᴳ+ G2). rewrite union_commutative with (G1 := G1). rewrite union_associative. rewrite union_swap_2_5_l5 with (G5 := G2). rewrite union_swap_3_5_l5 with (G5 := G3). rewrite union_swap_4_5_l5 with (G5 := G4). reflexivity. Qed.
Lemma union_swap_2_3_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G3 ᴳ+ G2 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6.
Proof. intros *. rewrite union_swap_2_3_l5 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_2_4_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G4 ᴳ+ G3 ᴳ+ G2 ᴳ+ G5 ᴳ+ G6.
Proof. intros *. rewrite union_swap_2_4_l5 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_2_5_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G5 ᴳ+ G3 ᴳ+ G4 ᴳ+ G2 ᴳ+ G6.
Proof. intros *. rewrite union_swap_2_5_l5 with (G1 := G1). reflexivity. Qed.
Lemma union_swap_2_6_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G6 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G2.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_associative with (G1 := G2 ᴳ+ G3 ᴳ+ G4). rewrite union_swap_1_5_l5. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_3_4_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G2 ᴳ+ G4 ᴳ+ G3 ᴳ+ G5 ᴳ+ G6.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_associative with (G1 := G2 ᴳ+ G3 ᴳ+ G4).  rewrite union_swap_2_3_l5. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_3_5_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G2 ᴳ+ G5 ᴳ+ G4 ᴳ+ G3 ᴳ+ G6.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_associative with (G1 := G2 ᴳ+ G3 ᴳ+ G4).  rewrite union_swap_2_4_l5. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_3_6_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G2 ᴳ+ G6 ᴳ+ G4 ᴳ+ G5 ᴳ+ G3.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_associative with (G1 := G2 ᴳ+ G3 ᴳ+ G4).  rewrite union_swap_2_5_l5. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_4_5_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G5 ᴳ+ G4 ᴳ+ G6.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_associative with (G1 := G2 ᴳ+ G3 ᴳ+ G4). rewrite union_swap_3_4_l5. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_4_6_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G6 ᴳ+ G5 ᴳ+ G4.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_associative with (G1 := G2). rewrite union_associative with (G1 := G2 ᴳ+ G3). rewrite union_associative with (G1 := G2 ᴳ+ G3 ᴳ+ G4). rewrite union_swap_3_5_l5. repeat rewrite union_associative. reflexivity. Qed.
Lemma union_swap_5_6_l6 : forall (G1 G2 G3 G4 G5 G6 : ctx), G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G5 ᴳ+ G6 = G1 ᴳ+ G2 ᴳ+ G3 ᴳ+ G4 ᴳ+ G6 ᴳ+ G5.
Proof. intros *. repeat rewrite <- union_associative. rewrite union_commutative with (G1 := G5). reflexivity. Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of stimes *)
(*----------------------------------------------------------------------------*)
Lemma stimes_empty_eq : forall (m : mode), m ᴳ· ᴳ{} = ᴳ{}.
Proof.
  intros *. unfold ctx_empty, empty, stimes, map. cbn.
  f_equal.
  apply proof_irrelevance.
Qed.
Hint Rewrite stimes_empty_eq : canonalize.

Lemma stimes_empty_iff : forall G m, m ᴳ· G = ᴳ{} <-> G = ᴳ{}.
Proof.
  intros *.
  split.
  - intros stimes_empty. apply ext_eq. intros n. unfold stimes in stimes_empty. apply func_eq_on_arg with (n := n) in stimes_empty. cbn in *; unfold Fun.map in stimes_empty; destruct (G n), n; cbn in *; trivial; try congruence; destruct b; unfold stimes_var, stimes_dh in *; try destruct (type_eq_dec T0 T); try destruct (mode_eq_dec n0 m); cbn; trivial.
  - intros empty. rewrite empty. apply stimes_empty_eq.
Qed.

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

Lemma stimes_distrib_on_union : forall (m : mode) (G1 G2 : ctx),  m ᴳ· (G1 ᴳ+ G2) = m ᴳ· G1 ᴳ+ m ᴳ· G2.
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
    { rewrite mode_times_distrib_on_plus; reflexivity. }
    { unfold mode_times. destruct m. destruct p. all: tauto. }
  - destruct H as (binding1 & mapstoG1), H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG1; rewrite mapstoG2; cbn.
    f_equal. unfold stimes_dh, union_dh.
    destruct binding1, binding2, (type_eq_dec T T0); try destruct (mode_eq_dec n n0).
    all: try rewrite mode_times_distrib_on_plus; try reflexivity.
    all: unfold mode_times; destruct m; try destruct p. all: tauto.
  - destruct H as (binding1 & mapstoG1); cbn; rewrite mapstoG1; cbn. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
  - destruct H as (binding1 & mapstoG1); cbn; rewrite mapstoG1; cbn. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
  - destruct H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG2; cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. reflexivity.
  - destruct H0 as (binding2 & mapstoG2); cbn; rewrite mapstoG2; cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. reflexivity.
  - cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
  - cbn. rewrite nIn_iff_nMapsTo in H. rewrite H. rewrite nIn_iff_nMapsTo in H0. rewrite H0. reflexivity.
Qed.
Hint Rewrite stimes_distrib_on_union : canonalize.

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

Lemma stimes_singleton_dest : forall (h : hname) (m n : mode) (T : type) (m': mode), m' ᴳ· ᴳ{- h : m ⌊ T ⌋ n} = ᴳ{- h : (m · m') ⌊ T ⌋ n}.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold stimes, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₋ m ⌊ T ⌋ n). split. tauto. unfold stimes_dh. rewrite mode_times_commutative. reflexivity. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ m ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ (m · m') ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.
Lemma stimes_singleton_hole : forall (h : hname) (T : type) (n : mode) (m': mode), m' ᴳ· ᴳ{+ h : T ‗ n} = ᴳ{+ h : T ‗ (n · m') }.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold stimes, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₊ T ‗ n). split. tauto. unfold stimes_dh. rewrite mode_times_commutative. reflexivity. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ T ‗ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ T ‗ (n · m')) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma stimes_mode_plus_eq : forall (G : ctx) (m1 m2 : mode), m1 ᴳ· G ᴳ+ m2 ᴳ· G = (mode_plus m1 m2) ᴳ· G.
Proof.
  intros *.
  apply ext_eq. intros n. unfold union, stimes. destruct (In_dec n G).
  - rewrite In_iff_exists_Some in H. destruct H as (tyb & mapsto). destruct n; unfold merge_with, merge, Fun.on_conflict_do, Fun.merge, map, Fun.map; try unfold stimes_var; try unfold stimes_dh; simpl; rewrite mapsto in *; destruct tyb; simpl; destruct (type_eq_dec T T); try rewrite 3 mode_times_commutative with (n := m); try rewrite 3 mode_times_commutative with (n := n); try rewrite mode_times_distrib_on_plus; try reflexivity; try contradiction.
    destruct (mode_eq_dec n n). reflexivity. contradiction.
  - rewrite nIn_iff_nMapsTo in H. unfold merge_with, merge, Fun.on_conflict_do, Fun.merge, map, Fun.map; try unfold stimes_var; try unfold stimes_dh; simpl; rewrite H; reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of hminus *)
(*----------------------------------------------------------------------------*)
Lemma hminus_empty_eq : (ᴳ- ᴳ{}) = ᴳ{}.
Proof.
  unfold hminus, empty, map. cbn.
  apply ext_eq.
  all: sfirstorder.
Qed.
Hint Rewrite hminus_empty_eq : canonalize.

Lemma hminus_distrib_on_union : forall (G1 G2 : ctx), G1 # G2 ->(ᴳ- (G1 ᴳ+ G2)) = (ᴳ-G1) ᴳ+ (ᴳ-G2).
Proof.
  intros * DisjointG1G2.
  apply ext_eq.
  intros n. unfold hminus, union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.on_conflict_do.
  destruct (In_dec n G1), (In_dec n G2).
  { unfold Disjoint in DisjointG1G2. specialize (DisjointG1G2 n H H0). contradiction. }
  all: destruct n; try destruct H as (binding1 & mapstoG1); try destruct H0 as (binding2 & mapstoG2); cbn; try rewrite nIn_iff_nMapsTo in H; try rewrite nIn_iff_nMapsTo in H0; try rewrite mapstoG1; try rewrite mapstoG2; try rewrite H; try rewrite H0; cbn; trivial.
Qed.

Lemma hminus_singleton : forall (h : hname) (T : type) (n : mode), (ᴳ- ᴳ{+ h : T ‗ n}) = ᴳ{- h : ¹ν ⌊ T ⌋ n }.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold hminus, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₊ T ‗ n). split; tauto. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ ¹ν ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ T ‗ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma hminus_hminus_inv_eq : forall (G : ctx), ValidOnly (ᴳ-⁻¹ G) -> ᴳ- (ᴳ-⁻¹ G) = G.
Proof.
  intros * ValidOnlyG. apply ext_eq. intros n. unfold hminus, hminus_inv, map, Fun.map; simpl. destruct (G n) eqn:Gmapsto; simpl. f_equal. 2:{ reflexivity. }
  specialize (ValidOnlyG n). unfold hminus_inv in ValidOnlyG. generalize (map_MapsTo_if (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) G n b); intros H. specialize (H Gmapsto). specialize (ValidOnlyG (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end) n b) H).
  destruct n, b; simpl in *.
  * inversion ValidOnlyG.
  * destruct m; try destruct p, a; try destruct m; try destruct n0; simpl in *; try reflexivity; try inversion ValidOnlyG.
  * inversion ValidOnlyG.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of hminus_inv *)
(*----------------------------------------------------------------------------*)
Lemma hminus_inv_empty_eq : (ᴳ-⁻¹ ᴳ{}) = ᴳ{}.
Proof.
  apply ext_eq.
  all: sfirstorder.
Qed.
Hint Rewrite hminus_inv_empty_eq : canonalize.

Lemma hminus_inv_empty_iff : forall (G : ctx), ᴳ-⁻¹ G = ᴳ{} <-> G = ᴳ{}.
Proof.
  intros. split; intros.
  - apply ext_eq. intros n; cbn in *. assert ((ᴳ-⁻¹ G) n = ᴳ{} n). { rewrite H; reflexivity. } unfold hminus_inv in H0. simpl (ᴳ{} n) in H0. rewrite map_nMapsTo_iff in H0. assumption.
  - apply ext_eq. intros n; cbn in *. rewrite H. reflexivity.
Qed.

Lemma hminus_inv_distrib_on_union : forall (G1 G2 : ctx), G1 # G2 ->(ᴳ-⁻¹ (G1 ᴳ+ G2)) = (ᴳ-⁻¹G1) ᴳ+ (ᴳ-⁻¹G2).
Proof.
  intros * DisjointG1G2.
  apply ext_eq.
  intros n. unfold hminus_inv, union.
  unfold map, merge_with, merge, Fun.map, Fun.merge, Fun.on_conflict_do.
  destruct (In_dec n G1), (In_dec n G2).
  { unfold Disjoint in DisjointG1G2. specialize (DisjointG1G2 n H H0). contradiction. }
  all: destruct n; try destruct H as (binding1 & mapstoG1); try destruct H0 as (binding2 & mapstoG2); cbn; try rewrite nIn_iff_nMapsTo in H; try rewrite nIn_iff_nMapsTo in H0; try rewrite mapstoG1; try rewrite mapstoG2; try rewrite H; try rewrite H0; cbn; trivial.
Qed.

Lemma hminus_inv_singleton : forall (h : hname) (T : type) (n : mode), (ᴳ-⁻¹ ᴳ{- h : ¹ν ⌊ T ⌋ n}) = ᴳ{+ h : T ‗ n }.
Proof.
  intros *.
  apply ext_eq.
  intros n'. unfold hminus_inv, ctx_singleton.
  destruct (name_eq_dec n' (ʰ h)); rewrite? e in *.
  { rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. rewrite singleton_MapsTo_at_elt. simpl. exists (₋ ¹ν ⌊ T ⌋ n). split; tauto. }
  { assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₋ ¹ν ⌊ T ⌋ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    assert (@singleton name binding_type_of (ʰ h) name_eq_dec (₊ T ‗ n) n' = None). { apply singleton_nMapsTo_iff. symmetry. assumption. }
    rewrite H0 in *. apply map_nMapsTo_iff. assumption. }
Qed.

Lemma hminus_inv_hminus_eq : forall (G : ctx), ValidOnly (ᴳ-⁻¹ (ᴳ- G)) -> ᴳ-⁻¹ (ᴳ- G) = G.
Proof.
  intros * ValidOnlyhiG. apply ext_eq. intros n. unfold hminus, hminus_inv, map, Fun.map; simpl. destruct (G n) eqn:Gmapsto; simpl. f_equal. 2:{ reflexivity. }
  specialize (ValidOnlyhiG n). unfold hminus, hminus_inv in ValidOnlyhiG. rewrite map_comp in ValidOnlyhiG. generalize (map_MapsTo_if (fun (x : name) (y : binding_type_of x) => fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end) x (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ _ ⌊ _ ⌋ _ => ₋ ☠ ⌊ ① ⌋ ☠
| ₊ T ‗ n => ₋ ¹ν ⌊ T ⌋ n
end) x y)) G n b); intros H. specialize (H Gmapsto). specialize (ValidOnlyhiG ((fun (x : name) (y : binding_type_of x) => fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end) x (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ _ ⌊ _ ⌋ _ => ₋ ☠ ⌊ ① ⌋ ☠
| ₊ T ‗ n => ₋ ¹ν ⌊ T ⌋ n
end) x y)) n b) H).
  destruct n, b; simpl in *.
  * inversion ValidOnlyhiG.
  * inversion ValidOnlyhiG.
  * unfold Fun.map in H; simpl in H. rewrite Gmapsto in H; simpl in H. reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* In *)
(*----------------------------------------------------------------------------*)
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

Lemma In_union_iff : forall (D1 D2 : ctx) (n : name), In n (D1 ᴳ+ D2) <-> In n D1 \/ In n D2.
Proof.
  intros *. split.
  - intros inUnion. unfold union in inUnion. apply In_merge_iff in inUnion. assumption.
  - intros [inD1|inD2].
    + apply In_union_forward_l. assumption.
    + apply In_union_forward_r. assumption.
Qed.

Lemma In_stimes_iff : forall (D : ctx) (m : mode) (n : name), In n (m ᴳ· D) <-> In n D.
Proof.
  intros *. split.
  - intros inStimes. unfold stimes in inStimes. destruct (In_dec n D).
    + assumption.
    + unfold stimes in H. apply In_map_iff in inStimes. congruence.
  - intros inD. unfold stimes. destruct (In_dec n D). apply In_map_iff. assumption. congruence.
Qed.

Lemma In_hminus_inv_iff : forall (D : ctx) (n : name), In n (ᴳ-⁻¹ D) <-> In n D.
Proof.
  intros *. split.
  - intros inHminusInv. unfold hminus_inv in inHminusInv. destruct (In_dec n D).
    + assumption.
    + unfold hminus_inv in H. apply In_map_iff in inHminusInv. congruence.
  - intros inD. unfold hminus_inv. destruct (In_dec n D). apply In_map_iff. assumption. congruence.
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

Lemma nIn_union_iff: forall (G1 G2 : ctx) (n : name), ~In n (G1 ᴳ+ G2) <-> ((~In n G1) /\ (~In n G2)).
Proof.
  intros *. split.
  - intros nInUnion. split.
    + intros contra. apply nInUnion. apply In_union_forward_l. assumption.
    + intros contra. apply nInUnion. apply In_union_forward_r. assumption.
  - intros (NotIn1 & NotIn2) InUnion. unfold union in InUnion. apply In_merge_iff in InUnion. destruct InUnion. all:congruence.
Qed.

Lemma nIn_stimes_iff : forall (D : ctx) (m : mode) (n : name), ~In n (m ᴳ· D) <-> ~In n D.
Proof.
  intros *. split.
  - intros nInStimes. unfold stimes in nInStimes. intros contra. apply nInStimes. apply In_stimes_iff. assumption.
  - intros nInD nInStimes. apply In_stimes_iff in nInStimes. congruence.
Qed.

Lemma In_union_nMapsTo_contra : forall (G1 G2 : ctx) (n : name), In n (G1 ᴳ+ G2) -> G1 n = None -> G2 n = None -> False.
Proof.
  intros * InG G1n G2n. apply In_union_iff in InG. destruct InG as [(b & InG) | (b & InG)]; congruence.
Qed.

Lemma Empty_dec : forall (G : ctx), { G = ᴳ{}} + { exists n binding, G n = Some binding }.
Proof.
  intros *. destruct (dom(G)) eqn:eDomG.
  - left. apply ext_eq. apply dom_nil_is_empty in eDomG. rewrite eDomG. intros x. trivial.
  - right. exists n. rewrite <- In_iff_exists_Some. apply dom_spec. rewrite eDomG. apply List.in_eq.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Disjoint *)
(*----------------------------------------------------------------------------*)
Lemma Disjoint_stimes_l_iff : forall (m : mode) (D D' : ctx), (m ᴳ· D) # D' <-> D # D'.
Proof.
  (* This proof, and the similar ones below are more complicated than
    they ought to because we can't rewrite under foralls. I
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
Hint Rewrite <- Disjoint_hminus_inv_l_iff : propagate_down.

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
Hint Rewrite <- Disjoint_hminus_inv_r_iff : propagate_down.

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

Lemma Disjoint_empty_l : forall (G : ctx), ᴳ{} # G.
Proof.
  sauto q: on unfold: Disjoint.
Qed.
Hint Resolve Disjoint_empty_l : autolemmas.

Lemma Disjoint_empty_r : forall (G : ctx), Disjoint G ᴳ{}.
Proof.
  sauto q: on unfold: Disjoint.
Qed.
Hint Resolve Disjoint_empty_r : autolemmas.

Lemma Disjoint_singletons_iff : forall (n1 n2 : name) (binding1 : binding_type_of n1) (binding2 : binding_type_of n2), ctx_singleton n1 binding1 # ctx_singleton n2 binding2 <-> n1 <> n2.
Proof.
  intros *.
  split.
  - intros DisjointSing. intros contra. subst. unfold Disjoint in DisjointSing. specialize (DisjointSing n2). assert (In n2 (ctx_singleton n2 binding1)). { apply In_singleton_iff; reflexivity. } assert (In n2 (ctx_singleton n2 binding2)). { apply In_singleton_iff; reflexivity. } specialize (DisjointSing H H0). congruence.
  - intros n1neq2. unfold Disjoint. intros n. intros inSing1 inSing2. unfold ctx_singleton in inSing1, inSing2. rewrite In_singleton_iff with (x := n1) (discr := name_eq_dec) (v := binding1) in inSing1. rewrite In_singleton_iff with (x := n2) (discr := name_eq_dec) (v := binding2) in inSing2. subst. congruence.
Qed.

Lemma Disjoint_singleton_var_iff_same_name : forall (G : ctx) (x : var) (m1 m2 : mode) (T1 T2 : type), G # ᴳ{ x : m1 ‗ T1} <-> G # (ᴳ{ x : m2 ‗ T2}).
Proof.
  intros *.
  unfold Disjoint.
  split.
  - intros * DisjointG. intros * InG InS. unfold ctx_singleton in *.
    rewrite In_singleton_iff in InS; subst.
    specialize (DisjointG (ˣ x) InG).
    contradiction DisjointG.
    rewrite In_singleton_iff. reflexivity.
  - intros * DisjointG. intros * InG InS. unfold ctx_singleton in *.
    rewrite In_singleton_iff in InS; subst.
    specialize (DisjointG (ˣ x) InG).
    contradiction DisjointG.
    rewrite In_singleton_iff. reflexivity.
Qed.

Lemma Disjoint_singleton_dest_iff_same_name : forall (G : ctx) (h : hname) (m1 m2 n1 n2 : mode) (T1 T2 : type), G # ᴳ{- h : m1 ⌊ T1 ⌋ n1 } <-> G # ᴳ{- h : m2 ⌊ T2 ⌋ n2 }.
Proof.
  intros *.
  unfold Disjoint.
  split.
  - intros * DisjointG. intros * InG InS. unfold ctx_singleton in *.
    rewrite In_singleton_iff in InS; subst.
    specialize (DisjointG (ʰ h) InG).
    contradiction DisjointG.
    rewrite In_singleton_iff. reflexivity.
  - intros * DisjointG. intros * InG InS. unfold ctx_singleton in *.
    rewrite In_singleton_iff in InS; subst.
    specialize (DisjointG (ʰ h) InG).
    contradiction DisjointG.
    rewrite In_singleton_iff. reflexivity.
Qed.

Lemma Disjoint_singleton_hole_iff_same_name : forall (G : ctx) (h : hname) (n1 n2 : mode) (T1 T2 : type), G # ᴳ{+ h : T1 ‗ n1 } <-> G # ᴳ{+ h : T2 ‗ n2 }.
Proof.
  intros *.
  unfold Disjoint.
  split.
  - intros * DisjointG. intros * InG InS. unfold ctx_singleton in *.
    rewrite In_singleton_iff in InS; subst.
    specialize (DisjointG (ʰ h) InG).
    contradiction DisjointG.
    rewrite In_singleton_iff. reflexivity.
  - intros * DisjointG. intros * InG InS. unfold ctx_singleton in *.
    rewrite In_singleton_iff in InS; subst.
    specialize (DisjointG (ʰ h) InG).
    contradiction DisjointG.
    rewrite In_singleton_iff. reflexivity.
Qed.

Lemma Disjoint_MapsTo_contra : forall (G1 G2 : ctx) (n : name) (b1 b2 : binding_type_of n), G1 # G2 -> G1 n = Some b1 -> G2 n = Some b2 -> False.
Proof.
  intros * DisjointG1G2 G1mapsto G2mapsto. apply DisjointG1G2 with (x := n). unfold In; exists b1; assumption.
  unfold In; exists b2; assumption.
Qed.

(* Sometimes bijections are beautiful *)
Lemma Disjoint_cshift_iff : forall D1 D2 H h', D1 # D2 <-> (D1 ᴳ[ H ⩲ h']) # (D2 ᴳ[ H ⩲ h']).
Proof.
  assert (forall p D1 D2, D1 # D2 -> ctx_shift p D1 # ctx_shift p D2) as suffices.
  2:{ split.
      - apply suffices.
      - specialize (suffices (shift_perm H h') (ctx_shift (List.rev (shift_perm H h')) D1) (ctx_shift (List.rev (shift_perm H h')) D2)).
        rewrite !shift_pre_inverse in suffices. auto. }
  intros *. unfold Disjoint. intros h x. rewrite !In_shift.
  sfirstorder.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Now we move on general properties on typing contexts, like ValidOnly, DestOnly, etc. *)
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* ValidOnly *)
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

Lemma ValidOnly_singleton_iff: forall (n : name) (binding: binding_type_of n), ValidOnly (ctx_singleton n binding) <-> IsValid (mode_of binding).
Proof.
  intros n binding. split.
  - intros ValidOnlySing. unfold ValidOnly in ValidOnlySing.
    specialize (ValidOnlySing n binding). unfold ctx_singleton in ValidOnlySing. specialize (ValidOnlySing (singleton_MapsTo_at_elt n name_eq_dec binding)). assumption.
  - intros IsValidMode. unfold ValidOnly. intros n' binding' mapstoSing. apply singleton_MapsTo_iff in mapstoSing. assert (n = n'). { apply eq_sigT_fst in mapstoSing. assumption. } subst. apply inj_pair2_eq_dec in mapstoSing. 2:{ exact name_eq_dec. } subst. assumption.
Qed.
Hint Rewrite ValidOnly_singleton_iff : propagate_down.
Hint Rewrite ValidOnly_singleton_iff : suffices.

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

Lemma ValidOnly_empty : ValidOnly ᴳ{}.
Proof.
  sauto q: on unfold: ValidOnly.
Qed.
Hint Resolve ValidOnly_empty : autolemmas.

Lemma ValidOnly_hminus_inv_DestOnly_LinNuOnly : forall D, ValidOnly (ᴳ-⁻¹ D) -> DestOnly D /\ LinNuOnly D.
Proof.
  intros * ValidOnlyhiD.
  split.
  - intros n b mapsto.
    pose (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) as f.
    specialize (ValidOnlyhiD n (f n b)).
    assert ((ᴳ-⁻¹ D) n = Some (f n b)).
      { unfold hminus_inv. apply map_MapsTo_if; trivial. }
    specialize (ValidOnlyhiD H). inversion ValidOnlyhiD. destruct n, b; simpl in *; trivial; try congruence.
  - intros n b mapsto.
    pose (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding0 : binding_dh => match binding0 with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) as f.
    specialize (ValidOnlyhiD n (f n b)).
    assert ((ᴳ-⁻¹ D) n = Some (f n b)).
      { unfold hminus_inv. apply map_MapsTo_if; trivial. }
    specialize (ValidOnlyhiD H). inversion ValidOnlyhiD. destruct n, b; simpl in *; trivial; try congruence.
    destruct m.
    * destruct p. destruct m, a; try destruct n0; trivial; try congruence; try constructor.
    * congruence.
Qed.

Lemma ValidOnly_hminus_inv_wk_l : forall (D1 D2 : ctx), ValidOnly (ᴳ-⁻¹ (D1 ᴳ+ D2)) -> ValidOnly (ᴳ-⁻¹ D1).
Proof.
  intros * ValidOnlyG.
  intros n b D1mapsto.
  unfold hminus_inv in D1mapsto.
  apply map_MapsTo_iff in D1mapsto. destruct D1mapsto as (b1 & D1mapsto & b1eq).
  rewrite b1eq; clear b1eq.
  destruct (D2 n) as [b2|] eqn:D2mapsto.
  - assert ((ᴳ-⁻¹ (D1 ᴳ+ D2)) n = Some ((fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) n ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b1 b2))).
    { unfold union, hminus_inv. apply map_MapsTo_if. apply merge_with_Some_Some_eq. split; assumption. }
    specialize (ValidOnlyG n ((fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) n ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b1 b2)) H).
    clear H. destruct n, b1, b2; simpl in *; inversion ValidOnlyG; subst; try destruct (type_eq_dec T T0); try destruct (mode_eq_dec n n0); try destruct m; try destruct m0; subst; try congruence; try destruct p; try destruct p0; simpl in *; try destruct m; try destruct m0; try destruct a; try destruct a0; simpl in *; try congruence.
  - assert ((ᴳ-⁻¹ (D1 ᴳ+ D2)) n = Some ((fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) n b1)).
    { unfold union, hminus_inv. apply map_MapsTo_if. apply merge_with_Some_None_eq. split; assumption. }
    specialize (ValidOnlyG n ((fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) n b1) H).
    clear H. destruct n, b1; simpl in *; inversion ValidOnlyG; subst; try destruct (type_eq_dec T T0); try destruct (mode_eq_dec n n0); try destruct m; try destruct m0; subst; try congruence; try destruct p; try destruct p0; simpl in *; try destruct m; try destruct m0; try destruct a; try destruct a0; simpl in *; try congruence.
Qed.

Lemma ValidOnly_hminus : forall (G : ctx), ValidOnly G -> HoleOnly G -> ValidOnly (ᴳ-⁻¹ (ᴳ- G)).
Proof.
  intros * ValidOnlyG HoleOnlyG. unfold ValidOnly. intros n b hmhGmapsto. specialize (ValidOnlyG n).
  specialize (HoleOnlyG n).
  unfold hminus_inv, hminus in hmhGmapsto. rewrite map_comp in hmhGmapsto.
  generalize (map_MapsTo_iff (fun (x : name) (y : binding_type_of x) => fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n => ₊ T ‗ n
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end) x (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ _ ⌊ _ ⌋ _ => ₋ ☠ ⌊ ① ⌋ ☠
| ₊ T ‗ n => ₋ ¹ν ⌊ T ⌋ n
end) x y)) G n b). intros H; apply H in hmhGmapsto. destruct hmhGmapsto as (b' & Gmapsto & H'). clear H. specialize (ValidOnlyG b' Gmapsto). specialize (HoleOnlyG b' Gmapsto). rewrite H'; simpl in *.
  destruct n, b'; simpl in *; try congruence; try contradiction.
Qed.

Lemma ValidOnly_hminus_inv_union : forall (D1 D2 : ctx), ValidOnly (ᴳ-⁻¹ D1) -> ValidOnly (ᴳ-⁻¹ D2) -> D1 # D2 -> ValidOnly (ᴳ-⁻¹ (D1 ᴳ+ D2)).
Proof.
  intros * ValidOnlyD1 ValidOnlyD2 DisjointD1D2. rewrite Disjoint_hminus_inv_l_iff in DisjointD1D2. rewrite Disjoint_hminus_inv_r_iff in DisjointD1D2.
  intros n b unionmapsto. destruct ((ᴳ-⁻¹ D1) n) eqn:hiD1mapsto.
  - specialize (ValidOnlyD1 n b0 hiD1mapsto).
    assert ((ᴳ-⁻¹ D2) n = None). { apply nIn_iff_nMapsTo. intros InnD2. assert (In n (ᴳ-⁻¹ D1)) as InnD1. { unfold In; exists b0; assumption. } specialize (DisjointD1D2 n InnD1 InnD2). assumption. }
    apply map_MapsTo_iff in hiD1mapsto. destruct hiD1mapsto as (b1 & D1mapsto & b0eq). rewrite b0eq in *; clear b0 b0eq.
    assert (D2 n = None). { unfold hminus_inv in H. apply map_nMapsTo_iff in H. assumption. }
    unfold hminus_inv, union, merge_with, merge, map, Fun.map, Fun.merge, Fun.on_conflict_do in unionmapsto. destruct n, b1; simpl in *; rewrite D1mapsto, H0 in unionmapsto; inversion unionmapsto; inversion ValidOnlyD1. constructor.
  - assert (D1 n = None). { unfold hminus_inv in hiD1mapsto. apply map_nMapsTo_iff in hiD1mapsto. assumption. }
    assert (In n (ᴳ-⁻¹ (D1 ᴳ+ D2))). { unfold In; exists b; assumption. }
    rewrite In_hminus_inv_iff in H0. apply In_union_iff in H0. destruct H0. { destruct H0. congruence. } destruct H0 as (b2 & D2mapsto).
    assert ((ᴳ-⁻¹ D2) n = Some ((fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n0 => ₊ T ‗ n0
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end)) n b2)) as hiD2mapsto. { apply map_MapsTo_if. assumption. }
    specialize (ValidOnlyD2 n (fsimple (fun t : Type => t -> t) (fun _ : binding_var => ₓ ☠ ‗ ①) (fun binding : binding_dh => match binding with
| ₋ ¹ν ⌊ T ⌋ n0 => ₊ T ‗ n0
| ₊ _ ‗ _ => ₊ ① ‗ ☠
| _ => ₋ ☠ ⌊ ① ⌋ ☠
end) n b2) hiD2mapsto). unfold hminus_inv, union, merge_with, merge, map, Fun.map, Fun.merge, Fun.on_conflict_do in unionmapsto. destruct n, b2; simpl in *; rewrite D2mapsto, H in unionmapsto; inversion unionmapsto; inversion ValidOnlyD2. constructor.
Qed.

Lemma ValidOnly_hminus_inv_union' : forall (D1 D2 : ctx), Basics.impl (ValidOnly (ᴳ-⁻¹ D1) /\ ValidOnly (ᴳ-⁻¹ D2) /\ D1 # D2) (ValidOnly (ᴳ-⁻¹ (D1 ᴳ+ D2))).
Proof.
  intros * H. destruct H as (H1 & H2 & H3). apply ValidOnly_hminus_inv_union; assumption.
Qed.
Hint Rewrite <- ValidOnly_hminus_inv_union' : suffices.

Lemma ValidOnly_cshift_iff: forall (G : ctx) (H : hnames) (h' : hname), ValidOnly G <-> ValidOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold ValidOnly, ctx_cshift, ctx_shift.
  rewrite map_propagate_both with (Q := fun x b => IsValid (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- ValidOnly_cshift_iff : propagate_down.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* LinOnly *)
(*----------------------------------------------------------------------------*)
Lemma LinOnly_empty : LinOnly ᴳ{}.
Proof.
  scongruence unfold: LinOnly.
Qed.
Hint Resolve LinOnly_empty : autolemmas.

Lemma LinOnly_singleton_iff: forall (n : name) (binding: binding_type_of n), LinOnly (ctx_singleton n binding) <-> IsLin (mode_of binding).
Proof.
  intros n binding. split.
  - intros LinOnlySing. unfold LinOnly in LinOnlySing.
    specialize (LinOnlySing n binding). unfold ctx_singleton in LinOnlySing. specialize (LinOnlySing (singleton_MapsTo_at_elt n name_eq_dec binding)). assumption.
  - intros IsLinMode. unfold LinOnly. intros n' binding' mapstoSing. apply singleton_MapsTo_iff in mapstoSing. assert (n = n'). { apply eq_sigT_fst in mapstoSing. assumption. } subst. apply inj_pair2_eq_dec in mapstoSing. 2:{ exact name_eq_dec. } subst. assumption.
Qed.
Hint Rewrite LinOnly_singleton_iff : propagate_down.

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

Lemma LinOnly_wk_ValidOnly : forall (G : ctx), LinOnly G -> ValidOnly G.
Proof.
  intros *.
  sfirstorder use: IsLin_wk_IsValid.
Qed.

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

Lemma LinOnly_stimes_plus_backward : forall (G : ctx) (m1 m2: mode), LinOnly ((mode_plus m1 m2) ᴳ· G) -> LinOnly (m1 ᴳ· G) /\ LinOnly (m2 ᴳ· G).
Proof.
  intros * LinOnlym1m2. unfold LinOnly in *. split.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in LinOnlym1m2. specialize (LinOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (mode_plus m1 m2)
    | ʰ _ => stimes_dh (mode_plus m1 m2)
    end) n tyb')).
  unfold map, Fun.map in LinOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *;  simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (LinOnlym1m2 eq_refl).
  all: apply IsLin_times_iff in LinOnlym1m2; destruct LinOnlym1m2 as (IsLinplus & IsLinm0); apply IsLin_plus_backward in IsLinplus; destruct IsLinplus as (IsLinm1 & IsLinm2); apply IsLin_times_iff; split; assumption.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in LinOnlym1m2. specialize (LinOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (mode_plus m1 m2)
    | ʰ _ => stimes_dh (mode_plus m1 m2)
    end) n tyb')).
  unfold map, Fun.map in LinOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *;  simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (LinOnlym1m2 eq_refl).
  all: apply IsLin_times_iff in LinOnlym1m2; destruct LinOnlym1m2 as (IsLinplus & IsLinm0); apply IsLin_plus_backward in IsLinplus; destruct IsLinplus as (IsLinm1 & IsLinm2); apply IsLin_times_iff; split; assumption.
Qed.
Lemma LinOnly_stimes_plus_backward' : forall (G : ctx) (m1 m2: mode), Basics.impl (LinOnly ((mode_plus m1 m2) ᴳ· G)) (LinOnly (m1 ᴳ· G) /\ LinOnly (m2 ᴳ· G)).
Proof.
  exact LinOnly_stimes_plus_backward.
Qed.
Hint Rewrite LinOnly_stimes_plus_backward' : propagate_down.

Lemma LinOnly_stimes_times_backward : forall (G : ctx) (m1 m2: mode), LinOnly ((m1 · m2) ᴳ· G) -> LinOnly (m1 ᴳ· G) /\ LinOnly (m2 ᴳ· G).
Proof.
  intros * LinOnlym1m2. unfold LinOnly in *. split.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in LinOnlym1m2. specialize (LinOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (m1 · m2)
    | ʰ _ => stimes_dh (m1 · m2)
    end) n tyb')).
  unfold map, Fun.map in LinOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *;  simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (LinOnlym1m2 eq_refl).
  all: apply IsLin_times_iff in LinOnlym1m2; destruct LinOnlym1m2 as (IsLintimes & IsLinm0); apply IsLin_times_iff in IsLintimes; destruct IsLintimes as (IsLinm1 & IsLinm2); apply IsLin_times_iff; split; assumption.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in LinOnlym1m2. specialize (LinOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (m1 · m2)
    | ʰ _ => stimes_dh (m1 · m2)
    end) n tyb')).
  unfold map, Fun.map in LinOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *;  simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (LinOnlym1m2 eq_refl).
  all: apply IsLin_times_iff in LinOnlym1m2; destruct LinOnlym1m2 as (IsLintimes & IsLinm0); apply IsLin_times_iff in IsLintimes; destruct IsLintimes as (IsLinm1 & IsLinm2); apply IsLin_times_iff; split; assumption.
Qed.
Lemma LinOnly_stimes_times_backward' : forall (G : ctx) (m1 m2: mode), Basics.impl (LinOnly ((m1 · m2) ᴳ· G)) (LinOnly (m1 ᴳ· G) /\ LinOnly (m2 ᴳ· G)).
Proof.
  exact LinOnly_stimes_times_backward.
Qed.
Hint Rewrite LinOnly_stimes_times_backward' : propagate_down.

Lemma LinOnly_stimes_dec : forall (D1: ctx) (m' : mode), IsValid m' -> LinOnly (m' ᴳ· D1) -> { IsLin m' } + { IsUr m' /\ D1 = ᴳ{} }.
Proof.
  intros * Validmp LinOnlyD.
  destruct (IsLin_dec m'). { left. assumption. }
  right. assert (IsUr m'). { destruct m'. destruct p. destruct m. specialize (n (IsLinProof a)). contradiction. constructor. inversion Validmp. }
  split. assumption.
  apply ext_eq. rename n into NotLin. intros n.
    assert (LinOnly (m' ᴳ· D1)). { auto. } unfold LinOnly in H0. destruct (Empty_dec D1).
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

Lemma LinOnly_mode_times_backward : forall (m1 m2 : mode) (D : ctx), LinOnly (m1 · m2 ᴳ· D) -> LinOnly (m1 ᴳ· D) /\ LinOnly  (m2 ᴳ· D).
Proof. intros * LinOnlymD.
  split.
  rewrite mode_times_commutative in LinOnlymD.
  all: rewrite <- stimes_is_action in LinOnlymD; apply LinOnly_stimes_backward in LinOnlymD; assumption.
Qed.

Lemma LinOnly_mode_plus_backward : forall (m1 m2 : mode) (D : ctx), LinOnly ((mode_plus m1 m2) ᴳ· D) -> LinOnly (m1 ᴳ· D) /\ LinOnly (m2 ᴳ· D).
Proof. intros * LinOnlymD.
  rewrite <- stimes_mode_plus_eq in LinOnlymD.
  apply LinOnly_union_iff in LinOnlymD. sfirstorder.
Qed.

Lemma LinOnly_times_linone_forward : forall (m : mode) (D : ctx), LinOnly (m ᴳ· D) -> LinOnly ((¹↑ · m) ᴳ· D).
Proof.
  intros * LinOnlymD. rewrite <- stimes_is_action.
  apply LinOnly_stimes_forward. constructor. assumption.
Qed.

Lemma LinOnly_times_linone_backward : forall (m : mode) (D : ctx), LinOnly ((¹↑ · m) ᴳ· D) -> LinOnly (m ᴳ· D).
Proof.
  intros * LinOnlymD. rewrite <- stimes_is_action in LinOnlymD.
  apply LinOnly_stimes_backward in LinOnlymD. assumption.
Qed.

Lemma LinOnly_cshift_iff : forall (G : ctx) (H : hnames) (h' : hname), LinOnly G <-> LinOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold LinOnly, ctx_cshift, ctx_shift.
  rewrite map_propagate_both with (Q := fun x b => IsLin (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- LinOnly_cshift_iff : propagate_down.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* LinNuOnly *)
(*----------------------------------------------------------------------------*)
Lemma LinNuOnly_wk_LinOnly : forall (G : ctx), LinNuOnly G -> LinOnly G.
Proof.
  intros *.
  sfirstorder use: IsLinNu_wk_IsLin.
Qed.

Lemma LinNuOnly_wk_FinAgeOnly : forall (G : ctx), LinNuOnly G -> FinAgeOnly G.
Proof.
  intros *.
  sfirstorder use: IsLinNu_wk_IsFinAge.
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

Lemma LinNuOnly_stimes_linone_contra : forall (G : ctx), LinNuOnly (¹↑ ᴳ· G) -> G = ᴳ{}.
Proof.
  intros * contra.
  apply ext_eq. intros n. simpl.
  destruct (G n) eqn:Gmapsto. 2:{ reflexivity. }
  exfalso.
  specialize (contra n). unfold stimes in contra.
  assert ((¹↑ ᴳ· G) n = Some ((fsimple (fun t : Type => t -> t) (stimes_var ¹↑) (stimes_dh ¹↑)) n b)). { unfold stimes; apply map_MapsTo_if. assumption. }
  specialize (contra (fsimple (fun t : Type => t -> t) (stimes_var ¹↑) (stimes_dh ¹↑) n b) H).
  inversion contra. destruct n, b; simpl in H1; try destruct m; try destruct m0; try destruct n; try destruct n0; try destruct p; try destruct p0; try destruct m; try destruct m0; try destruct a; try destruct a0; inversion H1.
Qed.

Lemma LinNuOnly_cshift_iff : forall (G : ctx) (H : hnames) (h' : hname), LinNuOnly G <-> LinNuOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold LinNuOnly, ctx_cshift, ctx_shift.
  rewrite map_propagate_both with (Q := fun x b => IsLinNu (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- LinNuOnly_cshift_iff : propagate_down.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* FinAgeOnly *)
(*----------------------------------------------------------------------------*)
Lemma FinAgeOnly_singleton_iff: forall (n : name) (binding: binding_type_of n), FinAgeOnly (ctx_singleton n binding) <-> IsFinAge (mode_of binding).
Proof.
  intros n binding. split.
  - intros FinAgeOnlySing. unfold FinAgeOnly in FinAgeOnlySing.
    specialize (FinAgeOnlySing n binding). unfold ctx_singleton in FinAgeOnlySing. specialize (FinAgeOnlySing (singleton_MapsTo_at_elt n name_eq_dec binding)). assumption.
  - intros IsFinAgeMode. unfold FinAgeOnly. intros n' binding' mapstoSing. apply singleton_MapsTo_iff in mapstoSing. assert (n = n'). { apply eq_sigT_fst in mapstoSing. assumption. } subst. apply inj_pair2_eq_dec in mapstoSing. 2:{ exact name_eq_dec. } subst. assumption.
Qed.
Hint Rewrite FinAgeOnly_singleton_iff : propagate_down.

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

Lemma FinAgeOnly_stimes_plus_backward : forall (G : ctx) (m1 m2: mode), FinAgeOnly ((mode_plus m1 m2) ᴳ· G) -> FinAgeOnly (m1 ᴳ· G) /\ FinAgeOnly (m2 ᴳ· G).
Proof.
  intros * FinAgeOnlym1m2. unfold FinAgeOnly in *. split.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in FinAgeOnlym1m2. specialize (FinAgeOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (mode_plus m1 m2)
    | ʰ _ => stimes_dh (mode_plus m1 m2)
    end) n tyb')).
  unfold map, Fun.map in FinAgeOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *;  simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (FinAgeOnlym1m2 eq_refl).
  all: apply IsFinAge_times_iff in FinAgeOnlym1m2; destruct FinAgeOnlym1m2 as (IsFinAgeplus & IsFinAgem0); apply IsFinAge_plus_backward in IsFinAgeplus; destruct IsFinAgeplus as (IsFinAgem1 & IsFinAgem2); apply IsFinAge_times_iff; split; assumption.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in FinAgeOnlym1m2. specialize (FinAgeOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (mode_plus m1 m2)
    | ʰ _ => stimes_dh (mode_plus m1 m2)
    end) n tyb')).
  unfold map, Fun.map in FinAgeOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *; simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (FinAgeOnlym1m2 eq_refl).
  all: apply IsFinAge_times_iff in FinAgeOnlym1m2; destruct FinAgeOnlym1m2 as (IsFinAgeplus & IsFinAgem0); apply IsFinAge_plus_backward in IsFinAgeplus; destruct IsFinAgeplus as (IsFinAgem1 & IsFinAgem2); apply IsFinAge_times_iff; split; assumption.
Qed.
Lemma FinAgeOnly_stimes_plus_backward' : forall (G : ctx) (m1 m2: mode), Basics.impl (FinAgeOnly ((mode_plus m1 m2) ᴳ· G)) (FinAgeOnly (m1 ᴳ· G) /\ FinAgeOnly (m2 ᴳ· G)).
Proof.
  exact FinAgeOnly_stimes_plus_backward.
Qed.
Hint Rewrite FinAgeOnly_stimes_plus_backward' : propagate_down.

Lemma FinAgeOnly_stimes_times_backward : forall (G : ctx) (m1 m2: mode), FinAgeOnly ((m1 · m2) ᴳ· G) -> FinAgeOnly (m1 ᴳ· G) /\ FinAgeOnly (m2 ᴳ· G).
Proof.
  intros * FinAgeOnlym1m2. unfold FinAgeOnly in *. split.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in FinAgeOnlym1m2. specialize (FinAgeOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (m1 · m2)
    | ʰ _ => stimes_dh (m1 · m2)
    end) n tyb')).
  unfold map, Fun.map in FinAgeOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *;  simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (FinAgeOnlym1m2 eq_refl).
  all: apply IsFinAge_times_iff in FinAgeOnlym1m2; destruct FinAgeOnlym1m2 as (IsFinAgetimes & IsFinAgem0); apply IsFinAge_times_iff in IsFinAgetimes; destruct IsFinAgetimes as (IsFinAgem1 & IsFinAgem2); apply IsFinAge_times_iff; split; assumption.
  - intros n tyb mapsto. unfold stimes in mapsto. rewrite map_MapsTo_iff in mapsto. destruct mapsto as (tyb' & mapsto & tyb'eq). unfold stimes in FinAgeOnlym1m2. specialize (FinAgeOnlym1m2 n ((fun n0 : name => match n0 as n1 return (binding_type_of n1 -> binding_type_of n1) with
    | ˣ _ => stimes_var (m1 · m2)
    | ʰ _ => stimes_dh (m1 · m2)
    end) n tyb')).
  unfold map, Fun.map in FinAgeOnlym1m2. destruct n; destruct tyb; destruct tyb'; simpl in *; try unfold stimes_var in *; try unfold stimes_dh in *; simpl in *; inversion tyb'eq; rewrite mapsto in *; specialize (FinAgeOnlym1m2 eq_refl).
  all: apply IsFinAge_times_iff in FinAgeOnlym1m2; destruct FinAgeOnlym1m2 as (IsFinAgetimes & IsFinAgem0); apply IsFinAge_times_iff in IsFinAgetimes; destruct IsFinAgetimes as (IsFinAgem1 & IsFinAgem2); apply IsFinAge_times_iff; split; assumption.
Qed.
Lemma FinAgeOnly_stimes_times_backward' : forall (G : ctx) (m1 m2: mode), Basics.impl (FinAgeOnly ((m1 · m2) ᴳ· G)) (FinAgeOnly (m1 ᴳ· G) /\ FinAgeOnly (m2 ᴳ· G)).
Proof.
  exact FinAgeOnly_stimes_times_backward.
Qed.
Hint Rewrite FinAgeOnly_stimes_times_backward' : propagate_down.

Lemma FinAgeOnly_empty : FinAgeOnly ᴳ{}.
Proof.
  scongruence unfold: FinAgeOnly.
Qed.
Hint Resolve FinAgeOnly_empty : autolemmas.

Lemma FinAgeOnly_stimes_dec : forall (D1: ctx) (m': mode), IsValid m' -> FinAgeOnly (m' ᴳ· D1) -> { IsFinAge m' } + { D1 = ᴳ{} }.
Proof.
  intros * Validmp FinAgeOnlyD.
  destruct (IsFinAge_dec m'). { left. assumption. }
  right. apply ext_eq. rename n into NotFinAge. intros n.
    unfold FinAgeOnly in FinAgeOnlyD. destruct (Empty_dec D1).
    - rewrite e. cbn. reflexivity.
    - destruct e as (n' & mapstoD1). exfalso.
      unfold stimes in FinAgeOnlyD. specialize (FinAgeOnlyD n').
      pose proof mapstoD1 as inD1. rewrite <- In_iff_exists_Some in inD1. apply In_map_iff with (m := fun n : name => match n as n0 return (binding_type_of n0 -> binding_type_of n0) with
| ˣ _ => stimes_var m'
| ʰ _ => stimes_dh m'
end) in inD1. rewrite In_iff_exists_Some in inD1. destruct inD1 as (binding & mapstoMap). specialize (FinAgeOnlyD binding mapstoMap).
      destruct n'; unfold map, Fun.map in mapstoMap; simpl in mapstoMap; destruct mapstoD1 as (binding' & mapstoD1); rewrite mapstoD1 in mapstoMap; inversion mapstoMap.
      + inversion FinAgeOnlyD. inversion H0. destruct binding, binding'; unfold stimes_var, mode_times, mul_times in *; destruct m, m', m0; simpl in *; try congruence; try destruct p0; try destruct p1; try destruct p2; try destruct m; try destruct m0; try destruct m1; try destruct a; try destruct a0; try destruct a1; simpl in *; trivial; try congruence; try specialize (NotFinAge (IsFinAgeProof Lin n1)); try specialize (NotFinAge (IsFinAgeProof Ur n1)); assumption.
      + inversion FinAgeOnlyD. inversion H0. destruct binding, binding'; unfold stimes_var, mode_times, mul_times in *; try destruct m; try destruct m'; try destruct m0; try destruct n; try destruct n'; try destruct n0; try destruct n1; simpl in *; try congruence; try destruct p0; try destruct p1; try destruct p2; try destruct m; try destruct m0; try destruct m1; try destruct a; try destruct a0; try destruct a1; simpl in *; trivial; try congruence; try specialize (NotFinAge (IsFinAgeProof Lin n0)); try specialize (NotFinAge (IsFinAgeProof Ur n0)); try specialize (NotFinAge (IsFinAgeProof Lin n)); try specialize (NotFinAge (IsFinAgeProof Ur n)); try assumption.
Qed.

Lemma FinAgeOnly_mode_times_backward : forall (m1 m2 : mode) (D : ctx), FinAgeOnly (m1 · m2 ᴳ· D) -> FinAgeOnly (m1 ᴳ· D) /\ FinAgeOnly  (m2 ᴳ· D).
Proof. intros * FinAgeOnlymD.
  split.
  rewrite mode_times_commutative in FinAgeOnlymD.
  all: rewrite <- stimes_is_action in FinAgeOnlymD; apply FinAgeOnly_stimes_backward in FinAgeOnlymD; assumption.
Qed.

Lemma FinAgeOnly_mode_plus_backward : forall (m1 m2 : mode) (D : ctx), FinAgeOnly ((mode_plus m1 m2) ᴳ· D) -> FinAgeOnly (m1 ᴳ· D) /\ FinAgeOnly (m2 ᴳ· D).
Proof. intros * FinAgeOnlymD.
  rewrite <- stimes_mode_plus_eq in FinAgeOnlymD.
  apply FinAgeOnly_union_backward in FinAgeOnlymD. sfirstorder.
Qed.

Lemma FinAgeOnly_times_linone_forward : forall (m : mode) (D : ctx), FinAgeOnly (m ᴳ· D) -> FinAgeOnly ((¹↑ · m) ᴳ· D).
Proof.
  intros * FinAgeOnlymD. rewrite <- stimes_is_action.
  apply FinAgeOnly_stimes_forward. constructor. assumption.
Qed.

Lemma FinAgeOnly_times_linone_backward : forall (m : mode) (D : ctx), FinAgeOnly ((¹↑ · m) ᴳ· D) -> FinAgeOnly (m ᴳ· D).
Proof.
  intros * FinAgeOnlymD. rewrite <- stimes_is_action in FinAgeOnlymD.
  apply FinAgeOnly_stimes_backward in FinAgeOnlymD. assumption.
Qed.

Lemma FinAgeOnly_cshift_iff : forall (G : ctx) (H : hnames) (h' : hname), FinAgeOnly G <-> FinAgeOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold FinAgeOnly, ctx_cshift, ctx_shift.
  rewrite map_propagate_both with (Q := fun x b => IsFinAge (mode_of b)).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- FinAgeOnly_cshift_iff : propagate_down.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* DestOnly *)
(*----------------------------------------------------------------------------*)
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

Lemma DestOnly_empty : DestOnly ᴳ{}.
Proof.
  sauto q: on unfold: DestOnly.
Qed.
Hint Resolve DestOnly_empty : autolemmas.

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

Lemma DestOnly_Disjoint_singleton_var' : forall (G : ctx) (x : var) (m : mode) (T : type), Basics.impl (DestOnly G) (G # (ᴳ{ x : m ‗ T})).
Proof.
  exact DestOnly_Disjoint_singleton_var.
Qed.
(* Hint Rewrite <- DestOnly_Disjoint_singleton_var' : suffices. *)

Lemma DestOnly_singleton_dest : forall (h : hname) (m n : mode) (T : type), DestOnly ᴳ{- h : m ⌊ T ⌋ n}.
Proof.
  unfold DestOnly, ctx_singleton, IsDest. intros * mapsto.
  apply singleton_MapsTo_iff in mapsto. pose proof mapsto as mapsto'. apply eq_sigT_fst in mapsto. destruct x; try congruence. inversion mapsto. rewrite <- H0 in *. apply inj_pair2_eq_dec in mapsto'. rewrite <- mapsto' in *. trivial. exact name_eq_dec.
Qed.

Lemma DestOnly_wk_NoVar : forall (D : ctx), DestOnly D -> NoVar D.
Proof.
  intros * H. unfold DestOnly in H. unfold NoVar. intros nam b mapstoD. specialize (H nam b mapstoD). destruct nam. { inversion H. } { intros contra. inversion contra. }
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

Lemma DestOnly_union_singleton_x_at_x : forall (D : ctx) (x : var) (m : mode) (T : type), DestOnly D -> (D ᴳ+ ᴳ{ x : m ‗ T}) (ˣ x) = Some (ₓ m ‗ T).
Proof.
  intros * DestOnlyD.
  unfold union. apply merge_with_None_Some_eq with (f := D). split.
  + apply DestOnly_nMapsTo_var. assumption.
  + apply singleton_MapsTo_at_elt.
Qed.

Lemma DestOnly_singleton_var_contra : forall (x : var) (m : mode) (T : type), DestOnly ᴳ{ x : m ‗ T} -> False.
Proof.
  intros * DestOnlyD.
  unfold DestOnly in DestOnlyD. specialize (DestOnlyD (ˣ x) (ₓ m ‗ T)). unfold ctx_singleton in DestOnlyD. rewrite singleton_MapsTo_at_elt in DestOnlyD. specialize (DestOnlyD eq_refl). inversion DestOnlyD.
Qed.
Lemma DestOnly_singleton_var_contra' : forall (x : var) (m : mode) (T : type), Basics.impl (DestOnly ᴳ{ x : m ‗ T}) False.
Proof.
  exact DestOnly_singleton_var_contra.
Qed.
Hint Rewrite DestOnly_singleton_var_contra' : propagate_down.

Lemma DestOnly_singleton_hole_contra : forall (h : hname) (T : type) (n : mode), DestOnly ᴳ{+ h : T ‗ n} -> False.
Proof.
  intros * DestOnlyD.
  unfold DestOnly in DestOnlyD. specialize (DestOnlyD (ʰ h) (₊ T ‗ n)). unfold ctx_singleton in DestOnlyD. rewrite singleton_MapsTo_at_elt in DestOnlyD. specialize (DestOnlyD eq_refl). inversion DestOnlyD.
Qed.
Lemma DestOnly_singleton_hole_contra' : forall (h : hname) (T : type) (n : mode), Basics.impl (DestOnly ᴳ{+ h : T ‗ n}) False.
Proof.
  exact DestOnly_singleton_hole_contra.
Qed.
Hint Rewrite DestOnly_singleton_hole_contra' : propagate_down.

Lemma DestOnly_hminus : forall (D : ctx), HoleOnly D -> DestOnly (ᴳ- D).
Proof.
  intros * HoleOnlyD.
  intros n b hMapsto. unfold hminus in hMapsto. apply map_MapsTo_iff in hMapsto. destruct hMapsto as (b' & mapsto & beq). rewrite beq in *; clear beq. specialize (HoleOnlyD n b' mapsto).
  destruct n, b'; simpl in *; trivial.
Qed.

Lemma DestOnly_hminus' : forall (D : ctx), Basics.impl (HoleOnly D) (DestOnly (ᴳ- D)).
Proof.
  intros * H. apply DestOnly_hminus. assumption.
Qed.
Hint Rewrite <- DestOnly_hminus' : suffices.

Lemma DestOnly_VarOnly_contra : forall (D : ctx), DestOnly D -> VarOnly D -> D = ᴳ{}.
Proof.
  intros D DestOnlyD VarOnlyD.
  apply DestOnly_wk_NoVar in DestOnlyD.
  apply ext_eq. intros n. destruct (D n) eqn:mapsto.
  specialize (DestOnlyD n b mapsto). specialize (VarOnlyD n b mapsto). congruence.
  simpl. reflexivity.
Qed.

Lemma DestOnly_cshift_iff: forall (G : ctx) (H : hnames) (h' : hname), DestOnly G <-> DestOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold DestOnly, ctx_cshift, ctx_shift.
  rewrite map_propagate_both with (Q := fun x b => IsDest _ b).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- DestOnly_cshift_iff : propagate_down.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* HoleOnly (we implemented only the few lemmas needed for the proof of type safety, as HoleOnly doesn't appear often) *)
(*----------------------------------------------------------------------------*)
Lemma HoleOnly_hminus_inv : forall (G : ctx), ValidOnly (ᴳ-⁻¹ G) -> HoleOnly (ᴳ-⁻¹ G).
Proof.
  intros * ValidOnlyhiG n b hiGmapsto. specialize (ValidOnlyhiG n b hiGmapsto).
  unfold hminus_inv in hiGmapsto. rewrite map_MapsTo_iff in hiGmapsto. destruct hiGmapsto as (b' & Gmapsto & H). destruct n, b; simpl in *.
  - inversion H; subst. inversion ValidOnlyhiG.
  - destruct b'; try destruct m0; try destruct p; try destruct m0; try destruct a; try destruct n1; try inversion H; subst; try congruence; try inversion ValidOnlyhiG.
  - destruct b'; try destruct m0; try destruct p; try destruct m0; try destruct a; try destruct n1; try inversion H; subst; try congruence; try inversion ValidOnlyhiG. trivial.
Qed.

Lemma HoleOnly_hminus_inv' : forall (G : ctx), Basics.impl (ValidOnly (ᴳ-⁻¹ G)) (HoleOnly (ᴳ-⁻¹ G)).
Proof.
  intros * H. apply HoleOnly_hminus_inv. assumption.
Qed.
Hint Rewrite <- HoleOnly_hminus_inv' : suffices.

Lemma HoleOnly_stimes_iff : forall (m : mode) (G : ctx), HoleOnly G <-> HoleOnly (m ᴳ· G).
Proof.
  intros *. unfold HoleOnly, stimes.
  rewrite map_propagate_both'.
  { sfirstorder. }
  unfold IsHole.
  hauto lq: on.
Qed.
Hint Rewrite <- HoleOnly_stimes_iff : propagate_down.
Hint Rewrite <- HoleOnly_stimes_iff : suffices.

Lemma HoleOnly_union_backward : forall (G1 G2 : ctx), HoleOnly (G1 ᴳ+ G2) -> ValidOnly (G1 ᴳ+ G2) -> HoleOnly G1 /\ HoleOnly G2.
  intros * HoleOnlyU ValidOnlyU. unfold HoleOnly, union. split.
  - intros n b G1mapsto. destruct (G2 n) eqn:G2mapsto.
    * assert ((G1 ᴳ+ G2) n = Some ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b b0)). { unfold union; simpl. unfold Fun.merge, Fun.on_conflict_do; rewrite G1mapsto; rewrite G2mapsto; simpl; reflexivity. }
      specialize (HoleOnlyU n ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b b0) H). specialize (ValidOnlyU n ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b b0) H). unfold IsHole in HoleOnlyU. inversion ValidOnlyU. destruct n; try destruct b; try destruct b0; simpl in *; try destruct (type_eq_dec T T0); try destruct (mode_eq_dec n n0); simpl in *; try congruence; trivial.
    * assert ((G1 ᴳ+ G2) n = Some b). { unfold union; simpl. unfold Fun.merge, Fun.on_conflict_do; rewrite G1mapsto; rewrite G2mapsto; simpl; reflexivity. }
      specialize (HoleOnlyU n b H). specialize (ValidOnlyU n b H). unfold IsHole in HoleOnlyU. inversion ValidOnlyU. destruct n, b; simpl in *; try congruence; trivial.
  - intros n b G2mapsto. destruct (G1 n) eqn:G1mapsto.
    * assert ((G1 ᴳ+ G2) n = Some ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b0 b)). { unfold union; simpl. unfold Fun.merge, Fun.on_conflict_do; rewrite G1mapsto; rewrite G2mapsto; simpl; reflexivity. }
      specialize (HoleOnlyU n ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b0 b) H). specialize (ValidOnlyU n ((fsimple (fun t : Type => t -> t -> t) union_var union_dh) n b0 b) H). unfold IsHole in HoleOnlyU. inversion ValidOnlyU. destruct n; try destruct b0; try destruct b; simpl in *; try destruct (type_eq_dec T T0); try destruct (mode_eq_dec n n0); simpl in *; try congruence; trivial.
    * assert ((G1 ᴳ+ G2) n = Some b). { unfold union; simpl. unfold Fun.merge, Fun.on_conflict_do; rewrite G1mapsto; rewrite G2mapsto; simpl; reflexivity. }
      specialize (HoleOnlyU n b H). specialize (ValidOnlyU n b H). unfold IsHole in HoleOnlyU. inversion ValidOnlyU. destruct n, b; simpl in *; try congruence; trivial.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* VarOnly *)
(*----------------------------------------------------------------------------*)
Lemma VarOnly_union_iff : forall (G1 G2 : ctx), VarOnly (G1 ᴳ+ G2) <-> VarOnly G1 /\ VarOnly G2.
Proof.
  intros *. unfold VarOnly, union.
  apply merge_with_propagate_both.
  intros [xx|xh]. all: cbn. { sfirstorder. }
  intros b1 b2. unfold union_dh. destruct b1, b2;
  destruct (type_eq_dec T T0), (mode_eq_dec n n0). all:sfirstorder.
Qed.
Hint Rewrite VarOnly_union_iff : propagate_down.
Lemma VarOnly_stimes_iff : forall (m : mode) (G : ctx), VarOnly G <-> VarOnly (m ᴳ· G).
Proof.
  intros *. unfold VarOnly, stimes.
  rewrite map_propagate_both'.
  { sfirstorder. }
  unfold IsVar. intros *; simpl. destruct x; sfirstorder.
Qed.
Hint Rewrite <- VarOnly_stimes_iff : propagate_down.

Lemma VarOnly_singleton_var : forall (x : var) (m : mode) (T : type), VarOnly ᴳ{ x : m ‗ T}.
Proof.
  unfold VarOnly, ctx_singleton, IsVar. intros * mapsto.
  apply singleton_MapsTo_iff in mapsto. pose proof mapsto as mapsto'. apply eq_sigT_fst in mapsto. destruct x0; try congruence. inversion mapsto. rewrite <- H0 in *. apply inj_pair2_eq_dec in mapsto'. trivial. exact name_eq_dec.
Qed.

Lemma VarOnly_union_NoVar_is_Disjoint : forall (P1 G2 : ctx), VarOnly P1 -> NoVar G2 -> P1 # G2.
Proof.
  intros * VarOnlyP NoVarG. unfold Disjoint. intros nam inP1 inG2. unfold VarOnly, NoVar, Fun.In, IsVar in *. destruct inP1; specialize (VarOnlyP nam x H). destruct inG2; specialize (NoVarG nam x0 H0). destruct nam; simpl in *; congruence.
Qed.

Lemma VarOnly_nMapsTo_hd : forall (P : ctx) (h : hname), VarOnly P -> P (ʰ h) = None.
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
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* DisposableOnly *)
(*----------------------------------------------------------------------------*)
Lemma DisposableOnly_empty : DisposableOnly ᴳ{}.
Proof.
  sauto q: on unfold: DisposableOnly.
Qed.
Hint Resolve DisposableOnly_empty : autolemmas.

Lemma DisposableOnly_stimes : forall (P : ctx) (m : mode), IsValid m -> DisposableOnly P -> DisposableOnly (m ᴳ· P).
Proof.
  intros * validm dispoP.
  unfold DisposableOnly in *.
  intros n b h.
  unfold stimes in h.
  rewrite map_MapsTo_iff in h. destruct h. destruct H.
  specialize (dispoP n x H). destruct n.
  - unfold stimes_var in H0. destruct x. subst. unfold mode_of in *. destruct m, m0; try destruct p; try destruct p0; try destruct m; try destruct m0; unfold mode_times, mul_times in *; cbn; try constructor; try inversion dispoP; try inversion validm.
  - unfold stimes_dh in H0. destruct x; subst; unfold mode_of in *; try rename n into m0; destruct m, m0; try destruct p; try destruct p0; try destruct m; try destruct m0; unfold mode_times, mul_times in *; cbn; try constructor; try inversion dispoP; try inversion validm.
Qed.

Lemma nDisposable_in_LinOnly: forall (P D : ctx), DisposableOnly P -> LinOnly (P ᴳ+ D) -> (P ᴳ+ D) = D.
Proof.
  intros * DisposP LinOnlyPuD.
  assert (P = ᴳ{}) as Pempty.
  { apply ext_eq. intros n. destruct (In_dec n P) as [[y h_inP]|h_ninP].
    - unfold DisposableOnly in DisposP. specialize (DisposP n y h_inP). unfold IsDisposable in DisposP.
      unfold LinOnly in LinOnlyPuD. assert (In n P) as inP. { exists y. assumption. } assert (In n (P ᴳ+ D)) as InPuD. { apply In_union_forward_l. assumption. } destruct InPuD as (y' & mapstoPuD). specialize (
      LinOnlyPuD n y' mapstoPuD). inversion LinOnlyPuD.
      assert (mode_of y ⥶ mode_of y'). { apply IsSubtype_union with (P := P) (D := D). all:assumption. } destruct n, y; try destruct n; inversion DisposP; rewrite <- H0, <- H1 in H; inversion H; inversion H5.
    - apply nIn_iff_nMapsTo. assumption.
  }
  rewrite Pempty. symmetry. apply union_empty_l_eq.
Qed.

Lemma DisposableOnly_union_forward : forall (P1 P2 : ctx), DisposableOnly P1 -> DisposableOnly P2 -> P1 # P2 -> DisposableOnly (P1 ᴳ+ P2).
Proof.
  intros P1 P2 DisposP1 DisposP2 DisjointP12.
  unfold DisposableOnly in *.
  intros n b mapsto.
  destruct (P1 n) as [b1|] eqn:mapstoP1, (P2 n) as [b2|] eqn:mapstoP2; unfold union in mapsto.
  - exfalso. apply Disjoint_MapsTo_contra with (2 := mapstoP1) (3:= mapstoP2); assumption.
  - specialize (DisposP1 n b1 mapstoP1).
    rewrite merge_with_Some_None_eq with (y1 := b1) in mapsto. inversion mapsto; subst. all:auto.
  - specialize (DisposP2 n b2 mapstoP2).
    rewrite merge_with_None_Some_eq with (y2 := b2) in mapsto. inversion mapsto; subst. all:auto.
  - assert (merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) P1 P2 n = None). { rewrite merge_with_None_None_eq; auto. }
    rewrite H in mapsto. congruence.
Qed.

Lemma DisposableOnly_union_backward : forall (P1 P2 : ctx), DisposableOnly (P1 ᴳ+ P2) -> P1 # P2 -> DisposableOnly P1 /\ DisposableOnly P2.
Proof.
  intros P1 P2 DisposP12 DisjointP12.
  unfold DisposableOnly in *.
  split.
  - intros n b1 mapstoP1. destruct (P2 n) as [b2|] eqn:mapstoP2.
    exfalso. apply Disjoint_MapsTo_contra with (2 := mapstoP1) (3:= mapstoP2); assumption.
    assert ((P1 ᴳ+ P2) n = Some b1). { unfold union. rewrite merge_with_Some_None_eq with (y1 := b1); auto. }
    specialize (DisposP12 n b1 H). assumption.
  - intros n b2 mapstoP2. destruct (P1 n) as [b1|] eqn:mapstoP1.
    exfalso. apply Disjoint_MapsTo_contra with (2 := mapstoP1) (3:= mapstoP2); assumption.
    assert ((P1 ᴳ+ P2) n = Some b2). { unfold union. rewrite merge_with_None_Some_eq with (y2 := b2); auto. }
    specialize (DisposP12 n b2 H). assumption.
Qed.

Lemma DisposableOnly_singleton_var : forall (x : var) (m : mode) (T : type), DisposableOnly (ᴳ{ x : m ‗ T}) <-> IsUr m.
Proof.
  intros *.
  unfold DisposableOnly.
  split.
  - intros * DisposSing.
    specialize (DisposSing (ˣ x) (ₓ m ‗ T)). assert (ᴳ{ x : m ‗ T} (ˣ x) = Some (ₓ m ‗ T)). { unfold ctx_singleton. rewrite singleton_MapsTo_at_elt. reflexivity. } specialize (DisposSing H). simpl in DisposSing. assumption.
  - intros IsUrm * mapsto.
    unfold ctx_singleton in mapsto. rewrite singleton_MapsTo_iff in mapsto.
    assert ((ˣ x) = n). { apply eq_sigT_fst in mapsto. assumption. } subst. apply inj_pair2_eq_dec in mapsto. subst. simpl. assumption. exact name_eq_dec.
Qed.

Lemma DisposableOnly_stimes_DestOnly_forward : forall (D : ctx) (m : mode), IsUr m -> DestOnly D -> ValidOnly D -> DisposableOnly (m ᴳ· D).
Proof.
  intros D m IsUrm DestOnlyD ValidOnlyD.
  unfold DisposableOnly.
  intros n b mapsto. unfold stimes in mapsto.
  apply map_MapsTo_iff in mapsto. destruct mapsto as (b' & mapstoD & beq).
  rewrite beq in *. clear beq b. unfold IsDisposable. specialize (DestOnlyD n b' mapstoD). specialize (ValidOnlyD n b' mapstoD).
  destruct n, b'; unfold stimes; simpl in *; unfold mode_times; inversion IsUrm; try congruence; destruct m0; try destruct p; try destruct m0; try destruct m1; simpl in *; try contradiction; try constructor; try inversion ValidOnlyD.
Qed.

Lemma DisposableOnly_wk_ValidOnly : forall (D : ctx), DisposableOnly D -> ValidOnly D.
Proof.
  intros D DisposD.
  unfold DisposableOnly, ValidOnly in *.
  intros n b mapsto.
  specialize (DisposD n b mapsto).
  destruct n, b; simpl in *; try destruct m; try contradiction; try constructor; try inversion DisposD.
Qed.

Lemma DisposableOnly_LinOnly_contra : forall (P : ctx), DisposableOnly P -> LinOnly P -> P = ᴳ{}.
Proof.
  intros P DisposP LinOnlyP.
  apply ext_eq. intros n. destruct (P n) eqn:mapsto.
  specialize (DisposP n b mapsto). specialize (LinOnlyP n b mapsto). unfold IsDisposable in DisposP. inversion LinOnlyP.
  destruct n, b; simpl in *; try destruct m; try contradiction; try constructor; try inversion DisposP; subst; try congruence.
  simpl; reflexivity.
Qed.

Lemma DisposableOnly_cshift_iff: forall (G : ctx) (H : hnames) (h' : hname), DisposableOnly G <-> DisposableOnly (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold DisposableOnly, ctx_cshift, ctx_shift.
  erewrite map_propagate_both with (Q := fun x b => IsDisposable _ b).
  2:{ intros [xx|xh] **. all: cbn.
      all: reflexivity. }
  apply precomp_propagate_both. intros x2.
  sfirstorder use: pre_cshift_surjective.
Qed.
Hint Rewrite <- DisposableOnly_cshift_iff : propagate_down.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* UserDefined (used when proving derived typing rules of syntactic sugar forms) *)
(*----------------------------------------------------------------------------*)
Lemma UserDefined_union_iff : forall (G1 G2 : ctx), UserDefined (G1 ᴳ+ G2) <-> UserDefined G1 /\ UserDefined G2.
Proof.
  intros *.
  unfold UserDefined.
  split.
  - intros UserDefinedG12.
    split; intros x Hin.
    + apply UserDefinedG12. apply In_union_iff. left. assumption.
    + apply UserDefinedG12. apply In_union_iff. right. assumption.
  - intros [UserDefinedG1 UserDefinedG2] x Hin.
    apply In_union_iff in Hin.
    destruct Hin as [Hin1 | Hin2].
    + apply UserDefinedG1. assumption.
    + apply UserDefinedG2. assumption.
Qed.

Lemma UserDefined_stimes : forall (G : ctx) (m : mode), UserDefined G -> UserDefined (m ᴳ· G).
Proof.
  intros * UserDefinedG.
  unfold UserDefined in *.
  intros x Hin.
  apply In_stimes_iff in Hin.
  specialize (UserDefinedG x Hin).
  assumption.
Qed.

Lemma UserDefined_Disjoint : forall (G : ctx) (x : var) (m : mode) (T : type), UserDefined G -> x <= max_runtime_var -> G # ᴳ{ x : m ‗ T}.
Proof.
  intros * UserDefinedG infMaxRuntime.
  unfold UserDefined in UserDefinedG.
  unfold Disjoint.
  intros * Hin1 Hin2.
  destruct x0.
  - apply In_singleton_iff in Hin2. inversion Hin2. subst.
    specialize (UserDefinedG x Hin1).
    lia.
  - apply In_singleton_iff in Hin2. inversion Hin2.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Predicates related to hnames: HIn, HSubset and HDisjoint *)
(*----------------------------------------------------------------------------*)
Lemma HIn_stimes_iff : forall (m : mode) (G : ctx) (h: hname), HNames.In h hnamesᴳ(m ᴳ· G) <-> HNames.In h hnamesᴳ(G).
Proof.
  sauto lq: on use: hnames_spec, map_MapsTo_iff.
Qed.

Lemma HIn_union_iff : forall (G G': ctx) (h: hname), HNames.In h hnamesᴳ(G ᴳ+ G') <-> HNames.In h hnamesᴳ(G) \/ HNames.In h hnamesᴳ(G').
Proof.
  intros *. split.
  - intros Hin. apply hnames_spec in Hin. rewrite hnames_spec, hnames_spec. destruct Hin as [x Hin]. destruct (In_dec (name_DH h) G) as [inG|notinG], (In_dec (name_DH h) G') as [inG'|notinG']; try unfold In, Fun.In in inG; try unfold In, Fun.In in inG'.
    + left. assumption.
    + left. assumption.
    + right. assumption.
    + assert (In (ʰ h) (G ᴳ+ G')). { unfold In, Fun.In. exists x. assumption. } apply In_merge_iff in H. unfold In, Fun.In in H. assumption.
  - intros [inG|inG'].
    + apply hnames_spec. rewrite hnames_spec in inG. destruct inG as [x inG]. destruct (In_dec (ʰ h) G').
      * unfold In, Fun.In in H. destruct H as (y & H). exists (union_dh x y). apply merge_with_Some_Some_eq. split; assumption.
      * rewrite nIn_iff_nMapsTo in H. exists x. apply merge_with_Some_None_eq. split; assumption.
    + apply hnames_spec. rewrite hnames_spec in inG'. destruct inG' as [x inG']. destruct (In_dec (ʰ h) G).
      * unfold In, Fun.In in H. destruct H as (y & H). exists (union_dh y x). apply merge_with_Some_Some_eq. split; assumption.
      * rewrite nIn_iff_nMapsTo in H. exists x. apply merge_with_None_Some_eq. split; assumption.
Qed.

Lemma nIn_impl_nHin : forall (G : ctx) (h : hname), ~ In (ʰ h) G -> ~ HNames.In h hnamesᴳ(G).
Proof.
  intros * nIn. intro Hin. apply hnames_spec in Hin. destruct Hin as (b & mapsto). contradiction nIn. exists b. assumption.
Qed.

Lemma HDisjoint_hempty_r : forall (H : hnames), H ## HNames.empty.
Proof.
  intros H. unfold HDisjoint. unfold HNames.Empty. intros h Hin. rewrite HNames.inter_spec in Hin. destruct Hin. inversion H1.
Qed.

Lemma HDisjoint_hempty_l : forall (H : hnames), HNames.empty ## H.
Proof.
  intros H. unfold HDisjoint. unfold HNames.Empty. intros h Hin. rewrite HNames.inter_spec in Hin. destruct Hin. inversion H0.
Qed.

Lemma HDisjoint_commutative : forall (H1 H2 : hnames), H1 ## H2 <-> H2 ## H1.
Proof.
  intros. split.
  intros H h contra. contradiction (H h). apply HNames.inter_spec. apply HNames.inter_spec in contra. split; tauto.
  intros H h contra. contradiction (H h). apply HNames.inter_spec. apply HNames.inter_spec in contra. split; tauto.
Qed.

Lemma HDisjoint_wk_remove : forall (H1 H2 : hnames) (h' : hname), H1 ## H2 -> HNames.remove h' H1 ## H2.
Proof.
  intros * H h contra. contradiction (H h). apply HNames.inter_spec. apply HNames.inter_spec in contra. destruct contra as (InH1 & InH2). apply HNames.remove_spec in InH1. destruct InH1 as (InH1 & neq). split; tauto.
Qed.

Lemma HSubset_union_backward : forall (G G': ctx) (H: hnames), HNames.Subset hnamesᴳ(G ᴳ+ G') H -> HNames.Subset hnamesᴳ(G) H /\ HNames.Subset hnamesᴳ(G') H.
Proof.
  unfold HNames.Subset in *. intros *. intros Hyp. split.
  - intros h Hin. specialize (Hyp h). apply Hyp, HIn_union_iff. left. assumption.
  - intros h Hin. specialize (Hyp h). apply Hyp, HIn_union_iff. right. assumption.
Qed.
Lemma HSubset_union_backward' : forall (G G': ctx) (H: hnames), Basics.impl (HNames.Subset hnamesᴳ(G ᴳ+ G') H) (HNames.Subset hnamesᴳ(G) H /\ HNames.Subset hnamesᴳ(G') H).
Proof.
  exact HSubset_union_backward.
Qed.
Hint Rewrite HSubset_union_backward' : propagate_down.

Lemma HSubset_stimes_backward : forall (m : mode) (G : ctx) (H: hnames), HNames.Subset hnamesᴳ(m ᴳ· G) H -> HNames.Subset hnamesᴳ(G) H.
Proof.
  unfold HNames.Subset in *. intros *. intros Hyp h Hin. specialize (Hyp h). apply Hyp, HIn_stimes_iff. assumption.
Qed.
Lemma HSubset_stimes_backward' : forall (m : mode) (G : ctx) (H: hnames), Basics.impl (HNames.Subset hnamesᴳ(m ᴳ· G) H) (HNames.Subset hnamesᴳ(G) H).
Proof.
  exact HSubset_stimes_backward.
Qed.
Hint Rewrite HSubset_stimes_backward' : propagate_down.

Lemma HSubset_impl_lt_max : forall (H H' : hnames), HNames.Subset H H' -> maxᴴ(H) <= maxᴴ(H').
Proof.
  intros *. unfold HNames.Subset. intros Hyp. unfold hname_max. destruct (HNames.max_elt H) as [h|] eqn:eMax.
    - apply HNames.max_elt_spec1 in eMax. specialize (Hyp h eMax).
      destruct (HNames.max_elt H') as [h'|] eqn:eMax'.
      + assert (~(h'<h)). { apply HNames.max_elt_spec2 with (s := H'). all:assumption. }
        apply not_lt_le; assumption.
      + apply HNames.max_elt_spec3 in eMax'. unfold HNames.Empty in eMax'. specialize (eMax' h). congruence.
    - apply Nat.le_0_l.
Qed.

Lemma HSubset_weaken_l : forall (H H' H'' : hnames), HNames.Subset H H' -> HNames.Subset H (H' ∪ H'').
Proof.
  intros *. unfold HNames.Subset. intros Hyp h Hin. apply HNamesFacts.union_iff. left. apply Hyp. assumption.
Qed.

Lemma HSubset_weaken_r : forall (H H' H'' : hnames), HNames.Subset H H'' -> HNames.Subset H (H' ∪ H'').
Proof.
  intros *. unfold HNames.Subset. intros Hyp h Hin. apply HNamesFacts.union_iff. right. apply Hyp. assumption.
Qed.

Lemma HSubset_preserves_HDisjoint : forall (H1 H2 H3 : hnames), HNames.Subset H1 H2 -> HDisjoint H2 H3 -> HDisjoint H1 H3.
Proof.
  intros * H1H2 H2H3. unfold HDisjoint, HNames.Subset, HNames.Empty in *.
  intros h. specialize (H1H2 h). specialize (H2H3 h).
  intros HinInter. apply HNames.inter_spec in HinInter. destruct HinInter as [H1h H3h]. specialize (H1H2 H1h). destruct H2H3. apply HNames.inter_spec. split; assumption.
Qed.

(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of hunion *)
(*----------------------------------------------------------------------------*)
Lemma hunion_hempty_l_eq : forall (H : hnames), H = (HNames.empty ∪ H).
Proof.
  intros H.
  apply HNames.eq_leibniz. unfold HNames.eq.
  intros h. rewrite HNamesFacts.union_iff. (* Definition of set equality *)
  split.
  - right; tauto.
  - intros [H1 | H2]. (* By definition of union, we can prove any goal if it is in one of the two sets *)
    + inversion H1.
    + tauto.
Qed.

Lemma hunion_hempty_r_eq : forall (H : hnames), H = (HNames.union H HNames.empty).
Proof.
  intros H.
  apply HNames.eq_leibniz. unfold HNames.eq.
  intros h. rewrite HNamesFacts.union_iff. (* Definition of set equality *)
  split.
  - intros H'. left; assumption.
  - intros [H1 | H2]. (* By definition of union, we can prove any goal if it is in one of the two sets *)
    + tauto.
    + inversion H2.
Qed.

Lemma hunion_commutative : forall (H H' : HNames.t), H ∪ H' = H' ∪ H.
Proof.
  intros. apply HNames.eq_leibniz. intros h. rewrite 2 HNames.union_spec. tauto.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of hnames *)
(*----------------------------------------------------------------------------*)
Lemma hnames_empty_is_hempty : hnamesᴳ(ᴳ{}) = HNames.empty.
Proof.
  unfold hnames_ctx, hnames_dom, ctx_empty. rewrite dom_empty_eq_nil. reflexivity.
Qed.

Lemma hnames_distrib_on_union : forall (G1 G2 : ctx), hnamesᴳ(G1 ᴳ+ G2) = hnamesᴳ(G1) ∪ hnamesᴳ(G2).
Proof.
  intros *.
  apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros *.
  rewrite HNamesFacts.union_iff. apply HIn_union_iff.
Qed.

Lemma hnames_hminus_inv_eq : forall (D : ctx), hnamesᴳ( (ᴳ-⁻¹ D)) = hnamesᴳ( D).
Proof.
  intros D. apply HNames.eq_leibniz. unfold HNames.eq. intros h. rewrite! hnames_spec. split.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus_inv in Hin. rewrite In_map_iff in Hin. rewrite <- In_iff_exists_Some. assumption.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus_inv. rewrite <- In_iff_exists_Some. rewrite In_map_iff. assumption.
Qed.

Lemma hnames_hminus_eq : forall (D : ctx), hnamesᴳ( (ᴳ- D)) = hnamesᴳ( D).
Proof.
  intros D. apply HNames.eq_leibniz. unfold HNames.eq. intros h. rewrite! hnames_spec. split.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus in Hin. rewrite In_map_iff in Hin. rewrite <- In_iff_exists_Some. assumption.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold hminus. rewrite <- In_iff_exists_Some. rewrite In_map_iff. assumption.
Qed.

Lemma hnames_stimes_eq : forall (m : mode) (D : ctx), hnamesᴳ( m ᴳ· D) = hnamesᴳ( D).
Proof.
  intros m D. apply HNames.eq_leibniz. unfold HNames.eq. intros h. rewrite! hnames_spec. split.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold stimes in Hin. rewrite In_map_iff in Hin. rewrite <- In_iff_exists_Some. assumption.
  - intros Hin. rewrite <- In_iff_exists_Some in Hin. unfold stimes. rewrite <- In_iff_exists_Some. rewrite In_map_iff. assumption.
Qed.

Lemma hnames_C_wk_hnames_G : forall (C : ectxs) (D : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), HNames.Subset hnamesᴳ(D) hnames©(C).
Proof.
  intros * TyC. induction TyC.
  { cbn. unfold hnames_ctx, ctx_empty.
    rewrite dom_empty_eq_nil. reflexivity. }
  all:
      try (cbn; unfold HNames.Subset; apply HSubset_union_backward in IHTyC; destruct IHTyC as (IHTyC1 & IHTyC2);  try apply HSubset_stimes_backward in IHTyC1; unfold HNames.Subset in IHTyC1 ; intros h Hin; specialize (IHTyC1 h Hin); apply HNamesFacts.union_iff; right; assumption);
      try (cbn; unfold HNames.Subset; apply HSubset_union_backward in IHTyC; destruct IHTyC as (IHTyC1 & IHTyC2); try apply HSubset_stimes_backward in IHTyC2; unfold HNames.Subset in IHTyC2; intros h Hin; specialize (IHTyC2 h Hin); apply HNamesFacts.union_iff; right; assumption);
      try (cbn; unfold HNames.Subset in * ; intros h Hin; specialize (IHTyC h Hin); apply HNamesFacts.union_iff; right; assumption).
  simpl. unfold HNames.Subset in *. intros h Hin. apply HNamesFacts.union_iff. apply HIn_union_iff in Hin. destruct Hin as [inD1|inD3].
  - right. apply HIn_stimes_iff in inD1. assert (HNames.In h hnamesᴳ( D1 ᴳ+ D2)).
    { apply HIn_union_iff. left. assumption. }
    specialize (IHTyC h H0). assumption.
  - left. assumption.
Qed.

Lemma hnames_singleton_dest : forall (h : hname) (m n : mode) (T : type), hnamesᴳ( ᴳ{- h : m ⌊ T ⌋ n} ) = ᴴ{ h }.
Proof.
  intros *.
  unfold hnames_ctx, hnames_dom, hnames_, ctx_singleton.
  rewrite dom_singleton_eq. reflexivity.
Qed.

Lemma hnames_singleton_hole : forall (h : hname) (T : type) (n : mode), hnamesᴳ( ᴳ{+ h : T ‗ n} ) = ᴴ{ h }.
Proof.
  intros *.
  unfold hnames_ctx, hnames_dom, hnames_, ctx_singleton.
  rewrite dom_singleton_eq. reflexivity.
Qed.

Lemma hnames_singleton_hunion_eq : forall (h1 h2 : hname), ᴴ{ h1 } ∪ ᴴ{ h2 } = ᴴ{ h1, h2 }.
Proof.
  intros. apply HNames.eq_leibniz. intros h. split.
  - intros InUnion. apply HNames.union_spec in InUnion. destruct InUnion as [InUnion | InUnion].
    + apply HNames.singleton_spec in InUnion. subst. apply HNames.add_spec. left. reflexivity.
    + apply HNames.singleton_spec in InUnion. subst. apply HNames.add_spec. right. apply HNames.add_spec. left. reflexivity.
  - intros InUnion. apply HNames.add_spec in InUnion. destruct InUnion as [InUnion | InUnion].
    + subst. apply HNames.union_spec. left. apply HNames.singleton_spec. reflexivity.
    + apply HNames.add_spec in InUnion. destruct InUnion as [InUnion | InUnion].
      * subst. apply HNames.union_spec. right. apply HNames.singleton_spec. reflexivity.
      * apply HNames.empty_spec in InUnion. contradiction.
Qed.

Lemma hnames_ectxs_fill : forall (C : ectxs) (h : hname) (H : hnames) (v : val) (D : ctx) (T U0 : type), D ⊣ C : T ↣ U0 -> HNames.In h hnames©( C) -> hnames©( C ©️[ h ≔ H ‗ v]) = (HNames.remove h (hnames©( C))) ∪ H.
Proof.
  dependent induction C.
  - intros * TyC contra. simpl in contra. generalize (HNames.empty_spec). intros empty_spec; specialize (empty_spec h); congruence.
  - intros * TyC Hin. dependent destruction a; inversion TyC; subst; simpl in *;
    try rewrite <- hunion_hempty_l_eq in *;
    try rewrite <- hunion_hempty_l_eq in *;
    try solve [apply (IHC _ _ _ _ _ _ TyC0); assumption].
    try solve [apply IHC; assumption].
    apply HNames.union_spec in Hin. destruct Hin as [Hin | Hin].
    + apply HNames.mem_spec in Hin; rewrite Hin in *. simpl in *.
      apply HNames.mem_spec in Hin.
      apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros h'. rewrite! HNames.union_spec. rewrite! HNames.remove_spec. rewrite! HNames.union_spec. split.
      * intros Hyp. destruct Hyp as [ [(InhpD3 & hpneqh) | InhpH0] | InhpC ].
          { left. split. left. assumption. assumption. }
          { right. assumption. }
          { left. split. right. assumption. intros contra; subst. contradiction (H7 h). apply HNames.inter_spec. split; assumption. }
      * intros Hyp. destruct Hyp as [ ( [InhpD3 | InhpC] & hpneqh) | InhpH0 ].
          { left. left. split; assumption. }
          { right. assumption. }
          { left. right. assumption. }
    + assert (~HNames.In h ( hnamesᴳ( D3))). { specialize (H7 h). intros InhD3. contradiction H7. apply HNames.inter_spec; split; assumption. }
      rewrite <- HNames.mem_spec in H. destruct (HNames.mem h hnamesᴳ( D3)); try congruence; simpl in *.
      rewrite (IHC _ _ _ _ _ _ TyC0). 2:{ assumption. }
      apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros h'. rewrite! HNames.union_spec. rewrite! HNames.remove_spec. rewrite! HNames.union_spec. split.
      * intros Hyp. destruct Hyp as [InhpD3 | [ (InhpC & hpneqh) | InhpH0]].
          { left. split. left. assumption. intros contra; subst. contradiction (H7 h). apply HNames.inter_spec. split; assumption. }
          { left. split. right. assumption. assumption. }
          { right. assumption. }
      * intros Hyp. destruct Hyp as [([InhpD3 | InhpC] & hpneqh) | InhpH0].
          { left. assumption. }
          { right. left. split; assumption. }
          { right. right. assumption. }
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Properties of shift and cshift *)
(*----------------------------------------------------------------------------*)
Lemma shift_by_max_impl_HDisjoint : forall (H H' : hnames) (h' : hname), maxᴴ(H) < h' -> H ## (H' ᴴ⩲ h').
Proof.
  intros * hH h hh. rewrite HNames.inter_spec in hh. destruct hh as [hhH hhH'].
  rewrite shift_spec in hhH'. destruct hhH' as [h'' [hh''H' hh''h']].
  assert (maxᴴ( H) < h).
  { lia. }
  sfirstorder use: gt_max_not_in.
Qed.

Lemma cshift_total_eq : forall (G : ctx) (h' : hname), maxᴴ(hnamesᴳ( G )) < h' -> hnamesᴳ(G ᴳ[ hnamesᴳ( G ) ⩲ h' ]) = hnamesᴳ(G) ᴴ⩲ h'.
Proof.
  intros * hpGreater. apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros xh.
  rewrite in_hnames. rewrite shift_spec. rewrite in_cshift.
  split.
  - intros h_in.
    destruct (Finitely.In_dec (ʰ xh) G) as [h_in'|h_nin'].
    1:{ rewrite <- in_hnames in h_in'.
        apply shift_perm_spec1 with (h':=h') in h_in'.
        2:{ assumption. }
        rewrite h_in' in *. clear h_in'.
        hauto l: on use: gt_max_not_in, in_hnames. }
    assert ((exists h'' : HNames.elt, HNames.In h'' hnamesᴳ( G) /\ xh = h'' + h') \/ ~(exists h'' : HNames.elt, HNames.In h'' hnamesᴳ( G) /\ xh = h'' + h')) as [hh|hh].
    { assert (xh >= h' \/ ~( xh >= h')) as [l|r].
      { lia. }
      + assert (HNames.mem (xh - h') (hnamesᴳ( G))= true \/ ~(HNames.mem (xh - h') hnamesᴳ( G) = true)) as h_mem.
        { destruct (HNames.mem (xh - h') (hnamesᴳ( G))).
          all: sfirstorder. }
        rewrite !HNames.mem_spec in h_mem. destruct h_mem as [ll|rr].
        * left. exists (xh-h').
          split.
          - assumption.
          - lia.
        * right. intros [h'' [h_in' h_eq]].
          assert (h'' = xh - h') as ->.
          { lia. }
          sfirstorder.
      + right.
        intros [h'' [h_in' h_eq]].
        lia.
    }
    * assumption.
    * rewrite shift_perm_spec3 in h_in.
      + sfirstorder.
      + assumption.
      + hauto lq: on use: in_hnames.
      + sfirstorder.
  - intros [h'' [h_in ->]].
    rewrite shift_perm_spec2.
    * hauto lq: on use: in_hnames.
    * assumption.
    * assumption.
Qed.

Lemma cshift_by_Disjoint_eq : forall (D D': ctx) (h': hname), D # D' -> maxᴴ(hnamesᴳ( D )) < h' -> D ᴳ[ hnamesᴳ( D' ) ⩲ h' ] = D.
Proof.
  intros * disj h_max. unfold ctx_cshift.
  apply perm_support_fixes'.
  apply fixes_inverse_fixes.
  apply fixes_untouched. intros t ht.
  unfold shift_perm, shift_one in *. rewrite List.in_map_iff in ht. destruct ht as [xh [<- ht]]. cbn.
  split.
  - intros h. unfold Disjoint in disj. eapply disj.
    { rewrite <- dom_spec. exact h. }
    rewrite <- InA_eq_eq, HNames.elements_spec1, in_hnames in ht.
    trivial.
  - assert (maxᴴ( hnamesᴳ( D)) < (xh + h')) as h by lia.
    apply gt_max_not_in in h.
    rewrite in_hnames, <- dom_spec in h.
    trivial.
Qed.

Lemma cshift_distrib_on_union : forall (G1 G2 : ctx) (H : hnames) (h' : hname), (G1 ᴳ+ G2)ᴳ[ H⩲h' ] = G1 ᴳ[ H⩲h' ] ᴳ+ G2 ᴳ[ H⩲h' ].
Proof.
  intros *. unfold union.
  apply merge_with_cshift.
Qed.
(* TODO: add to canonalize? *)

Lemma cshift_distrib_on_stimes : forall (m : mode) (G : ctx) (H : hnames) (h' : hname), (m ᴳ· G)ᴳ[ H⩲h' ] = m ᴳ· (G ᴳ[ H⩲h' ]).
Proof.
  intros *. unfold stimes.
  apply map_cshift.
Qed.
(* TODO: add to canonalize? *)

Lemma cshift_distrib_on_hminus_inv : forall (G : ctx) (H : hnames) (h' : hname), (ᴳ-⁻¹ G) ᴳ[ H ⩲ h' ] = (ᴳ-⁻¹ (G ᴳ[ H ⩲ h' ])).
Proof.
  intros *. unfold hminus_inv.
  apply map_cshift.
Qed.

Lemma cshift_distrib_on_hminus : forall (G : ctx) (H : hnames) (h' : hname), (ᴳ- G) ᴳ[ H ⩲ h' ] = (ᴳ- (G ᴳ[ H ⩲ h' ])).
Proof.
  intros *. unfold hminus.
  apply map_cshift.
Qed.

Lemma cshift_distrib_on_hnames : forall H h' D, hnames_cshift hnamesᴳ( D) H h' = hnamesᴳ( D ᴳ[ H ⩲ h']).
Proof.
  intros *. apply HNames.eq_leibniz. unfold HNames.eq, HNames.Equal. intros xh.
  unfold hnames_cshift. rewrite HNames.fold_spec, <- fold_left_rev_right.
  rewrite in_hnames, in_cshift. rewrite <- dom_spec, in_hnames_dom, in_rev.
  (*  Writing an assert because for some reason `induction (rev (HNames.elements hnamesᴳ( D))) as [|h D_elts].` only destructed the first occurrence *)

  assert (forall D_elts,
             HNames.In xh (fold_right (fun (y : HNames.elt) (x : HNames.t) => HNames.add (y ʰ[ H ⩲ h']) x) HNames.empty D_elts)
             <-> List.In (Permutation.sem (rev (shift_perm H h')) xh) D_elts).
  2:{ sfirstorder. }
  induction D_elts as [|h D_elts ih].
  - compute. sauto lq: on.
  - cbn. rewrite HNames.add_spec.
    hauto l: on use: Permutation.pre_inverse, Permutation.post_inverse.
Qed.

(* Could really be generalised to any var-only context. *)
Lemma cshift_singleton_var_eq : forall H h' x m T, ᴳ{ x : m ‗ T}ᴳ[ H ⩲ h'] = ᴳ{ x : m ‗ T}.
Proof.
  intros *. unfold ctx_singleton. unfold ctx_cshift, ctx_shift.
  apply ext_eq. intros n.
  destruct (name_eq_dec n (ˣ x)); subst.
  * rewrite singleton_MapsTo_at_elt. apply map_MapsTo_iff. exists (ₓ m ‗ T). split. cbn. unfold Fun.singleton. destruct (name_eq_dec (ˣ x) (ˣ x)) as [e|e]. dependent destruction e. reflexivity. congruence. cbn. reflexivity.
  * assert (@singleton name binding_type_of (ˣ x) name_eq_dec (ₓ m ‗ T) n = ☠). { rewrite singleton_nMapsTo_iff. symmetry. assumption. } rewrite H0.
  apply map_nMapsTo_iff. cbn. rewrite <- singleton_spec. apply singleton_nMapsTo_iff. destruct n.
  { cbn. symmetry. assumption. } { cbn. congruence. }
Qed.

Lemma cshift_singleton_hname : forall H h' h b, (ctx_singleton (name_DH h) b) ᴳ[ H ⩲ h'] = ctx_singleton (name_DH (h ʰ[ H ⩲ h'])) b.
Proof.
  intros *. apply Finitely.ext_eq. intros [xx|xh]. all: cbn.
  { reflexivity. }
  unfold Fun.map. unfold Fun.singleton, hname_cshift, pre_shift.
  destruct (Nat.eq_dec (Permutation.sem (shift_perm H h') h) xh) as [<-|ne].
  - rewrite Permutation.post_inverse.
    destruct (name_eq_dec (ʰ h) (ʰ h)) as [e1|ne1].
    * hauto l: on dep: on.
    * sfirstorder.
  - destruct (name_eq_dec (ʰ h) (ʰ Permutation.sem (rev (shift_perm H h')) xh)) as [e1|ne1].
    { hauto lq: on use: Permutation.eqn_inverse. }
    destruct (name_eq_dec (ʰ Permutation.sem (shift_perm H h') h) (ʰ xh)) as [e2|ne2].
    { hauto lq: on use: Permutation.eqn_inverse. }
    reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Other lemmas on HDisjoint that have a dependency on other lemmas so they can't be defined in the same group *)
Lemma Disjoint_to_HDisjoint : forall (D D' : ctx), D # D' -> hnamesᴳ(D) ## hnamesᴳ(D').
Proof.
  intros * DisjointDDp.
  unfold HDisjoint. unfold HNames.Empty. intros h HinInter.
  rewrite HNamesFacts.inter_iff in HinInter. destruct HinInter as (inD & inD').
  rewrite hnames_spec in inD, inD'. rewrite <- In_iff_exists_Some in inD, inD'.
  unfold Disjoint in DisjointDDp. specialize (DisjointDDp (name_DH h) inD inD'). assumption.
Qed.

Lemma HDisjoint_to_Disjoint : forall (D D' : ctx), DestOnly D -> hnamesᴳ(D) ## hnamesᴳ(D') -> D # D'.
Proof.
  intros * DestOnlyD hnamesDisjoint.
  unfold Disjoint. intros n inD inD'. unfold In, Fun.In in *. destruct n.
  - unfold DestOnly, IsDest in DestOnlyD. destruct inD as (binding & inD); specialize (DestOnlyD (name_Var x) binding inD); cbn in DestOnlyD. assumption.
  - rewrite <- hnames_spec in inD, inD'. unfold HDisjoint in hnamesDisjoint.
    assert (HNames.In h (HNames.inter hnamesᴳ(D) hnamesᴳ(D'))).
      { apply HNames.inter_spec. split; assumption. }
    unfold HNames.Empty in hnamesDisjoint. specialize (hnamesDisjoint h). congruence.
Qed.

Lemma HDisjoint_gt_max : forall (h h1 h2 : hname) (H : HNames.t), (0 < h1) -> H ## ᴴ{ maxᴴ( H ∪ ᴴ{ h}) + h1 + h2}.
Proof.
  intros *.
  intros h1notnull.
  unfold HDisjoint. intros h' contra. rewrite HNames.inter_spec in contra. destruct contra as (contra & contra'). unfold hnames_ in contra'. rewrite HNames.add_spec in contra'. destruct contra' as [contra' | contra'].
  * rewrite contra' in *. apply different_than_gt_max with (h1 := h1) (h2 := h2) (H := ᴴ{ h}) in contra. rewrite 1 hunion_commutative in contra. simpl in contra. contradiction contra. reflexivity. assumption.
  * apply HNames.empty_spec in contra'. contradiction.
Qed.

Lemma HDisjoint_hunion_iff : forall (H H' H'' : HNames.t), (H ## H' /\ H ## H'') <-> H ## H' ∪ H''.
Proof.
  intros. split.
  - intros (disj1 & disj2) h contra. rewrite HNames.inter_spec in contra. destruct contra as (contra & contra'). apply HNames.union_spec in contra'. destruct contra' as [contra' | contra'].
    + contradiction disj1 with (a := h). apply HNames.inter_spec. tauto.
    + contradiction disj2 with (a := h). apply HNames.inter_spec. tauto.
  - intros disj. split; intros h contra; contradiction disj with (a := h); apply HNames.inter_spec; apply HNames.inter_spec in contra; destruct contra as (contra & contra'); split; trivial.
    * apply HNames.union_spec. left. assumption.
    * apply HNames.union_spec. right. assumption.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* Here we define automatic reasoning tactics to ease proofs of more complex lemmas *)

(* hauto_ctx is the basis for tactics crush and supercrush, which try the most used lemmas to solve simple goals on contexts *)
Ltac hauto_ctx :=
  hauto
    depth: 3
    use:
        mode_plus_associative,
        mode_plus_commutative,
        mode_times_associative,
        mode_times_commutative,
        mode_times_distrib_on_plus,
        mode_times_linnu_l_eq,
        mode_times_linnu_r_eq,
        IsValid_linnu',
        IsValid_linup',
        IsValid_plus_backward,
        IsValid_times_backward,
        IsValid_times_iff,
        IsFinAge_linnu',
        IsFinAge_linup',
        IsFinAge_plus_backward,
        IsFinAge_times_iff,
        IsLin_linnu',
        IsLin_linup',
        IsLin_plus_backward,
        IsLin_times_iff,
        IsLin_wk_IsValid,
        nIsLin_mode_plus,
        IsLinNu_mode_plus,
        IsLinNu_wk_IsFinAge,
        IsLinNu_wk_IsLin,
        ModeSubtype_linnu_eq,
        ModeSubtype_refl,

        union_associative,
        union_commutative,
        union_empty_iff,
        union_empty_l_eq,
        union_empty_r_eq,

        stimes_distrib_on_union,
        stimes_empty_eq,
        stimes_empty_iff,
        stimes_is_action,
        stimes_linnu_eq,
        stimes_mode_plus_eq,
        stimes_singleton_dest,
        stimes_singleton_hole,
        stimes_singleton_var,

        hminus_distrib_on_union,
        hminus_empty_eq,
        hminus_singleton,

        hminus_inv_distrib_on_union,
        hminus_inv_empty_eq,
        hminus_inv_singleton,

        Disjoint_commutative,
        Disjoint_empty_l,
        Disjoint_empty_r,
        Disjoint_hminus_inv_l_iff,
        Disjoint_hminus_inv_r_iff,
        Disjoint_hminus_l_iff,
        Disjoint_hminus_r_iff,
        Disjoint_singleton_dest_iff_same_name,
        Disjoint_singleton_hole_iff_same_name,
        Disjoint_singleton_var_iff_same_name,
        Disjoint_singletons_iff,
        Disjoint_stimes_l_iff,
        Disjoint_stimes_r_iff,
        Disjoint_union_l_iff,
        Disjoint_union_r_iff,

        ValidOnly_cshift_iff,
        ValidOnly_singleton_iff,
        ValidOnly_stimes_backward,
        ValidOnly_stimes_forward,
        ValidOnly_union_backward,
        ValidOnly_union_forward,

        LinOnly_cshift_iff,
        LinOnly_empty,
        LinOnly_singleton_iff,
        LinOnly_stimes_backward,
        LinOnly_stimes_forward,
        LinOnly_stimes_plus_backward,
        LinOnly_stimes_times_backward,
        LinOnly_union_iff,
        LinOnly_wk_ValidOnly,

        LinNuOnly_cshift_iff,
        LinNuOnly_stimes_backward,
        LinNuOnly_stimes_forward,
        LinNuOnly_union_iff,
        LinNuOnly_wk_FinAgeOnly,
        LinNuOnly_wk_LinOnly,

        FinAgeOnly_cshift_iff,
        FinAgeOnly_empty,
        FinAgeOnly_singleton_iff,
        FinAgeOnly_stimes_backward,
        FinAgeOnly_stimes_forward,
        FinAgeOnly_stimes_plus_backward,
        FinAgeOnly_stimes_times_backward,
        FinAgeOnly_union_backward,
        FinAgeOnly_union_forward,

        DestOnly_Disjoint_singleton_var,
        DestOnly_cshift_iff,
        DestOnly_empty,
        DestOnly_singleton_dest,
        DestOnly_stimes_iff,
        DestOnly_union_iff,

        VarOnly_singleton_var,
        VarOnly_stimes_iff,
        VarOnly_union_iff,

        DisposableOnly_cshift_iff,
        DisposableOnly_empty,

        Disjoint_to_HDisjoint,
        HDisjoint_to_Disjoint,
        hnames_empty_is_hempty,
        hnames_hminus_eq,
        hnames_hminus_inv_eq,
        hnames_singleton_dest,
        hnames_singleton_hole,
        
        hunion_hempty_l_eq,
        hunion_hempty_r_eq,

        HDisjoint_hempty_l,
        HDisjoint_hempty_r.

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
  let finisher := solve [ hauto
                        | (rewrite_strat
                            (topdown (choice (hints suffices) (hints propagate_down)))); hauto use: Disjoint_commutative ] in
  let workhorse :=
    solve
      [ trivial with autolemmas
      (* Saturate is slowish. So it's worth trying without it first. *)
      | autorewrite with propagate_down in *; finisher
      (* Saturate a second time because it isn't unlikely to uncover
         something new after simplification. *)
      | saturate'; solve [ finisher | saturate'; finisher ]
      (* ⬇️ should really be the last case because it can be quite slow. *)
      | timeout 60 hauto_ctx ]
  in
  solve
    [ trivial
    | autorewrite with canonalize in *; workhorse ].

Ltac supercrush :=
  autorewrite with propagate_down in * ; crush.

Ltac Disjoint_singleton_using' DisjointHyp :=
 match type of DisjointHyp with
  | _ /\ _ => let DisjointHyp2 := fresh DisjointHyp "" in
    destruct DisjointHyp as (DisjointHyp & DisjointHyp2); apply nIn_iff_Disjoint_singleton; apply nIn_iff_Disjoint_singleton in DisjointHyp; apply nIn_iff_Disjoint_singleton in DisjointHyp2; assumption
  | _ => apply nIn_iff_Disjoint_singleton; apply nIn_iff_Disjoint_singleton in DisjointHyp; assumption
 end.

Ltac Disjoint_singleton_using DisjointHyp :=
  autorewrite with propagate_down in *; Disjoint_singleton_using' DisjointHyp.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* These lemmas are about inverting an operation on one side of a context equality (stimes, union) *)
(*----------------------------------------------------------------------------*)
Lemma stimes_inv_singleton_hole : forall (m : mode) (G : ctx) (h : hname) (T : type) (n : mode), m ᴳ· G = ᴳ{+ h : T ‗ n} -> exists m', n = m · m' /\ G = ᴳ{+ h : T ‗ m'}.
Proof.
  intros *. intros Geq.
  destruct (G (ʰ h)) eqn:Gmapstoh.
  exists (mode_of b). split.
  - assert ((m ᴳ· G) (ʰ h) = Some (₊ T ‗ n)). { rewrite Geq. unfold ctx_singleton. rewrite singleton_MapsTo_at_elt. reflexivity. }
    unfold stimes in H. rewrite map_MapsTo_iff in H. destruct H as (b' & mapsto' & H). assert (b = b'). { rewrite mapsto' in Gmapstoh. inversion Gmapstoh. reflexivity. } subst. destruct b'; simpl in H; inversion H; simpl; reflexivity.
  - apply ext_eq. intros n'.
    assert ((m ᴳ· G) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. }
    destruct (name_eq_dec (ʰ h) n').
    * subst. 
      unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *.
      unfold stimes in H; unfold map, Fun.map in H; simpl in H. rewrite Gmapstoh in H; simpl in H. destruct b; simpl in *. congruence. rewrite Gmapstoh. inversion H; reflexivity.
    * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. apply map_nMapsTo_iff in H.
      assert (ᴳ{+ h : T ‗ mode_of b} n' = None). { apply singleton_nMapsTo_iff. assumption. }
      rewrite H. rewrite H1. reflexivity.
  - assert (In (ʰ h) (m ᴳ· G)). { rewrite Geq. apply In_singleton_iff; reflexivity. } rewrite In_stimes_iff in H. destruct H as (b' & mapsto). congruence.
Qed.

Lemma stimes_inv_singleton_dest : forall (m : mode) (G : ctx) (h : hname) (m0 : mode) (T : type) (n : mode), m ᴳ· G = ᴳ{- h : m0 ⌊ T ⌋ n} -> exists m1, m0 = m · m1 /\ G = ᴳ{- h : m1 ⌊ T ⌋ n}.
Proof.
  intros *. intros Geq.
  destruct (G (ʰ h)) eqn:Gmapstoh.
  exists (mode_of b). split.
  - assert ((m ᴳ· G) (ʰ h) = Some (₋ m0 ⌊ T ⌋ n)). { rewrite Geq. unfold ctx_singleton. rewrite singleton_MapsTo_at_elt. reflexivity. }
    unfold stimes in H. rewrite map_MapsTo_iff in H. destruct H as (b' & mapsto' & H). assert (b = b'). { rewrite mapsto' in Gmapstoh. inversion Gmapstoh. reflexivity. } subst. destruct b'; simpl in H; inversion H; simpl; reflexivity.
  - apply ext_eq. intros n'.
    assert ((m ᴳ· G) n' = ᴳ{- h : m0 ⌊ T ⌋ n} n'). { rewrite Geq. reflexivity. }
    destruct (name_eq_dec (ʰ h) n').
    * subst. 
      unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *.
      unfold stimes in H; unfold map, Fun.map in H; simpl in H. rewrite Gmapstoh in H; simpl in H. destruct b; simpl in *. congruence. rewrite Gmapstoh. inversion H; reflexivity.
    * assert (ᴳ{- h : m0 ⌊ T ⌋ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. apply map_nMapsTo_iff in H.
      assert (ᴳ{- h : mode_of b ⌊ T ⌋ n} n' = None). { apply singleton_nMapsTo_iff. assumption. }
      rewrite H. rewrite H1. reflexivity.
  - assert (In (ʰ h) (m ᴳ· G)). { rewrite Geq. apply In_singleton_iff; reflexivity. } rewrite In_stimes_iff in H. destruct H as (b' & mapsto). congruence.
Qed.

Lemma stimes_inv_singleton_var : forall (m : mode) (G : ctx) (x : var) (m0 : mode) (T : type) , m ᴳ· G = ᴳ{ x : m0 ‗ T} -> exists m', m0 = m · m' /\ G = ᴳ{ x : m' ‗ T}.
Proof.
  intros *. intros Geq.
  destruct (G (ˣ x)) eqn:Gmapstox.
  exists (mode_of b). split.
  - assert ((m ᴳ· G) (ˣ x) = Some (ₓ m0 ‗ T)). { rewrite Geq. unfold ctx_singleton. rewrite singleton_MapsTo_at_elt. reflexivity. }
    unfold stimes in H. rewrite map_MapsTo_iff in H. destruct H as (b' & mapsto' & H). assert (b = b'). { rewrite mapsto' in Gmapstox. inversion Gmapstox. reflexivity. } subst. destruct b'; simpl in H; inversion H; simpl; reflexivity.
  - apply ext_eq. intros n'.
    assert ((m ᴳ· G) n' = ᴳ{ x : m0 ‗ T} n'). { rewrite Geq. reflexivity. }
    destruct (name_eq_dec (ˣ x) n').
    * subst. 
      unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *.
      unfold stimes in H; unfold map, Fun.map in H; simpl in H. rewrite Gmapstox in H; simpl in H. destruct b; simpl in *. congruence.
    * assert (ᴳ{ x : m0 ‗ T} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. apply map_nMapsTo_iff in H.
      assert (ᴳ{ x : mode_of b ‗ T} n' = None). { apply singleton_nMapsTo_iff. assumption. }
      rewrite H. rewrite H1. reflexivity.
  - assert (In (ˣ x) (m ᴳ· G)). { rewrite Geq. apply In_singleton_iff; reflexivity. } rewrite In_stimes_iff in H. destruct H as (b' & mapsto). congruence.
Qed.

Lemma stimes_inv_hminus_inv : forall (m : mode) (G G1 : ctx), ValidOnly (ᴳ-⁻¹ G1) -> m ᴳ· G = ᴳ-⁻¹ G1 -> G = ᴳ-⁻¹ (ᴳ- G).
Proof.
  intros * ValidOnlyG1 Geq.
  assert (ValidOnly G). { rewrite <- Geq in ValidOnlyG1. apply ValidOnly_stimes_backward in ValidOnlyG1. assumption. }
  assert (HoleOnly G). { apply HoleOnly_hminus_inv in ValidOnlyG1. rewrite <- Geq in ValidOnlyG1. rewrite <- HoleOnly_stimes_iff in ValidOnlyG1. assumption. }
  symmetry. apply hminus_inv_hminus_eq. apply ValidOnly_hminus; assumption.
Qed.

Lemma stimes_linone_equal_iff : forall (G1 G2 : ctx), ¹↑ ᴳ· G1 = ¹↑ ᴳ· G2 <-> G1 = G2.
Proof.
  intros *.
  split.
  - intros Geq. apply ext_eq. intros n.
    destruct (G1 n) eqn:G1mapsto, (G2 n) eqn:G2mapsto.
    assert ((¹↑ ᴳ· G1) n = (¹↑ ᴳ· G2) n). { rewrite Geq; reflexivity. }
    unfold stimes in H. simpl in H. unfold Fun.map in H. rewrite G1mapsto, G2mapsto in H. inversion H. destruct n, b, b0; simpl in H1; try destruct m; try destruct m0; try destruct n; try destruct n0; try destruct p; try destruct p0; try destruct m; try destruct m0; try destruct a; try destruct a0; inversion H1; trivial.
    assert (In n G2). { rewrite <- In_stimes_iff with (m := ¹↑). rewrite <- Geq. rewrite In_stimes_iff. exists b; assumption. } destruct H; congruence.
    assert (In n G1). { rewrite <- In_stimes_iff with (m := ¹↑). rewrite Geq. rewrite In_stimes_iff. exists b; assumption. } destruct H; congruence.
    reflexivity.
  - intros Geq. rewrite Geq. reflexivity.
Qed.

Lemma union_inv_singleton_hole : forall (G1 G2 : ctx) (h : hname) (T : type) (n : mode), IsValid n -> G1 ᴳ+ G2 = ᴳ{+ h : T ‗ n} -> {exists n1 n2, G1 = ᴳ{+ h : T ‗ n1} /\ G2 = ᴳ{+ h : T ‗ n2} /\ n = mode_plus n1 n2} + {G1 = ᴳ{+ h : T ‗ n} /\ G2 = ᴳ{}} + {G1 = ᴳ{} /\ G2 = ᴳ{+ h : T ‗ n}}.
Proof.
  intros * IsValidn Geq.
  destruct (G1 (ʰ h)) eqn:G1mapstoh, (G2 (ʰ h)) eqn:G2mapstoh.
  - left. left. exists (mode_of b), (mode_of b0). repeat split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_Some_eq with (y1 := b) (y2 := b0) in H. 2:{ split; assumption. } destruct b, b0; simpl in *; try destruct (type_eq_dec T0 T1); try destruct (mode_eq_dec n0 n1); simpl in *; inversion H; subst; try congruence; try inversion IsValidn; trivial.
      * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
        assert (ᴳ{+ h : T ‗ mode_of b} n' = None). { unfold ctx_singleton. rewrite singleton_nMapsTo_iff. assumption. }
      rewrite H1, H2; reflexivity.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_Some_eq with (y1 := b) (y2 := b0) in H. 2:{ split; assumption. } destruct b, b0; simpl in *; try destruct (type_eq_dec T0 T1); try destruct (mode_eq_dec n0 n1); simpl in *; inversion H; subst; try congruence; try inversion IsValidn; trivial.
      * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
        assert (ᴳ{+ h : T ‗ mode_of b0} n' = None). { unfold ctx_singleton. rewrite singleton_nMapsTo_iff. assumption. }
      rewrite H1, H2; reflexivity.
    + assert ((G1 ᴳ+ G2) (ʰ h) = ᴳ{+ h : T ‗ n} (ʰ h)). { rewrite Geq. reflexivity. }
      unfold union, merge_with, merge, Fun.merge, Fun.on_conflict_do, ctx_singleton in H. rewrite singleton_MapsTo_at_elt in H; simpl in H; rewrite G1mapstoh, G2mapstoh in H; unfold union_dh in H.
      destruct b, b0; simpl in *; try destruct (type_eq_dec T0 T1); try destruct (mode_eq_dec n0 n1); simpl in *; inversion H; subst;  try congruence; try inversion IsValidn; trivial.
  - left. right. split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_None_eq with (y1 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion IsValidn; trivial.
      * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      rewrite H0, H1; reflexivity.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. simpl. assumption.
      * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. } simpl. assumption.
  - right. split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_None_Some_eq with (y2 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion IsValidn; trivial.
      * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. } simpl. assumption.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{+ h : T ‗ n} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_None_Some_eq with (y2 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion IsValidn; trivial.
      * assert (ᴳ{+ h : T ‗ n} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      rewrite H0, H1; reflexivity.
  - exfalso. assert (In (ʰ h) (G1 ᴳ+ G2)). { rewrite Geq. apply In_singleton_iff; reflexivity. } rewrite In_union_iff in H. destruct H as [H | H].
    + unfold In, Fun.In in H. destruct H. congruence.
    + unfold In, Fun.In in H. destruct H. congruence.
Qed.

Lemma union_inv_singleton_var : forall (G1 G2 : ctx) (x : var) (m : mode) (T : type), IsValid m -> G1 ᴳ+ G2 = ᴳ{ x : m ‗ T } -> {exists m1 m2, G1 = ᴳ{ x : m1 ‗ T } /\ G2 = ᴳ{ x : m2 ‗ T } /\ m = mode_plus m1 m2} + {G1 = ᴳ{ x : m ‗ T } /\ G2 = ᴳ{}} + {G1 = ᴳ{} /\ G2 = ᴳ{ x : m ‗ T }}.
Proof.
  intros * Validm Geq.
  destruct (G1 (ˣ x)) eqn:G1mapstox, (G2 (ˣ x)) eqn:G2mapstox.
  - left. left. exists (mode_of b), (mode_of b0). repeat split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{ x : m ‗ T } n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ˣ x) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_Some_eq with (y1 := b) (y2 := b0) in H. 2:{ split; assumption. } destruct b, b0; simpl in *; inversion H; try destruct (type_eq_dec T0 T1); subst; try congruence; trivial. inversion H; subst; inversion Validm.
      * assert (ᴳ{ x : m ‗ T } n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
        assert (ᴳ{ x : mode_of b ‗ T } n' = None). { unfold ctx_singleton. rewrite singleton_nMapsTo_iff. assumption. }
      rewrite H1, H2; reflexivity.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{ x : m ‗ T } n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ˣ x) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_Some_eq with (y1 := b) (y2 := b0) in H. 2:{ split; assumption. } destruct b, b0; simpl in *; inversion H; try destruct (type_eq_dec T0 T1); subst; try congruence; trivial. inversion H; subst; inversion Validm.
      * assert (ᴳ{ x : m ‗ T } n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
        assert (ᴳ{ x : mode_of b0 ‗ T } n' = None). { unfold ctx_singleton. rewrite singleton_nMapsTo_iff. assumption. }
      rewrite H1, H2; reflexivity.
    + assert ((G1 ᴳ+ G2) (ˣ x) = ᴳ{ x : m ‗ T } (ˣ x)). { rewrite Geq. reflexivity. }
      unfold union, merge_with, merge, Fun.merge, Fun.on_conflict_do, ctx_singleton in H. rewrite singleton_MapsTo_at_elt in H; simpl in H; rewrite G1mapstox, G2mapstox in H; unfold union_var in H.
      destruct b, b0; simpl in *; try destruct (type_eq_dec T0 T1); try destruct (mode_eq_dec n n0); simpl in *; inversion H; subst;  try congruence; try inversion Validm; trivial.
  - left. right. split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{ x : m ‗ T } n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ˣ x) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_None_eq with (y1 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion Validm; trivial.
      * assert (ᴳ{ x : m ‗ T } n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      rewrite H0, H1; reflexivity.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{ x : m ‗ T } n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ˣ x) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_None_eq with (y1 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion Validm; trivial.
      * assert (ᴳ{ x : m ‗ T } n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      simpl. assumption.
  - right. split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{ x : m ‗ T } n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ˣ x) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_None_Some_eq with (y2 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion Validm; trivial.
      * assert (ᴳ{ x : m ‗ T } n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      simpl. assumption.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{ x : m ‗ T } n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ˣ x) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_None_Some_eq with (y2 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion Validm; trivial.
      * assert (ᴳ{ x : m ‗ T } n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      rewrite H0, H1; reflexivity.
  - exfalso. assert (In (ˣ x) (G1 ᴳ+ G2)). { rewrite Geq. apply In_singleton_iff; reflexivity. } rewrite In_union_iff in H. destruct H as [H | H].
    + unfold In, Fun.In in H. destruct H. congruence.
    + unfold In, Fun.In in H. destruct H. congruence.
Qed.

Lemma union_inv_singleton_dest_IsLin : forall (G1 G2 : ctx) (h : hname) (T : type) (m0 m1 : mode), IsLin m0 -> G1 ᴳ+ G2 = ᴳ{- h : m0 ⌊ T ⌋ m1} -> {G1 = ᴳ{- h : m0 ⌊ T ⌋ m1} /\ G2 = ᴳ{}} + {G1 = ᴳ{} /\ G2 = ᴳ{- h : m0 ⌊ T ⌋ m1}}.
Proof.
  intros * IsLinm0 Geq.
  destruct (G1 (ʰ h)) eqn:G1mapstoh, (G2 (ʰ h)) eqn:G2mapstoh.
  - exfalso.
    assert ((G1 ᴳ+ G2) (ʰ h) = ᴳ{- h : m0 ⌊ T ⌋ m1} (ʰ h)). { rewrite Geq. reflexivity. }
    unfold union, merge_with, merge, Fun.merge, Fun.on_conflict_do, ctx_singleton in H. rewrite singleton_MapsTo_at_elt in H; simpl in H; rewrite G1mapstoh, G2mapstoh in H; unfold union_dh in H;
    destruct b, b0; simpl in *; try destruct (type_eq_dec T0 T1); try destruct (mode_eq_dec n n0); inversion H; rewrite <- H1 in *; try inversion IsLinm0.
    apply (nIsLin_mode_plus m m2 IsLinm0).
  - left. split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{- h : m0 ⌊ T ⌋ m1} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_Some_None_eq with (y1 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion IsLinm0; trivial.
      * assert (ᴳ{- h : m0 ⌊ T ⌋ m1} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      rewrite H0, H1; reflexivity.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{- h : m0 ⌊ T ⌋ m1} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. simpl. assumption.
      * assert (ᴳ{- h : m0 ⌊ T ⌋ m1} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. } simpl. assumption.
  - right. split.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{- h : m0 ⌊ T ⌋ m1} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_None_Some_eq with (y2 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion IsLinm0; trivial.
      * assert (ᴳ{- h : m0 ⌊ T ⌋ m1} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G1 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      simpl. assumption.
    + apply ext_eq. intros n'. assert ((G1 ᴳ+ G2) n' = ᴳ{- h : m0 ⌊ T ⌋ m1} n'). { rewrite Geq. reflexivity. } destruct (name_eq_dec (ʰ h) n').
      * subst. unfold ctx_singleton in *. rewrite singleton_MapsTo_at_elt in *. unfold union in H. rewrite merge_with_None_Some_eq with (y2 := b) in H. 2:{ split; assumption. } destruct b; simpl in *; inversion H; subst; try congruence; try inversion IsLinm0; trivial.
      * assert (ᴳ{- h : m0 ⌊ T ⌋ m1} n' = None). { apply singleton_nMapsTo_iff. assumption. } rewrite H0 in H. assert (G2 n' = None). { apply nIn_iff_nMapsTo. intros contra. apply nIn_iff_nMapsTo in H. apply nIn_union_iff in H. destruct H as (nInG1 & nInG2). congruence. }
      rewrite H0, H1; reflexivity.
  - exfalso. assert (In (ʰ h) (G1 ᴳ+ G2)). { rewrite Geq. apply In_singleton_iff; reflexivity. } rewrite In_union_iff in H. destruct H as [H | H].
    + unfold In, Fun.In in H. destruct H. congruence.
    + unfold In, Fun.In in H. destruct H. congruence.
Qed.

Lemma union_inv_hminus_inv : forall (G G1 G2 : ctx), ValidOnly (ᴳ-⁻¹ G) -> ᴳ-⁻¹ G = G1 ᴳ+ G2 -> G1 = ᴳ-⁻¹ (ᴳ- G1) /\ G2 = ᴳ-⁻¹ (ᴳ- G2).
Proof.
  intros * ValidOnlyhiG union_eq. repeat split.
  - assert (ValidOnly G1). { rewrite union_eq in ValidOnlyhiG. apply ValidOnly_union_backward in ValidOnlyhiG. sfirstorder. }
    assert (HoleOnly G1). { pose proof ValidOnlyhiG as ValidOnlyhiG'. apply HoleOnly_hminus_inv in ValidOnlyhiG. rewrite union_eq in ValidOnlyhiG, ValidOnlyhiG'. apply HoleOnly_union_backward in ValidOnlyhiG. all: sfirstorder. }
    symmetry. apply hminus_inv_hminus_eq. apply ValidOnly_hminus; assumption.
  - assert (ValidOnly G2). { rewrite union_eq in ValidOnlyhiG. apply ValidOnly_union_backward in ValidOnlyhiG. sfirstorder. }
    assert (HoleOnly G2). { pose proof ValidOnlyhiG as ValidOnlyhiG'. apply HoleOnly_hminus_inv in ValidOnlyhiG. rewrite union_eq in ValidOnlyhiG, ValidOnlyhiG'. apply HoleOnly_union_backward in ValidOnlyhiG. all:sfirstorder. }
    symmetry. apply hminus_inv_hminus_eq. apply ValidOnly_hminus; assumption.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* The following lemmas are all about splitting typing contexts in parts. They are used when we have an equality of typing contexts at hand (potentially with sums and scalar products on each side) *)
(*----------------------------------------------------------------------------*)
Definition DomSubset (G G' : ctx) : Prop :=
  forall (n : name), In n G -> In n G'.

Lemma DomSubset_union_l : forall (G1 G2 : ctx), DomSubset G1 (G1 ᴳ+ G2).
Proof.
  intros * n InG. apply In_union_iff. left; assumption.
Qed.

Lemma DomSubset_union_r : forall (G1 G2 : ctx), DomSubset G2 (G1 ᴳ+ G2).
Proof.
  intros * n InG. apply In_union_iff. right; assumption.
Qed.

#[program]
Definition restriction (G G1 : ctx) : ctx :=
  {|
    underlying := fun n => match G1 n with
                           | Some b => G n
                           | None => None
                           end
  |}.
Next Obligation.
  exists (dom G1). unfold Fun.Support. intros n b.
  destruct (G1 n) eqn:G1mapsto; intros H. 2:{ congruence. }
  assert (In n G1). { unfold In. exists b0; assumption. }
  apply dom_spec; assumption.
Qed.

Lemma restriction_distrib_on_union : forall (G G' G1 : ctx), restriction (G ᴳ+ G') G1 = restriction G G1 ᴳ+ restriction G' G1.
Proof.
  intros. apply ext_eq. intros n. unfold restriction; simpl. destruct (G1 n) eqn:G1mapsto, (G n) eqn:Gmapsto, (G' n) eqn:Gpmapsto; destruct n; try destruct b; unfold Fun.merge, Fun.on_conflict_do; try rewrite G1mapsto; try rewrite Gmapsto; try rewrite Gpmapsto; simpl; trivial.
Qed.

Lemma restriction_distrib_on_stimes : forall (m : mode) (G G1 : ctx), restriction (m ᴳ· G) G1 = m ᴳ· restriction G G1.
Proof.
  intros. apply ext_eq. intros n. unfold restriction; simpl. destruct (G1 n) eqn:G1mapsto, (G n) eqn:Gmapsto; destruct n; try destruct b; unfold Fun.map; try rewrite G1mapsto; try rewrite Gmapsto; simpl; trivial.
Qed.

Lemma restriction_disjoint_empty : forall (G G1 : ctx), G # G1 -> restriction G G1 = ᴳ{}.
Proof.
  intros * DisjointG1G2. apply ext_eq. intros n. unfold restriction; simpl. destruct (G1 n) eqn:G1mapsto; trivial. rewrite Disjoint_commutative in DisjointG1G2. assert (In n G1). { unfold In. exists b; assumption. } specialize (DisjointG1G2 n H).
  apply nIn_iff_nMapsTo. assumption.
Qed.

Lemma restriction_self_eq : forall (G : ctx), restriction G G = G.
Proof.
  intros. apply ext_eq. intros n. unfold restriction; simpl. destruct (G n) eqn:Gmapsto; trivial.
Qed.

Lemma restriction_MapsTo_iff : forall (G G1 : ctx) (n : name) (b : binding_type_of n), (G n = Some b /\ exists b', G1 n = Some b') <-> restriction G G1 n = Some b.
Proof.
  intros *. split.
  - intros (Gmapsto & (b' & G1mapsto)). unfold restriction; simpl. rewrite G1mapsto. rewrite Gmapsto. reflexivity.
  - intros restrmapsto. unfold restriction in restrmapsto; simpl in restrmapsto. destruct (G1 n) eqn:G1mapsto. 2:{ inversion restrmapsto. }
    split. assumption. exists b0; reflexivity.
Qed.

Lemma restriction_nIn_iff_nMapsTo : forall (G G1 : ctx) (n : name), G n = None \/ G1 n = None <-> restriction G G1 n = None.
Proof.
  intros *. split.
  - intros [Gmapsto | G1mapsto]; unfold restriction; simpl. destruct (G1 n) eqn:G1mapsto; trivial. rewrite G1mapsto. reflexivity.
  - intros restrn. unfold restriction in restrn. destruct (G1 n) eqn:G1mapsto; simpl in restrn; rewrite G1mapsto in restrn; simpl in *. left; assumption. right; assumption.
Qed.

Lemma ctx_split_stimes_union : forall (m : mode) (G G1 G2 : ctx), G1 # G2 -> m ᴳ· G = G1 ᴳ+ G2 -> exists G1' G2', G1 = m ᴳ· G1' /\ G2 = m ᴳ· G2' /\ G = G1' ᴳ+ G2'.
Proof.
  intros * DisjointG1G2 CtxEq.
  exists (restriction G G1), (restriction G G2). repeat split.
  - assert (restriction (m ᴳ· G) G1 = restriction (G1 ᴳ+ G2) G1). { rewrite CtxEq. reflexivity. } rewrite restriction_distrib_on_stimes in H. rewrite restriction_distrib_on_union in H. rewrite restriction_disjoint_empty with (G := G2) in H. 2:{ apply Disjoint_commutative; assumption. } rewrite restriction_self_eq in H. rewrite <- union_empty_r_eq in H. symmetry; assumption.
  - assert (restriction (m ᴳ· G) G2 = restriction (G1 ᴳ+ G2) G2). { rewrite CtxEq. reflexivity. } rewrite restriction_distrib_on_stimes in H. rewrite restriction_distrib_on_union in H. rewrite restriction_disjoint_empty with (G := G1) in H. 2:{ assumption. } rewrite restriction_self_eq in H. rewrite <- union_empty_l_eq in H. symmetry; assumption.
  - apply ext_eq. intros n. destruct (G n) eqn:Gmapsto, (G1 n) eqn:G1mapsto; unfold union.
    * rewrite merge_with_Some_None_eq with (y1 := b); trivial. split.
      apply restriction_MapsTo_iff. split. assumption. exists b0; assumption.
      apply restriction_nIn_iff_nMapsTo. right. assert (In n G1). { unfold In. exists b0; assumption. } specialize (DisjointG1G2 n H). apply nIn_iff_nMapsTo. assumption.
    * assert (In n G2). { assert (In n G). { exists b; assumption. } rewrite <- In_stimes_iff with (m := m) in H. rewrite CtxEq in H. rewrite In_union_iff in H. destruct H. destruct H as (z & mapsto). congruence. assumption. }
      destruct H as (b0 & G2mapsto).
      rewrite merge_with_None_Some_eq with (y2 := b); trivial. split.
      apply restriction_nIn_iff_nMapsTo. right; assumption.
      apply restriction_MapsTo_iff. split. assumption. exists b0; assumption.
    * rewrite merge_with_None_None_eq. reflexivity. split; apply restriction_nIn_iff_nMapsTo; left; assumption.
    * rewrite merge_with_None_None_eq. reflexivity. split; apply restriction_nIn_iff_nMapsTo; left; assumption.
Qed.

Lemma ctx_split_into_restrictions : forall (G G1 G2 : ctx), G1 # G2 -> DomSubset G (G1 ᴳ+ G2) -> G = restriction G G1 ᴳ+ restriction G G2.
Proof.
  intros * DisjointG1G2 DomSubsetG. apply ext_eq. intros n.
  destruct (G n) eqn:Gmapsto. assert (In n G). { unfold In. exists b. assumption. } specialize (DomSubsetG n H). all: destruct ((restriction G G1 ᴳ+ restriction G G2) n) eqn:restrmapsto.
  all: unfold union in *; destruct (G1 n) eqn:G1mapsto; destruct (G2 n) eqn:G2mapsto; trivial; try contradiction (Disjoint_MapsTo_contra G1 G2 n b1 b2 DisjointG1G2 G1mapsto G2mapsto); try contradiction (Disjoint_MapsTo_contra G1 G2 n b0 b1 DisjointG1G2 G1mapsto G2mapsto); try contradiction (In_union_nMapsTo_contra G1 G2 n DomSubsetG G1mapsto G2mapsto).
  { assert ((restriction G G1) n = Some b). { apply restriction_MapsTo_iff; split. assumption. exists b1; assumption. }
    assert ((restriction G G2) n = None). { apply restriction_nIn_iff_nMapsTo. right. assumption. }
    assert (merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) (restriction G G1) (restriction G G2) n = Some b). { apply merge_with_Some_None_eq. split; assumption. }
    rewrite <- restrmapsto. rewrite H2. reflexivity. }
  { assert ((restriction G G1) n = None). { apply restriction_nIn_iff_nMapsTo. right. assumption. }
    assert ((restriction G G2) n = Some b). { apply restriction_MapsTo_iff; split. assumption. exists b1; assumption. }
    assert (merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) (restriction G G1) (restriction G G2) n = Some b). { apply merge_with_None_Some_eq. split; assumption. }
    rewrite <- restrmapsto. rewrite H2. reflexivity. }
  all: try (assert (~ In n ((restriction G G1) ᴳ+ (restriction G G2))) by (rewrite nIn_iff_nMapsTo; rewrite <- restrmapsto; reflexivity);
  apply nIn_union_iff in H0; rewrite 2 nIn_iff_nMapsTo in H0; rewrite <- 2 restriction_nIn_iff_nMapsTo in H0; destruct H0 as (H1 & H2); destruct H1, H2; trivial; try congruence).
  all: assert (In n ((restriction G G1) ᴳ+ (restriction G G2))) by (unfold In; exists b; unfold union; assumption); rewrite In_union_iff in H; destruct H; unfold In in H; destruct H as (b' & H); apply restriction_MapsTo_iff in H; destruct H; congruence.
Qed.

Lemma ctx_split_union_union : forall (G3 G4 G1 G2 : ctx), G1 # G2 -> G3 ᴳ+ G4 = G1 ᴳ+ G2 -> exists G13 G14 G23 G24, G1 = G13 ᴳ+ G14 /\ G2 = G23 ᴳ+ G24 /\ G3 = G13 ᴳ+ G23 /\ G4 = G14 ᴳ+ G24.
Proof.
  intros * DisjointG1G2 CtxEq.
  exists (restriction G3 G1), (restriction G4 G1), (restriction G3 G2), (restriction G4 G2). repeat split.
  - assert (restriction (G3 ᴳ+ G4) G1 = restriction (G1 ᴳ+ G2) G1). { rewrite CtxEq. reflexivity. } rewrite restriction_distrib_on_union in H. rewrite restriction_distrib_on_union in H. rewrite restriction_disjoint_empty with (G := G2) in H. 2:{ apply Disjoint_commutative; assumption. } rewrite restriction_self_eq in H. rewrite <- union_empty_r_eq in H. symmetry; assumption.
  - assert (restriction (G3 ᴳ+ G4) G2 = restriction (G1 ᴳ+ G2) G2). { rewrite CtxEq. reflexivity. } rewrite restriction_distrib_on_union in H. rewrite restriction_distrib_on_union in H. rewrite restriction_disjoint_empty with (G := G1) in H. 2:{ assumption. } rewrite restriction_self_eq in H. rewrite <- union_empty_l_eq in H. symmetry; assumption.
  - apply ctx_split_into_restrictions. assumption. rewrite <- CtxEq. apply DomSubset_union_l.
  - apply ctx_split_into_restrictions. assumption. rewrite <- CtxEq. apply DomSubset_union_r.
Qed.

Lemma ctx_split_stimes_union_3 : forall (m : mode) (G G1 G2 G3 : ctx), G1 # G2 -> G1 # G3 -> G2 # G3 -> m ᴳ· G = G1 ᴳ+ (G2 ᴳ+ G3) -> exists G1' G2' G3', G1 = m ᴳ· G1' /\ G2 = m ᴳ· G2' /\ G3 = m ᴳ· G3' /\ G = G1' ᴳ+ (G2' ᴳ+ G3').
Proof.
  intros * DisjointG1G2 DisjointG1G3 DisjointG2G3 CtxEq.
  destruct (ctx_split_stimes_union m G G1 (G2 ᴳ+ G3)) as (G1' & G2G3' & G1eq & G2G3eq & Geq); trivial. crush.
  apply eq_sym in G2G3eq.
  destruct (ctx_split_stimes_union m G2G3' G2 G3) as (G2' & G3' & G2eq & G3eq & G2G3eq_); trivial. rewrite G2G3eq_ in *. exists G1', G2', G3'. repeat split; trivial.
Qed.

Lemma ctx_split_union_union_3 : forall (G4 G5 G1 G2 G3 : ctx), G1 # G2 -> G1 # G3 -> G2 # G3 -> G4 ᴳ+ G5 = G1 ᴳ+ (G2 ᴳ+ G3) -> exists G14 G15 G24 G25 G34 G35, G1 = G14 ᴳ+ G15 /\ G2 = G24 ᴳ+ G25 /\ G3 = G34 ᴳ+ G35 /\ G4 = G14 ᴳ+ (G24 ᴳ+ G34) /\ G5 = G15 ᴳ+ (G25 ᴳ+ G35).
Proof.
  intros * DisjointG1G2 DisjointG1G3 DisjointG2G3 CtxEq.
  destruct (ctx_split_union_union G4 G5 G1 (G2 ᴳ+ G3)) as (G14 & G15 & G234 & G235 & G1eq & G2G3eq & G4eq & G5eq); trivial. crush.
  apply eq_sym in G2G3eq.
  destruct (ctx_split_union_union G234 G235 G2 G3) as (G24 & G25 & G34 & G35 & G2eq & G3eq & G234eq & G235eq); trivial. exists G14, G15, G24, G25, G34, G35. repeat split; trivial; subst; trivial.
Qed.

Lemma ctx_split_stimes_union_union : forall (m1 m2 : mode) (P1 P2 Pt : ctx) (x' : var) (m' : mode) (Tv' : type),
  ValidOnly (Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'}) ->
  Pt # ᴳ{ x' : m' ‗ Tv'} ->
  m1 ᴳ· P1 ᴳ+ m2 ᴳ· P2 = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'} ->
  ( exists m1' m2' Pt1 Pt2, m' = mode_plus (m1 · m1') (m2 · m2') /\ Pt = m1 ᴳ· Pt1 ᴳ+ m2 ᴳ· Pt2 /\ P1 = Pt1 ᴳ+ ᴳ{ x' : m1' ‗ Tv'} /\ P2 = Pt2 ᴳ+ ᴳ{ x' : m2' ‗ Tv'} ) \/
  ( exists m1' Pt1, m' = m1 · m1' /\ Pt = m1 ᴳ· Pt1 ᴳ+ m2 ᴳ· P2 /\ P1 = Pt1 ᴳ+ ᴳ{ x' : m1' ‗ Tv'} /\ ~In (ˣ x') P2) \/
  ( exists m2' Pt2, m' = m2 · m2' /\ Pt = m1 ᴳ· P1 ᴳ+ m2 ᴳ· Pt2 /\ P2 = Pt2 ᴳ+ ᴳ{ x' : m2' ‗ Tv'} /\ ~In (ˣ x') P1).
Proof.
  intros * ValidOnlyR DisjointPtx UnionEq.
  destruct (ctx_split_union_union (m1 ᴳ· P1) (m2 ᴳ· P2) Pt (ᴳ{ x' : m' ‗ Tv'}) DisjointPtx UnionEq) as (Pt1 & Pt2 & sing1 & sing2 & PtEq & singEq & P1eq & P2eq).
  destruct (ctx_split_stimes_union m1 P1 Pt1 sing1) as (Pt1' & sing1' & Pt1eq & sing1eq & P1eq'); trivial. { rewrite PtEq, singEq in DisjointPtx. crush. }
  destruct (ctx_split_stimes_union m2 P2 Pt2 sing2) as (Pt2' & sing2' & Pt2eq & sing2eq & P2eq'); trivial. { rewrite PtEq, singEq in DisjointPtx. crush. }
  destruct (union_inv_singleton_var sing1 sing2 x' m' Tv') as [[(m1'' & m2'' & sing1eq' & sing2eq' & m''eq) | (sing1eq' & sing2eq')] | (sing1eq' & sing2eq')].
  { apply ValidOnly_singleton_iff with (n := (ˣ x')) (binding := ₓ m' ‗ Tv'). crush. }
  { symmetry; assumption. }
  all: rewrite sing1eq', sing2eq' in *. clear sing1eq' sing1 sing2eq' sing2.
  - destruct (stimes_inv_singleton_var m1 sing1' x' m1'' Tv') as (m1' & m1eq & Pt1eq'); trivial. { symmetry; assumption. }
    destruct (stimes_inv_singleton_var m2 sing2' x' m2'' Tv') as (m2' & m2eq & Pt2eq'); trivial. { symmetry; assumption. }
    rewrite Pt1eq', Pt2eq', m1eq, m2eq in *. clear Pt1eq' Pt2eq' sing1' sing2' m1eq m2eq m1'' m2''. rewrite Pt1eq, Pt2eq in *. clear Pt1eq Pt2eq Pt1 Pt2. rewrite P1eq, P2eq in *.
    left. exists m1', m2', Pt1', Pt2'; repeat split; trivial.
  - apply eq_sym in sing2eq. apply stimes_empty_iff in sing2eq. rewrite sing2eq in *. clear sing2eq sing2eq' sing2 sing2'.
    destruct (stimes_inv_singleton_var m1 sing1' x' m' Tv') as (m1' & m1eq & Pt1eq'); trivial. { symmetry; assumption. }
    rewrite Pt1eq', m1eq in *. clear Pt1eq' sing1' sing1eq' m1eq.
    rewrite <- union_empty_r_eq in *. rewrite <- P2eq' in *. clear P2eq' Pt2'.
     rewrite Pt1eq, Pt2eq in *. clear Pt1eq Pt2eq Pt1 Pt2. rewrite P1eq in *.
     right. left. exists m1', Pt1'; repeat split; trivial.
     rewrite PtEq in DisjointPtx. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m1 · m1' ‗ Tv'). crush.
  - apply eq_sym in sing1eq. apply stimes_empty_iff in sing1eq. rewrite sing1eq in *. clear sing1eq sing1eq' sing1 sing1'.
    destruct (stimes_inv_singleton_var m2 sing2' x' m' Tv') as (m2' & m2eq & Pt2eq'); trivial. { symmetry; assumption. }
    rewrite Pt2eq', m2eq in *. clear Pt2eq' sing2' sing2eq' m2eq.
    rewrite <- union_empty_r_eq in *. rewrite <- P1eq' in *. clear P1eq' Pt1'.
    rewrite Pt1eq, Pt2eq in *. clear Pt1eq Pt2eq Pt1 Pt2. rewrite P2eq in *.
    right. right. exists m2', Pt2'; repeat split; trivial.
    rewrite PtEq in DisjointPtx. apply nIn_iff_Disjoint_singleton with (n := (ˣ x')) (binding := ₓ m2 · m2' ‗ Tv'). crush.
Qed.

Lemma singleton_is_one_of_disjoint_union : forall (n : name) (b : binding_type_of n) (G1 G2 : ctx), G1 # G2 -> ctx_singleton n b = G1 ᴳ+ G2 -> { G1 = ctx_singleton n b /\ G2 = ᴳ{} } + { G1 = ᴳ{} /\ G2 = ctx_singleton n b }.
Proof.
  intros * DisjointG1G2 union_eq.
  destruct (G1 n) eqn:G1mapsto.
  - left. unfold union in union_eq. split.
    * apply ext_eq. intros n'. destruct (ctx_singleton n b n') eqn:singmapsto.
        { pose proof singmapsto as singmapsto'. apply singleton_MapsTo_iff in singmapsto. apply eq_sigT_fst in singmapsto; subst. assert (ctx_singleton n' b n' = merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) G1 G2 n'). { rewrite union_eq. reflexivity. } rewrite singmapsto' in H. simpl in H. unfold Fun.merge, Fun.on_conflict_do in H. rewrite G1mapsto in H. assert (G2 n' = None). { rewrite <- nIn_iff_nMapsTo. intros nInG2. contradiction DisjointG1G2 with (x := n'). unfold In. exists b0; assumption. } rewrite H0 in H; cbn in H. inversion H; subst; trivial. }
        { apply nIn_iff_nMapsTo. apply nIn_iff_nMapsTo in singmapsto. intros contra. contradiction singmapsto. rewrite union_eq. apply In_union_iff. left; assumption. }
    * apply ext_eq. intros n'. destruct (ctx_singleton n b n') eqn:singmapsto.
        { pose proof singmapsto as singmapsto'. apply singleton_MapsTo_iff in singmapsto. apply eq_sigT_fst in singmapsto; subst. assert (ctx_singleton n' b n' = merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) G1 G2 n'). { rewrite union_eq. reflexivity. } rewrite singmapsto' in H. simpl in H. unfold Fun.merge, Fun.on_conflict_do in H. rewrite G1mapsto in H. destruct (G2 n') eqn:G2mapsto. 2:{ cbn; reflexivity. } contradiction DisjointG1G2 with (x := n'). unfold In. exists b0; assumption. unfold In. exists b2; assumption. }
        { apply nIn_iff_nMapsTo. apply nIn_iff_nMapsTo in singmapsto. intros contra. contradiction singmapsto. rewrite union_eq. apply In_union_iff. right; assumption. }
  - right. assert (exists b0, G2 n = Some b0). { assert (In n G2 -> (exists b0 : binding_type_of n, G2 n = Some b0)). { intros H. unfold In, Fun.In in H. assumption. } apply H. assert (In n (G1 ᴳ+ G2)). { rewrite <- union_eq. apply In_singleton_iff; reflexivity. } apply In_union_iff in H0. destruct H0. unfold In, Fun.In in H0. destruct H0. congruence. assumption. } destruct H as (b0 & G2mapsto). unfold union in union_eq. split.
    * apply ext_eq. intros n'. destruct (ctx_singleton n b n') eqn:singmapsto.
        { pose proof singmapsto as singmapsto'. apply singleton_MapsTo_iff in singmapsto. apply eq_sigT_fst in singmapsto; subst. assert (ctx_singleton n' b n' = merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) G1 G2 n'). { rewrite union_eq. reflexivity. } rewrite singmapsto' in H. simpl in H. cbn. assumption. }
        { apply nIn_iff_nMapsTo. apply nIn_iff_nMapsTo in singmapsto. intros contra. contradiction singmapsto. rewrite union_eq. apply In_union_iff. left; assumption. }
    * apply ext_eq. intros n'. destruct (ctx_singleton n b n') eqn:singmapsto.
        { pose proof singmapsto as singmapsto'. apply singleton_MapsTo_iff in singmapsto. apply eq_sigT_fst in singmapsto; subst. assert (ctx_singleton n' b n' = merge_with (fsimple (fun t : Type => t -> t -> t) union_var union_dh) G1 G2 n'). { rewrite union_eq. reflexivity. } rewrite singmapsto' in H. simpl in H. unfold Fun.merge, Fun.on_conflict_do in H. rewrite G2mapsto in H. rewrite G1mapsto in H. inversion H; subst; trivial. }
        { apply nIn_iff_nMapsTo. apply nIn_iff_nMapsTo in singmapsto. intros contra. contradiction singmapsto. rewrite union_eq. apply In_union_iff. right; assumption. }
Qed.

Lemma singleton_is_one_of_disjoint_union_3 : forall (n : name) (b : binding_type_of n) (G1 G2 G3 : ctx), G1 # G2 -> G1 # G3 -> G2 # G3 -> ctx_singleton n b = G1 ᴳ+ (G2 ᴳ+ G3) -> { G1 = ctx_singleton n b /\ G2 = ᴳ{} /\ G3 = ᴳ{} } + { G1 = ᴳ{} /\ G2 = ctx_singleton n b /\ G3 = ᴳ{} } + { G1 = ᴳ{} /\ G2 = ᴳ{} /\ G3 = ctx_singleton n b }.
Proof.
  intros * DisjointG1G2 DisjointG1G3 DisjointG2G3 union_eq.
  destruct (singleton_is_one_of_disjoint_union n b G1 (G2 ᴳ+ G3)).
  { crush. } { assumption. }
  - left. left. destruct a as (G1eq & empty_eq). repeat split.
    assumption. all: apply union_empty_iff in empty_eq; sauto.
  - destruct a as (empty_eq & union_eq'). apply eq_sym in union_eq'. destruct (singleton_is_one_of_disjoint_union n b G2 G3). { crush. } { crush. } all: destruct a as (G2eq & G3eq).
    * left. right. repeat split. all: assumption.
    * right. repeat split. all: assumption.
Qed.

Lemma singleton_eq_empty_contra : forall (n : name) (b : binding_type_of n), ctx_singleton n b = ᴳ{} -> False.
Proof.
  intros * contra. assert (In n (ctx_singleton n b)). { apply In_singleton_iff; reflexivity. } rewrite contra in H. destruct H. cbn in H. congruence.
Qed.

Lemma singleton_same_name_eq_iff : forall (n : name) (b b' : binding_type_of n), ctx_singleton n b = ctx_singleton n b' <-> b = b'.
Proof.
  intros. split; intros.
  2: { subst; reflexivity. }
  assert (ctx_singleton n b n = ctx_singleton n b' n). { rewrite H; reflexivity. }
  unfold ctx_singleton in H0. rewrite !singleton_MapsTo_at_elt in H0. inversion H0. reflexivity.
Qed.

Lemma singleton_eq_impl_same_name : forall (n n' : name) (b : binding_type_of n) (b' : binding_type_of n'), ctx_singleton n b = ctx_singleton n' b' -> n = n'.
Proof.
  intros * H. assert (ctx_singleton n b n = ctx_singleton n' b' n). { rewrite H; reflexivity. } unfold ctx_singleton in H0. rewrite !singleton_MapsTo_at_elt in H0. apply eq_sym in H0. rewrite singleton_MapsTo_iff in H0. apply eq_sigT_fst in H0. symmetry; assumption.
Qed.

Lemma singletons_var_eq_iff : forall (x1 x2 : var) (m1 m2 : mode) (T1 T2 : type), ᴳ{ x1 : m1 ‗ T1} = ᴳ{ x2 : m2 ‗ T2} <-> x1 = x2 /\ m1 = m2 /\ T1 = T2.
Proof.
  intros *.
  split.
  - intros H. assert (ᴳ{ x1 : m1 ‗ T1} (ˣ x1) = ᴳ{ x2 : m2 ‗ T2} (ˣ x1)). { rewrite H. reflexivity. } unfold ctx_singleton in H0. rewrite singleton_MapsTo_at_elt in H0. apply eq_sym in H0. apply singleton_MapsTo_iff in H0.
  assert (x2 = x1). { apply eq_sigT_fst in H0. inversion H0. reflexivity. } subst. apply inj_pair2_eq_dec in H0. inversion H0; subst. auto. exact name_eq_dec.
  - intros (-> & -> & ->). reflexivity.
Qed.

Lemma singletons_union_r_neq : forall (x1 x2 : var) (m1 m2 m3 : mode) (T1 T2 T3 : type), x1 <> x2 -> ᴳ{ x1 : m1 ‗ T1} ᴳ+ ᴳ{ x2 : m2 ‗ T2} = ᴳ{ x2 : m3 ‗ T3} -> False.
Proof.
  intros * neq H.
  assert ((ᴳ{ x1 : m1 ‗ T1} ᴳ+ ᴳ{ x2 : m2 ‗ T2}) (ˣ x1) = ᴳ{ x2 : m3 ‗ T3} (ˣ x1)). { rewrite H. reflexivity. }
  assert ((ᴳ{ x1 : m1 ‗ T1} ᴳ+ ᴳ{ x2 : m2 ‗ T2}) (ˣ x1) = Some (ₓ m1 ‗ T1)). { unfold ctx_singleton, union. rewrite (@merge_with_Some_None_eq name binding_type_of) with (x := (ˣ x1)) (y1 := (ₓ m1 ‗ T1)); split. apply singleton_MapsTo_at_elt. apply singleton_nMapsTo_iff. injection. intros contra. congruence. } rewrite H1 in H0.
  assert (ᴳ{ x2 : m3 ‗ T3} (ˣ x1) = None). { unfold ctx_singleton. apply singleton_nMapsTo_iff. injection. intros contra. congruence. } rewrite H2 in H0. congruence.
Qed.

Lemma singletons_union_l_neq : forall (x1 x2 : var) (m1 m2 m3 : mode) (T1 T2 T3 : type), x1 <> x2 -> ᴳ{ x1 : m1 ‗ T1} ᴳ+ ᴳ{ x2 : m2 ‗ T2} = ᴳ{ x1 : m3 ‗ T3} -> False.
Proof.
  intros * neq H. rewrite union_commutative in H. apply singletons_union_r_neq with (2 := H). symmetry. assumption.
Qed.
(*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*)
(* All the following lemmas are properties of typing relations on values, terms, or evaluation contexts, and substitution/filling *)
(*----------------------------------------------------------------------------*)

(* This lemma says that if we prove that a hole doesn't belong to a value, then filling this hole in the value results in the same inchanged value *)
Lemma val_fill_nIn_no_effect : forall (v v': val) (h : hname) (H : hnames) (G : ctx) (T : type), ~ In (ʰ h) G -> G ⫦ v : T -> val_fill v h H v' = v.
Proof.
  intros * nInG Tyv. dependent induction Tyv; simpl.
  rewrite nIn_iff_Disjoint_singleton with (n := (ʰ h)) (binding := ₊ T ‗ ¹ν) in nInG. rewrite Disjoint_singletons_iff in nInG. destruct (HNamesFacts.eq_dec h0 h). congruence. reflexivity.
  all: trivial.
  - f_equal. apply IHTyv; assumption.
  - f_equal. apply IHTyv; assumption.
  - f_equal. { apply IHTyv1. apply nIn_union_iff in nInG. crush. } { apply IHTyv2. apply nIn_union_iff in nInG. crush. }
  - f_equal. apply IHTyv. apply nIn_stimes_iff in nInG. crush.
Qed.

Lemma DisposableOnly_sub : forall (PtP : ctx) (x' : var) (m' : mode) (Tv' : type) (Dv' : ctx), ValidOnly Dv' -> DestOnly Dv' -> PtP # ᴳ{ x' : m' ‗ Tv'} -> PtP # Dv' -> DisposableOnly (PtP ᴳ+ ᴳ{ x' : m' ‗ Tv'}) -> DisposableOnly (PtP ᴳ+ m' ᴳ· Dv').
Proof.
  intros * ValidOnlyDv' DestOnlyDv' DisjointPtP DisjointDv' DisposPtP.
  apply DisposableOnly_union_forward. apply DisposableOnly_union_backward with (P2 := ᴳ{ x' : m' ‗ Tv'}). assumption. assumption.
  apply DisposableOnly_stimes_DestOnly_forward.
  apply DisposableOnly_singleton_var with (x := x') (T := Tv').
  apply DisposableOnly_union_backward with (P1 := PtP). assumption. assumption. assumption.
  assert (ValidOnly (PtP ᴳ+ ᴳ{ x' : m' ‗ Tv'})). { apply DisposableOnly_wk_ValidOnly. assumption. } assumption.
  apply Disjoint_stimes_r_iff. auto.
Qed.

Lemma IsValid_in_sub_1 : forall (x x' : var) (m m' : mode) (P Pt : ctx) (T Tv' : type), IsValid m' -> ValidOnly Pt -> Pt # ᴳ{ x' : m' ‗ Tv' } -> P ᴳ+ ᴳ{ x : m ‗ T } = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'} -> IsValid m.
Proof.
  intros * Validm' ValidOnlyPt DisjointPtP UnionEq.
  assert (ValidOnly (Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'})). { apply ValidOnly_union_forward; trivial. apply ValidOnly_singleton_iff. simpl; assumption. }
  assert (ValidOnly (P ᴳ+ ᴳ{ x : m ‗ T})). { rewrite UnionEq; assumption. }
  apply ValidOnly_union_backward in H0. destruct H0 as (ValidP & ValidSing).
  apply ValidOnly_singleton_iff in ValidSing. simpl in ValidSing; assumption.
Qed.

Lemma IsValid_in_sub_2 : forall (x1 x2 x' : var) (m m' : mode) (P Pt : ctx) (T1 T2 Tv' : type), IsValid m' -> ValidOnly Pt -> Pt # ᴳ{ x' : m' ‗ Tv' } -> P ᴳ+ ᴳ{ x1 : m ‗ T1 } ᴳ+ ᴳ{ x2 : m ‗ T2 } = Pt ᴳ+ ᴳ{ x' : m' ‗ Tv'} -> IsValid m.
Proof.
  intros * Validm' ValidOnlyPt DisjointPtP UnionEq.
  apply IsValid_in_sub_1 with (x := x2) (x' := x') (m' := m') (P := P ᴳ+ ᴳ{ x1 : m ‗ T1 }) (Pt := Pt) (T := T2) (Tv' := Tv'); trivial.
Qed.

(* This lemma says that if we prove that a variable doesn't belong to a term, then substituting this variable in the term results in the same inchanged term *)
Lemma term_sub_nIn_no_effect : forall (P : ctx) (te : term) (T : type) (x' : var) (v': val),
  ~(In (ˣ x') P) -> P ⊢ te : T -> te ᵗ[ x' ≔ v'] = te.
Proof.
  intros * NotInP Tyte. dependent induction Tyte; simpl.
  - reflexivity.
  - destruct (HNamesFacts.eq_dec x x').
    * rewrite e in *. contradiction NotInP. apply In_union_forward_r. apply In_singleton_iff. reflexivity.
    * reflexivity.
  - apply nIn_union_iff in NotInP. destruct NotInP. rewrite IHTyte1, IHTyte2. reflexivity. assumption. intros inP1. contradiction H. apply In_stimes_iff. assumption.
  - apply nIn_union_iff in NotInP. destruct NotInP. rewrite IHTyte1, IHTyte2. reflexivity. assumption. assumption.
  - rewrite IHTyte1. 2:{ apply nIn_union_iff in NotInP. destruct NotInP. intros inP1. contradiction H. apply In_stimes_iff. assumption. }
    destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst.
    * reflexivity.
    * rewrite IHTyte3. reflexivity. intros inP2x2. apply In_union_iff in inP2x2. destruct inP2x2. { unfold Disjoint in DisjointP2x1. specialize (DisjointP2x1 (ˣ x')). contradiction DisjointP2x1. apply In_singleton_iff. reflexivity. } { apply In_singleton_iff in H. inversion H. congruence. }
    * rewrite IHTyte2. reflexivity. intros inP1x1. apply In_union_iff in inP1x1. destruct inP1x1. { unfold Disjoint in DisjointP2x2. specialize (DisjointP2x2 (ˣ x')). contradiction DisjointP2x2. apply In_singleton_iff. reflexivity. } { apply In_singleton_iff in H. inversion H. congruence. }
    * rewrite IHTyte2, IHTyte3. reflexivity. all: apply nIn_union_iff; split.
    all: try apply nIn_union_iff in NotInP; try destruct NotInP; try assumption.
    intros inx2. apply In_singleton_iff in inx2. inversion inx2. congruence.
    intros inx1. apply In_singleton_iff in inx1. inversion inx1. congruence.
  - rewrite IHTyte1. 2: { apply nIn_union_iff in NotInP. destruct NotInP. intros inP1. contradiction H. apply In_stimes_iff. assumption. }
    destruct (HNamesFacts.eq_dec x1 x'), (HNamesFacts.eq_dec x2 x'); subst.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * rewrite IHTyte2. reflexivity. intros inP2x1x2. apply In_union_iff in inP2x1x2. destruct inP2x1x2.
      { apply In_union_iff in H. destruct H. contradiction NotInP. apply In_union_forward_r. assumption. apply In_singleton_iff in H. inversion H. congruence. }
      { apply In_singleton_iff in H. inversion H. congruence. }
  - rewrite IHTyte1. 2: { apply nIn_union_iff in NotInP. destruct NotInP. intros inP1. contradiction H. apply In_stimes_iff. assumption. }
    destruct (HNamesFacts.eq_dec x x'); subst.
    * reflexivity.
    * rewrite IHTyte2. reflexivity. intros inP2x. apply In_union_iff in inP2x. destruct inP2x. { apply nIn_union_iff in NotInP. destruct NotInP. congruence. } { apply In_singleton_iff in H. inversion H. congruence. }
  - rewrite IHTyte1. 2: { apply nIn_union_iff in NotInP. destruct NotInP. assumption. }
    destruct (HNamesFacts.eq_dec x x'); subst.
    * reflexivity.
    * rewrite IHTyte2. reflexivity. intros inP2x. apply In_union_iff in inP2x. destruct inP2x. { apply nIn_union_iff in NotInP. destruct NotInP. apply In_stimes_iff in H. congruence. } { apply In_singleton_iff in H. inversion H. congruence. }
  - rewrite IHTyte. reflexivity. assumption.
  - rewrite IHTyte. reflexivity. assumption.
  - reflexivity.
  - rewrite IHTyte. reflexivity. assumption.
  - rewrite IHTyte. reflexivity. assumption.
  - rewrite IHTyte. reflexivity. assumption.
  - rewrite IHTyte. reflexivity. assumption.
  - rewrite IHTyte. reflexivity. assumption.
  - rewrite IHTyte1. 2: { apply nIn_union_iff in NotInP. destruct NotInP. assumption. }
    destruct (HNamesFacts.eq_dec x x'); subst.
    * reflexivity.
    * rewrite IHTyte2. reflexivity. intros inP2x. apply In_union_iff in inP2x. destruct inP2x. { apply nIn_union_iff in NotInP. destruct NotInP. contradiction H1. apply In_stimes_iff. assumption. } { apply In_singleton_iff in H. inversion H. congruence. }
  - rewrite IHTyte1. 2: { apply nIn_union_iff in NotInP. destruct NotInP. assumption. }
    rewrite IHTyte2. 2: { apply nIn_union_iff in NotInP. destruct NotInP. intros inP2. contradiction H0. apply In_stimes_iff. assumption. }
    reflexivity.
  - rewrite IHTyte1. 2: { apply nIn_union_iff in NotInP. destruct NotInP. assumption. }
    rewrite IHTyte2. 2: { apply nIn_union_iff in NotInP. destruct NotInP. intros inP2. contradiction H0. apply In_stimes_iff. assumption. }
    reflexivity.
Qed.

Lemma Ty_val_NoVar : forall (G : ctx) (v : val) (T : type) (Ty: G ⫦ v : T), NoVar G.
Proof.
  intros * Ty. induction Ty; unfold NoVar; intros nam b mapstoG contra.
  - unfold ctx_singleton in mapstoG. rewrite singleton_MapsTo_iff in mapstoG. apply eq_sigT_fst in mapstoG; subst. inversion contra.
  - unfold ctx_singleton in mapstoG. rewrite singleton_MapsTo_iff in mapstoG. apply eq_sigT_fst in mapstoG; subst. inversion contra.
  - unfold ctx_empty in mapstoG. simpl in mapstoG. congruence.
  - unfold DestOnly in DestOnlyD. unfold NoVar in contra. specialize (DestOnlyD nam b mapstoG). destruct nam. { inversion DestOnlyD. } { inversion contra. }
  - unfold NoVar in IHTy. specialize (IHTy nam b mapstoG). congruence.
  - unfold NoVar in IHTy. specialize (IHTy nam b mapstoG). congruence.
  - assert (In nam (G1 ᴳ+ G2)). { apply In_iff_exists_Some; exists b; tauto. }
    apply In_merge_iff in H. destruct H.
    + destruct H. unfold NoVar in IHTy1. specialize (IHTy1 nam x H). unfold IsVar in IHTy1. destruct nam. specialize (IHTy1 I); assumption. inversion contra.
    + destruct H. unfold NoVar in IHTy2. specialize (IHTy2 nam x H). unfold IsVar in IHTy2. destruct nam. specialize (IHTy2 I); assumption. inversion contra.
  - apply map_MapsTo_iff in mapstoG. destruct mapstoG. destruct H.
    unfold NoVar in IHTy. specialize (IHTy nam x H). unfold IsVar in IHTy. destruct nam. specialize (IHTy I); assumption. inversion contra.
  - assert (In nam (D1 ᴳ+ D2)). { apply In_iff_exists_Some; exists b; tauto. }
    apply In_merge_iff in H. destruct H.
    + assert (In nam (¹↑ ᴳ· D1 ᴳ+ D3)). { apply In_iff_exists_Some. apply In_merge_iff. left. apply In_map_iff. assumption. }
      destruct H0. unfold NoVar in IHTy1. specialize (IHTy1 nam x H0). unfold IsVar in IHTy1. destruct nam. specialize (IHTy1 I); assumption. inversion contra.
    + assert (In nam (D2 ᴳ+ (ᴳ-⁻¹ D3))). { apply In_iff_exists_Some. apply In_merge_iff. left. assumption. }
      destruct H0. unfold NoVar in IHTy2. specialize (IHTy2 nam x H0). unfold IsVar in IHTy2. destruct nam. specialize (IHTy2 I); assumption. inversion contra.
Qed.

Lemma Ty_val_Hole_DestOnly_contra : forall (D : ctx) (h : hname) (T : type), (D ⫦ ᵛ+ h : T) -> DestOnly D -> False.
Proof.
  intros D h T Tyv DestOnlyD. inversion Tyv; subst.
  specialize (DestOnlyD (ʰ h)). unfold DestOnly, ctx_singleton in DestOnlyD. specialize (DestOnlyD (₊ T ‗ ¹ν)). rewrite singleton_MapsTo_iff in DestOnlyD. sfirstorder.
Qed.

(* These lemmas prove that a well-typed value (resp. term) is still well-typed when we used conditional shift on both the typing context and the value (resp. term) *)
Lemma Ty_val_cshift : forall (G : ctx) (v : val) (T : type) (H: hnames) (h': hname), (G ⫦ v : T) -> (G ᴳ[ H⩲h' ] ⫦ v ᵛ[H⩲h'] : T)
with Ty_term_cshift : forall (G : ctx) (t : term) (T : type) (H: hnames) (h': hname), (G ⊢ t : T) -> (G ᴳ[ H⩲h' ] ⊢ term_cshift t H h' : T).
Proof.
  - destruct 1.
    + cbn. rewrite cshift_singleton_hname.
      constructor.
    + cbn. rewrite cshift_singleton_hname.
      constructor. assumption.
    + replace (ᴳ{} ᴳ[ H ⩲ h']) with ᴳ{}.
      2:{ apply ext_eq. cbn. congruence. }
      cbn.
      constructor.
    + cbn.
      constructor.
      * assumption.
      * hauto l: on use: DestOnly_cshift_iff.
      * erewrite <- cshift_singleton_var_eq, <- cshift_distrib_on_union.
        auto.
    + cbn.
      constructor. auto.
    + cbn.
      constructor. auto.
    + cbn. rewrite cshift_distrib_on_union.
      constructor. all: auto.
    + cbn. rewrite cshift_distrib_on_stimes.
      constructor. all: auto.
    + cbn. rewrite cshift_distrib_on_union, cshift_distrib_on_hnames.
      constructor.
      (* 11 goals *)
      * hauto l: on use: DestOnly_cshift_iff.
      * hauto l: on use: DestOnly_cshift_iff.
      * hauto l: on use: DestOnly_cshift_iff.
      * rewrite <- cshift_distrib_on_hminus_inv. rewrite <- ValidOnly_cshift_iff. assumption.
      * hauto l: on use: Disjoint_cshift_iff.
      * hauto l: on use: Disjoint_cshift_iff.
      * hauto l: on use: Disjoint_cshift_iff.
      * rewrite <- cshift_distrib_on_stimes, <- cshift_distrib_on_union.
        auto.
      * rewrite <- cshift_distrib_on_hminus_inv, <- cshift_distrib_on_union.
        auto.
  - destruct 1.
    { cbn. rewrite cshift_distrib_on_union. apply Ty_term_Val. apply Disjoint_cshift_iff. assumption. apply DisposableOnly_cshift_iff. assumption.
      eapply Ty_val_cshift; trivial.
      apply DestOnly_cshift_iff; assumption. }
    { cbn. rewrite cshift_distrib_on_union. rewrite cshift_singleton_var_eq.
     apply Ty_term_Var. apply DisposableOnly_cshift_iff. assumption.
     rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. assumption. }
    all: cbn; try rewrite cshift_distrib_on_union; try rewrite cshift_distrib_on_stimes; try rewrite cshift_distrib_on_stimes.
    * apply Ty_term_App with (T := T); trivial. eapply Ty_term_cshift; trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_PatU; trivial. eapply Ty_term_cshift; trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_PatS with (T1 := T1) (T2 := T2); trivial. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. eapply Ty_term_cshift; trivial.
    rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). rewrite <- cshift_distrib_on_union. eapply Ty_term_cshift; trivial.
    rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). rewrite <- cshift_distrib_on_union. eapply Ty_term_cshift; trivial.
    * apply Ty_term_PatP with (T1 := T1) (T2 := T2); trivial. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. eapply Ty_term_cshift; trivial.
    rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). rewrite <- cshift_singleton_var_eq with (x := x2) (H := H) (h' := h'). rewrite <- cshift_distrib_on_union. rewrite <- cshift_distrib_on_union. eapply Ty_term_cshift; trivial.
    * apply Ty_term_PatE with (T := T); trivial. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. eapply Ty_term_cshift; trivial.
    rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). rewrite <- cshift_distrib_on_union. eapply Ty_term_cshift; trivial.
    * apply Ty_term_UpdA with (T := T). rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. eapply Ty_term_cshift; trivial. rewrite <- cshift_distrib_on_stimes. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). rewrite <- cshift_distrib_on_union. eapply Ty_term_cshift; trivial.
    * apply Ty_term_ToA. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FromA. eapply Ty_term_cshift; trivial.
    * apply Ty_term_NewA. apply DisposableOnly_cshift_iff. assumption.
    * apply Ty_term_FillU with (n := n); trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillL with (n := n) (T2 := T2); trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillR with (n := n) (T1 := T1); trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillP with (n := n) (T1 := T1) (T2 := T2); trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillE with (n := n) (T := T); trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillF with (T := T) (U := U); trivial. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). apply Disjoint_cshift_iff; assumption. eapply Ty_term_cshift; trivial. rewrite <- cshift_singleton_var_eq with (H := H) (h' := h'). rewrite <- cshift_distrib_on_union. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillComp with (U := U). eapply Ty_term_cshift; trivial. eapply Ty_term_cshift; trivial.
    * apply Ty_term_FillLeaf with (T := T); trivial. eapply Ty_term_cshift; trivial. eapply Ty_term_cshift; trivial.
Qed.

Lemma Ty_ectxs_DestOnly : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), DestOnly D.
Proof.
  intros * TyC. induction TyC.
  all: crush.
Qed.

Lemma Ty_ectxs_HDisjoint_to_Disjoint : forall (C : ectxs) (D D' : ctx) (T U0 : type) (TyC : D ⊣ C : T ↣ U0), hnames©(C) ## hnamesᴳ(D') -> D # D'.
Proof.
  intros * TyC hnamesDisjoint. pose proof TyC as TyC'.
  apply hnames_C_wk_hnames_G in TyC.
  assert (hnamesᴳ(D) ## hnamesᴳ( D')). { apply HSubset_preserves_HDisjoint with (H2 := hnames©(C)); assumption. }
  apply HDisjoint_to_Disjoint in H. assumption. apply Ty_ectxs_DestOnly in TyC'. assumption.
Qed.

Lemma Ty_ectxs_LinOnly_FinAgeOnly : forall (D : ctx) (C : ectxs) (T U0 : type) (TyC: D ⊣ C : T ↣ U0), LinOnly D /\ FinAgeOnly D.
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
    hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - destruct IHTy_ectxs as (LinOnlyD & FinAgeOnlyD).
    hauto lq: on use: LinOnly_union_iff, LinOnly_stimes_backward, FinAgeOnly_union_backward, FinAgeOnly_stimes_backward, LinOnly_wk_ValidOnly.
  - destruct IHTy_ectxs as (LinOnlyD & FinAgeOnlyD). apply LinOnly_union_iff in LinOnlyD. destruct LinOnlyD as (LinOnlyD1 & LinOnlyD2 & _). apply FinAgeOnly_union_backward in FinAgeOnlyD. destruct FinAgeOnlyD as (FinAgeOnlyD1 & FinAgeOnlyD2). split.
    * apply LinOnly_union_iff; repeat split. apply LinOnly_stimes_forward. constructor. assumption. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & ValidOnlyhiD3). apply LinNuOnly_wk_LinOnly in ValidOnlyhiD3; tauto. } apply Disjoint_stimes_l_iff. assumption.
    * apply FinAgeOnly_union_forward; repeat split. apply FinAgeOnly_stimes_forward. constructor. assumption. { apply ValidOnly_hminus_inv_DestOnly_LinNuOnly in ValidOnlyhiD3. destruct ValidOnlyhiD3 as (_ & ValidOnlyhiD3). apply LinNuOnly_wk_FinAgeOnly in ValidOnlyhiD3; tauto. } apply Disjoint_stimes_l_iff. assumption.
Qed.

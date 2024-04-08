Require List.
Require FMapList.
Require MSetList.
Require Import Psatz.
Require Import Coq.Structures.OrderedType.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
From SMTCoq Require Import SMTCoq.
Require MMaps.OrdList.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Set Primitive Projections.

(* Plan: we're making a cheap dependent map out of three component
   maps. For extensibility purposes, we're not going to assume that
   the type of names is the same in each variant.

   I [aspiwack] am a little worried about changing our minds about
   details later. This is why I'm organising proofs in reference to a
   functional semantics. The interface to reprove will be smaller. *)

Module Fun.

  (* Note: this mirrors the design of MMaps. Except that we're
     ignoring everything about setoids since we won't be needing them
     for our use-case. *)

  (* TODO: map, merge (already done), proof of support for each. Then
     make a type of finitely supported map (don't care about
     equality). Implement the Admitted/Parameter definitions in
     grammar.ott. *)

Definition In {A B} (x:A) (f:forall x:A, option (B x)) : Prop := exists y, f x = Some y.

Lemma In_None1 : forall {A B} (x:A) (f:forall x:A, option (B x)), In x f <-> f x <> None.
Proof.
  unfold In.
  intros *. split.
  - intros [y ->].
    discriminate.
  - intros h. unfold In.
    destruct (f x).
    + eexists.
      reflexivity.
    + contradiction h.
      reflexivity.
Qed.

Lemma In_None2 : forall {A B} (x:A) (f:forall x:A, option (B x)), ~(In x f) <-> f x = None.
Proof.
  intros *.
  rewrite In_None1.
  destruct (f x).
  - sfirstorder.
  - sfirstorder.
Qed.

Lemma In_dec :  forall {A B} (x : A) (f : forall x:A, option (B x)), In x f \/ ~In x f.
Proof.
  intros *. unfold In.
  destruct (f x) as [b|].
  all: sfirstorder.
Qed.

Definition Support {A B} (l : list A) (f : forall x:A, option (B x)) : Prop :=
  forall (x:A) (y:B x), f x = Some y -> List.In x l.

Lemma In_supported : forall {A B} (f:forall x:A, option (B x)) l, Support l f <-> forall x, In x f -> List.In x l.
Proof.
  firstorder.
Qed.

Lemma In_supported_r : forall {A B} (f:forall x:A, option (B x)) l, Support l f -> forall x, impl (In x f) (List.In x l).
Proof.
  firstorder.
Qed.

Lemma out_of_support_is_None : forall {A B} (f:forall x:A, option (B x)) l, Support l f -> forall x, ~List.In x l -> f x = None.
Proof.
  intros * h x hnin.
  apply In_None2.
  hauto lq: on use: In_supported.
Qed.

(* Not the most general statement: we only need finite preimages for elements in f's support. *)
Lemma precomp_support : forall {A B C} (g:A->B) (preimg : B -> list A) (f : forall x:B, option (C x)) (l : list B),
    (forall x w, g w = x -> List.In w (preimg x)) -> Support l f ->
    Support (flat_map preimg l) (fun w => f (g w)).
Proof.
  intros * h_preimg h_l. unfold Support in *.
  intros w y h_w.
  rewrite in_flat_map.
  exists (g w).
  split.
  all: sfirstorder.
Qed.

Definition singleton {A B} (x : A) (discr : forall x y, {x = y} + {x<>y}) (v : B x) (y : A) : option (B y) :=
  match discr x y with
  | left e =>
      (* Silly, but deep pattern-matching confuses Coq here. *)
      match e with eq_refl => Some v end
  | right _ => None
  end.

Lemma singleton_support : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), Support (x :: nil) (singleton x discr v).
Proof.
  intros *. unfold Support, singleton. intros y w.
  hauto lq: on.
Qed.

Lemma in_singleton : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A), In y (singleton x discr v) <-> y = x.
Proof.
  intros *. unfold In, singleton.
  hauto q: on.
Qed.

Lemma singleton_spec_1 : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), singleton x discr v x = Some v.
Proof.
  intros *. unfold singleton.
  hauto dep: on.
Qed.

Lemma mapsto_singleton : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A) (v': B y), (singleton x discr v) y = Some v' <-> existT B x v = existT B y v'.
Proof.
  intros *. unfold singleton.
  destruct (discr x y) as [e|c].
  - destruct e. split.
    * intros eq. inversion eq; subst. tauto.
    * intros eq. apply inj_pair2_eq_dec in eq. subst. all: tauto.
  - split.
    * intros h. inversion h.
    * intros h. contradiction c. inversion h; tauto.
Qed.

Definition map {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) (x : A) : option (B2 x) :=
  match f x with
  | Some y => Some (m x y)
  | None => None
  end.

Lemma map_In : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) x, In x f <-> In x (map m f).
Proof.
  intros *. unfold In, map.
  destruct (f x).
  all: hauto lq: on.
Qed.

Lemma map_ext : forall {A B1 B2} (m1 m2 : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) x,
    (forall x, m1 x = m2 x) -> map m1 f x = map m2 f x.
Proof.
  intros * h. unfold map.
  hauto lq: on.
Qed.

Lemma map_comp : forall {A B1 B2 B3} (m1 : forall x, B1 x -> B2 x) (m2 : forall x, B2 x -> B3 x) (f : forall x:A, option (B1 x)) x, map m2 (map m1 f) x = map (fun x y => m2 x (m1 x y)) f x.
Proof.
  intros *. unfold map.
  hauto lq: on.
Qed.

(* Not great: Q can never been inferred. But better than nothing. Easy case: map_propagate_forward'. *)
Lemma map_propagate_forward : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y1, f x = Some y1 -> Q x y1) -> (forall x y1, Q x y1 -> P x (m x y1)) -> forall x y2, map m f x = Some y2 -> P x y2.
Proof.
  intros * hf hm x y2 hy2. unfold map in *.
  specialize (hf x).
  destruct (f x) as [h_inf|].
  - injection hy2 as [= <-].
    sfirstorder.
  - scongruence.
Qed.

Lemma map_propagate_forward' : forall {A B} (m : forall x, B x -> B x) (f : forall x:A, option (B x)) (P : forall x, B x -> Prop),
    (forall x y1, f x = Some y1 -> P x y1) -> (forall x y1, P x y1 -> P x (m x y1)) -> forall x y2, map m f x = Some y2 -> P x y2.
Proof.
  intros *.
  apply map_propagate_forward.
Qed.

Lemma map_propagate_backward : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y2, map m f x = Some y2 -> P x y2) -> (forall x y1, P x (m x y1) -> Q x y1) -> (forall x y1, f x = Some y1 -> Q x y1).
Proof.
  intros * hmap hm x y1 hy1.
  hfcrush unfold: map.
Qed.

Lemma map_propagate_backward' : forall {A B} (m : forall x, B x -> B x) (f : forall x:A, option (B x)) (P : forall x, B x -> Prop),
    (forall x y2, map m f x = Some y2 -> P x y2) -> (forall x y1, P x (m x y1) -> P x y1) -> (forall x y1, f x = Some y1 -> P x y1).
Proof.
  intros *.
  apply map_propagate_backward.
Qed.

Lemma map_propagate_both : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y1, P x (m x y1) <-> Q x y1) -> (forall x y2, map m f x = Some y2 -> P x y2) <-> (forall x y1, f x = Some y1 -> Q x y1).
Proof.
  intros * hm.
  split.
  - hauto lq: on use: map_propagate_backward.
  - hfcrush use: map_propagate_forward.
Qed.

Lemma map_propagate_both' : forall {A B} (m : forall x, B x -> B x) (f : forall x:A, option (B x)) (P : forall x, B x -> Prop),
    (forall x y1, P x (m x y1) <-> P x y1) -> (forall x y2, map m f x = Some y2 -> P x y2) <-> (forall x y1, f x = Some y1 -> P x y1).
Proof.
  intros *.
  apply map_propagate_both.
Qed.

Definition map_support : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) l, Support l f -> Support l (map m f).
Proof.
  intros * h. unfold Support, map in *.
  intros x. specialize (h x).
  destruct (f x).
  - eauto.
  - intros ? [=].
Qed.

Definition merge {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) (x:A) : option (B3 x) :=
  match f x, g x with
  | None, None => None
  | fx, gx => m x fx gx
  end.

Lemma merge_spec1 : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) (x:A),
    In x f \/ In x g -> merge m f g x = m x (f x) (g x).
Proof.
  unfold merge.
  hauto lq: on.
Qed.

Lemma merge_spec2 : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) (x:A),
    In x (merge m f g) -> In x f \/ In x g.
Proof.
  unfold merge.
  hauto lq: on.
Qed.

Lemma merge_commutative : forall {A B} (m : forall x:A, option (B x) -> option (B x) -> option (B x)) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) x,
    (forall y1 y2, m x y1 y2 = m x y2 y1) -> merge m f g x = merge m g f x.
Proof.
  intros * h. unfold merge.
  destruct (f x) as [yf|]; destruct (g x) as [yg|].
  all: sfirstorder.
Qed.

(* Note, there are weaker requirements than requiring that `m x None
   None = None` and `m` associative such as requiring that `m' = m`
   except that `m' None None = None` is associative. But it isn't
   clear that it's worth generalising. *)
Lemma merge_associative : forall {A B} (m : forall x:A, option (B x) -> option (B x) -> option (B x)) (f g h: forall x:A, option (B x)) x,
    (m x None None = None) -> (forall y1 y2 y3, m x y1 (m x y2 y3) = m x (m x y1 y2) y3) -> merge m f (merge m g h) x = merge m (merge m f g) h x.
Proof.
  intros * H_None H. unfold merge.
  destruct (f x) as [yf|]; destruct (g x) as [yg|]; destruct (h x) as [yh|]. all: cbn.
  all: hauto l: on.
Qed.

Lemma merge_support : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) lf lg, Support lf f -> Support lg g -> Support (lf ++ lg) (merge m f g).
Proof.
  intros * h_suppf h_suppg.
  apply In_supported. intros x h_in.
  qauto l: on use: In_supported, in_or_app, merge_spec2.
Qed.


Definition merge_fun_of_with {A B} (m : forall x:A, B x -> B x -> B x) (x:A) (y1 : option (B x)) (y2 : option (B x)) : option (B x) :=
  match y1, y2 with
  | Some y1', Some y2' => Some (m x y1' y2')
  | Some y, None | None, Some y => Some y
  | None, None => None
  end.

(* A most common instance of merge. *)
Definition merge_with {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) : forall (x:A), option (B x) :=
  merge (merge_fun_of_with m) f g.

Lemma merge_with_spec_1 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) (y1 y2:B x),
    f x = Some y1 /\ g x = Some y2 -> merge_with m f g x = Some (m x y1 y2).
Proof.
  unfold merge_with.
  hauto lq: on use: @merge_spec1.
Qed.

Lemma merge_with_spec_2 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) (y1:B x),
    f x = Some y1 /\ g x = None -> merge_with m f g x = Some y1.
Proof.
  unfold merge_with.
  hauto lq: on use: @merge_spec1.
Qed.

Lemma merge_with_spec_3 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) (y2:B x),
    f x = None /\ g x = Some y2 -> merge_with m f g x = Some y2.
Proof.
  unfold merge_with.
  hauto lq: on use: @merge_spec1.
Qed.

Lemma merge_with_spec_4 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A),
    f x = None /\ g x = None -> merge_with m f g x = None.
Proof.
  unfold merge_with, merge.
  hauto lq: on.
Qed.

Lemma merge_with_spec_5 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A),
    In x (merge_with m f g) <-> In x f \/ In x g.
Proof.
  split.
  - hauto lq: on use :@merge_spec2.
  - unfold merge_with, merge, In.
    hauto.
Qed.

Lemma merge_with_propagate_backward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x b1 b2, P x (m x b1 b2) -> P x b1 /\ P x b2) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h h0.
  (* factoring of conclusion to avoid duplicating the proof. *)
  assert (forall x, (forall (b : B x), f x = Some b -> P x b) /\ (forall (b : B x), g x = Some b -> P x b)).
  2:{ sfirstorder. }
  intros x. specialize (h0 x).
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?In_None2 in *.
  - erewrite merge_with_spec_1 in h0.
    2:{ eauto. }
    hecrush.
  - erewrite merge_with_spec_2 in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_spec_3 in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_spec_4 in h0.
    all: hfcrush.
Qed.

Lemma merge_with_propagate_backward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x b1 b2, ~P x (m x b1 b2)) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b)/\(forall x, In x f -> In x g -> False).
Proof.
  intros * h h0.
  (* factoring of conclusion to avoid duplicating the proof. *)
  assert (forall x, (forall (b : B x), f x = Some b -> P x b) /\ (forall (b : B x), g x = Some b -> P x b) /\ (In x f -> In x g -> False)).
  2:{ sfirstorder. }
  intros x. specialize (h0 x).
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?In_None2 in *.
  - erewrite merge_with_spec_1 in h0.
    2:{ eauto. }
    hecrush.
  - erewrite merge_with_spec_2 in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_spec_3 in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_spec_4 in h0.
    all: hfcrush.
Qed.

Lemma merge_with_propagate_backward_disjoint' : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x, In x f -> In x g -> False) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h_disj h.
  (* factoring of conclusion to avoid duplicating the proof. *)
  assert (forall x, (forall (b : B x), f x = Some b -> P x b) /\ (forall (b : B x), g x = Some b -> P x b)).
  2:{ sfirstorder. }
  intros x. specialize (h x).
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?In_None2 in *.
  - sfirstorder.
  - erewrite merge_with_spec_2 in h.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_spec_3 in h.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_spec_4 in h.
    all: hfcrush.
Qed.

Lemma merge_with_propagate_forward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
     (forall x b1 b2, P x b1 /\ P x b2 -> P x (m x b1 b2)) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b h_merge.
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?In_None2 in *.
  - erewrite merge_with_spec_1 in h_merge.
    2:{ eauto. }
    hauto l: on.
  - erewrite merge_with_spec_2 in h_merge.
    2:{ eauto. }
    hauto l: on.
  - erewrite merge_with_spec_3 in h_merge.
    2:{ eauto. }
    hauto l: on.
  - sblast use: merge_with_spec_4.
Qed.

Lemma merge_with_propagate_forward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x, In x f -> In x g -> False) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b h_merge.
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?In_None2 in *.
  - hauto l: on.
  - erewrite merge_with_spec_2 in h_merge.
    2:{ eauto. }
    hauto l: on.
  - erewrite merge_with_spec_3 in h_merge.
    2:{ eauto. }
    hauto l: on.
  - hauto lq: on use: merge_with_spec_4.
Qed.

Lemma merge_with_propagate_both : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x b1 b2, P x (m x b1 b2) <-> P x b1 /\ P x b2) -> (forall x b, merge_with m f g x = Some b -> P x b) <-> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h.
  split.
  - eapply merge_with_propagate_backward.
    sfirstorder.
  - intros [? ?].
    eapply merge_with_propagate_forward.
    all: sfirstorder.
Qed.

Lemma merge_with_propagate_both_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x b1 b2, ~P x (m x b1 b2)) -> (forall x b, merge_with m f g x = Some b -> P x b) <-> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b)/\(forall x, In x f -> In x g -> False).
Proof.
  intros * h.
  split.
  - hfcrush use: merge_with_propagate_backward_disjoint.
  - sfirstorder use: merge_with_propagate_forward_disjoint.
Qed.

Lemma merge_with_commutative : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) x,
    (forall y1 y2, m x y1 y2 = m x y2 y1) -> merge_with m f g x = merge_with m g f x.
Proof.
  intros * h. unfold merge_with.
  apply merge_commutative. unfold merge_fun_of_with.
  intros [] [].
  all: sfirstorder.
Qed.

Lemma merge_with_associative : forall {A B} (m : forall x:A, B x -> B x -> B x) (f g h: forall x:A, option (B x)) x,
    (forall y1 y2 y3, m x y1 (m x y2 y3) = m x (m x y1 y2) y3) -> merge_with m f (merge_with m g h) x = merge_with m (merge_with m f g) h x.
Proof.
  intros * H. unfold merge_with.
  apply merge_associative.
  all: sauto.
Qed.

End Fun.

(* Optionally, we could make a notation for this type. Something like "finitely (x:A), B". *)
Record T A B := {
    underlying :> forall x:A, option (B x);
    support : list A;
    support_supports : Fun.Support support underlying
  }.
Arguments underlying {A B}.
Arguments support {A B}.

Lemma ext_eq : forall {A B} (f g : T A B), (forall x, f x = g x) -> (f.(support) = g.(support)) -> f = g.
Proof.
  intros A B [f f_supp h_f] [g g_supp h_g] h_ext h_supp. cbn in *.
  assert (f = g) as e.
  { apply functional_extensionality_dep. assumption. }
  subst g. subst g_supp.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition In {A B} (x : A) (f : T A B) : Prop := Fun.In x f.

Lemma In_spec : forall {A B} (x : A) (f : T A B), In x f <-> exists y, f x = Some y.
Proof.
  sfirstorder.
Qed.

Lemma In_None1 : forall {A B} (x:A) (f:T A B), In x f <-> f x <> None.
Proof.
  intros *.
  hauto lq: on unfold: In use: Fun.In_None1.
Qed.

Lemma In_None2 : forall {A B} (x:A) (f: T A B), ~(In x f) <-> f x = None.
Proof.
  intros *.
  hauto lq: on unfold: In use: Fun.In_None2.
Qed.

Lemma In_dec :  forall {A B} (x : A) (f : T A B), In x f \/ ~In x f.
Proof.
  intros *. rewrite !In_spec.
  destruct (f x) as [y|].
  all:sfirstorder.
Qed.

Definition dom {A B} (f : T A B) : list A :=
  List.filter (fun x => match f x with Some _ => true | None => false end) f.(support).

Lemma dom_spec : forall {A B} (f : T A B) (x : A), List.In x (dom f) <-> In x f.
Proof.
  intros *. unfold dom.
  split.
  - rewrite filter_In.
    hauto l: on.
  - rewrite filter_In.
    rewrite <- (Fun.In_supported_r f).
    + sauto.
    + apply support_supports.
Qed.

Lemma dom_Support : forall {A B} (f : T A B), Fun.Support (dom f) f.
Proof.
  intros *.
  rewrite Fun.In_supported.
  hauto lq: on use: dom_spec.
Qed.

#[program]
Definition empty {A B} : T A B :=
  {|
    underlying := fun _ => None;
    support := nil
  |}.

#[program]
Definition singleton {A B} (x : A) (discr : forall x y, {x = y} + {x<>y}) (v : B x) : T A B :=
  {|
    underlying := Fun.singleton x discr v;
    support := x::nil;
  |}.
Next Obligation.
  hauto lq: on use: Fun.singleton_support.
Qed.

Lemma singleton_spec0 : forall {A B} (x : A) (discr : forall x y, {x = y} + {x<>y}) (v : B x) (y : A),
    singleton x discr v y = Fun.singleton x discr v y.
Proof.
  intros *.
  sfirstorder.
Qed.

Lemma in_singleton : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A), In y (singleton x discr v) <-> y = x.
Proof.
  intros *.
  hauto lq: on use: In_spec, singleton_spec0, Fun.in_singleton.
Qed.

Lemma mapsto_singleton : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A) (v': B y), (singleton x discr v) y = Some v' <-> existT B x v = existT B y v'.
Proof.
  intros *. rewrite singleton_spec0. apply Fun.mapsto_singleton.
Qed.

Lemma singleton_spec_1 : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), singleton x discr v x = Some v.
Proof.
  intros *. rewrite singleton_spec0.
 apply Fun.singleton_spec_1.
Qed.

(** Design note: precomp is defined using a subtype rather than a
    precondition. Because this way, Program can defer the precondition
    to an obligation.

    e.g. (partially pseudo syntax, and very suboptimal preimage):

    #[program]
    Definition f = precomp (fun n => n-57) (fun n => [n .. n+57])) f'.
    Next Obligation.
      …
 *)
#[program]
Definition precomp {A1 A2 B} (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B) : T A1 (fun w => B (g w)) :=
  {|
    underlying := fun w => f (g w);
    support := List.flat_map preimg f.(support)
  |}.
Next Obligation.
  sauto lq: on rew: off use: Fun.precomp_support.
Qed.

#[program]
Definition map {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) : T A B2 :=
  {|
    underlying := Fun.map m f;
    support := f.(support);
  |}.
Next Obligation.
  hauto lq: on use: support_supports, Fun.map_support.
Qed.

Lemma map_spec0 : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (x : A), map m f x = Fun.map m f x.
Proof.
  trivial.
Qed.

Lemma map_In : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) x, In x f <-> In x (map m f).
Proof.
  intros *. unfold In, Fun.In.
  rewrite map_spec0.
  apply Fun.map_In.
Qed.

Lemma map_ext : forall {A B1 B2} (m1 m2 : forall x, B1 x -> B2 x) (f : T A B1) x,
    (forall x, m1 x = m2 x) -> map m1 f x = map m2 f x.
Proof.
  intros *. rewrite map_spec0.
  apply Fun.map_ext.
Qed.

Lemma map_Mapsto : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (x : A) (y : B2 x), map m f x = Some y <-> exists z, f x = Some z /\ y = m x z.
Proof.
  intros *.
  rewrite map_spec0.
  split.
- intros issome.
  unfold Fun.map in issome. destruct (f x) eqn:emap in issome.
  assert (m x b = y) as e. { injection issome; tauto. } rewrite <- e.
  exists b. tauto. congruence.
- intros [z [eq1 eq2]]. unfold Fun.map. destruct (f x) eqn:emap. assert (b = z) as e. { injection eq1; tauto. } subst. tauto. congruence.
Qed.

Lemma map_comp : forall {A B1 B2 B3} (m1 : forall x, B1 x -> B2 x) (m2 : forall x, B2 x -> B3 x) (f : T A B1) x, map m2 (map m1 f) x = map (fun x y => m2 x (m1 x y)) f x.
Proof.
  intros *. rewrite !map_spec0.
  apply Fun.map_comp.
Qed.

(* Not great: Q can never been inferred. But better than nothing. Easy case: map_propagate_forward'. *)
Lemma map_propagate_forward : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y1, f x = Some y1 -> Q x y1) -> (forall x y1, Q x y1 -> P x (m x y1)) -> forall x y2, map m f x = Some y2 -> P x y2.
Proof.
  intros * hf hm x y2. rewrite map_spec0.
  hfcrush use: Fun.map_propagate_forward.
Qed.

Lemma map_propagate_forward' : forall {A B} (m : forall x, B x -> B x) (f : T A B) (P : forall x, B x -> Prop),
    (forall x y1, f x = Some y1 -> P x y1) -> (forall x y1, P x y1 -> P x (m x y1)) -> forall x y2, map m f x = Some y2 -> P x y2.
Proof.
  intros *.
  apply map_propagate_forward.
Qed.

Lemma map_propagate_backward : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y2, map m f x = Some y2 -> P x y2) -> (forall x y1, P x (m x y1) -> Q x y1) -> (forall x y1, f x = Some y1 -> Q x y1).
Proof.
  intros * hmap hm x y1.
  eapply Fun.map_propagate_backward.
  all: hauto l: on use: map_spec0, Fun.map_propagate_backward.
Qed.

Lemma map_propagate_backward' : forall {A B} (m : forall x, B x -> B x) (f : T A B) (P : forall x, B x -> Prop),
    (forall x y2, map m f x = Some y2 -> P x y2) -> (forall x y1, P x (m x y1) -> P x y1) -> (forall x y1, f x = Some y1 -> P x y1).
Proof.
  intros *.
  apply map_propagate_backward.
Qed.

Lemma map_propagate_both : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y1, P x (m x y1) <-> Q x y1) -> (forall x y2, map m f x = Some y2 -> P x y2) <-> (forall x y1, f x = Some y1 -> Q x y1).
Proof.
  intros * hm.
  split.
  - intros h.
    rewrite <- Fun.map_propagate_both with (m:=m) (P:=P).
    all: hauto l: on use: map_spec0.
  - intros h *. rewrite map_spec0.
    hfcrush use: Fun.map_propagate_both.
Qed.

Lemma map_propagate_both' : forall {A B} (m : forall x, B x -> B x) (f : T A B) (P : forall x, B x -> Prop),
    (forall x y1, P x (m x y1) <-> P x y1) -> (forall x y2, map m f x = Some y2 -> P x y2) <-> (forall x y1, f x = Some y1 -> P x y1).
Proof.
  intros *.
  apply map_propagate_both.
Qed.

#[program]
Definition merge {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2) : T A B3 :=
  {|
    underlying := Fun.merge m f g;
    support := f.(support) ++ g.(support);
  |}.
Next Obligation.
  hauto lq: on use: support_supports, Fun.merge_support.
Qed.

Lemma merge_spec0 : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2),
    (merge m f g).(underlying) = Fun.merge m f g.
Proof.
  trivial.
Qed.

Lemma merge_spec1 : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2) (x:A),
    In x f \/ In x g -> merge m f g x = m x (f x) (g x).
Proof.
  intros *.
  rewrite merge_spec0.
  apply Fun.merge_spec1.
Qed.

Lemma merge_spec2 : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2) (x:A),
    In x (merge m f g) -> In x f \/ In x g.
Proof.
  intros *.
  rewrite In_spec, merge_spec0.
  apply Fun.merge_spec2.
Qed.

Definition merge_with {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) : T A B :=
  merge (Fun.merge_fun_of_with m) f g.

Lemma merge_with_spec0 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x : A), merge_with m f g x = Fun.merge_with m f g x.
Proof.
  trivial.
Qed.

Lemma merge_with_spec_1 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A) (y1 y2:B x),
    f x = Some y1 /\ g x = Some y2 -> merge_with m f g x = Some (m x y1 y2).
Proof.
  intros *.
  rewrite merge_with_spec0.
  apply Fun.merge_with_spec_1.
Qed.

Lemma merge_with_spec_2 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A) (y1:B x),
    f x = Some y1 /\ g x = None -> merge_with m f g x = Some y1.
Proof.
  intros *.
  rewrite merge_with_spec0.
  apply Fun.merge_with_spec_2.
Qed.

Lemma merge_with_spec_3 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A) (y2:B x),
    f x = None /\ g x = Some y2 -> merge_with m f g x = Some y2.
Proof.
  intros *.
  rewrite merge_with_spec0.
  apply Fun.merge_with_spec_3.
Qed.

Lemma merge_with_spec_4 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A),
    f x = None /\ g x = None -> merge_with m f g x = None.
Proof.
  intros *.
  rewrite merge_with_spec0.
  apply Fun.merge_with_spec_4.
Qed.

Lemma merge_with_spec_5 : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A),
    In x (merge_with m f g) <-> In x f \/ In x g.
Proof.
  intros *.
  rewrite !In_spec, merge_with_spec0.
  hauto lq: on use: Fun.merge_with_spec_5.
Qed.

Lemma merge_with_propagate_backward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x b1 b2, P x (m x b1 b2) -> P x b1 /\ P x b2) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h h0.
  assert (forall (x : A) (b : B x), Fun.merge_with m f g x = Some b -> P x b) as h0'.
  { sfirstorder use: merge_with_spec0. }
  apply Fun.merge_with_propagate_backward with (m:=m).
  all: sfirstorder.
Qed.

Lemma merge_with_propagate_backward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x b1 b2, ~P x (m x b1 b2)) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b)/\(forall x, In x f -> In x g -> False).
Proof.
  intros * h h0.
  assert (forall (x : A) (b : B x), Fun.merge_with m f g x = Some b -> P x b) as h0'.
  { sfirstorder use: merge_with_spec0. }
  apply Fun.merge_with_propagate_backward_disjoint with (m:=m).
  all: sfirstorder.
Qed.

Lemma merge_with_propagate_backward_disjoint' : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x, In x f -> In x g -> False) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h h0.
  assert (forall (x : A) (b : B x), Fun.merge_with m f g x = Some b -> P x b) as h0'.
  { sfirstorder use: merge_with_spec0. }
  apply Fun.merge_with_propagate_backward_disjoint' with (m:=m).
  all: sfirstorder.
Qed.

Lemma merge_with_propagate_forward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
     (forall x b1 b2, P x b1 /\ P x b2 -> P x (m x b1 b2)) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b.
  erewrite merge_with_spec0.
  sfirstorder use: Fun.merge_with_propagate_forward.
Qed.

Lemma merge_with_propagate_forward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x, In x f -> In x g -> False) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b.
  erewrite merge_with_spec0.
  sfirstorder use: Fun.merge_with_propagate_forward_disjoint.
Qed.

Lemma merge_with_propagate_both : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x b1 b2, P x (m x b1 b2) <-> P x b1 /\ P x b2) -> (forall x b, merge_with m f g x = Some b -> P x b) <-> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
  intros * h.
  split.
  - eapply merge_with_propagate_backward.
    sfirstorder.
  - intros [? ?].
    eapply merge_with_propagate_forward.
    all: sfirstorder.
Qed.

Lemma merge_with_propagate_both_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x b1 b2, ~P x (m x b1 b2)) -> (forall x b, merge_with m f g x = Some b -> P x b) <-> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b)/\(forall x, In x f -> In x g -> False).
Proof.
  intros * h.
  split.
  - hfcrush use: merge_with_propagate_backward_disjoint.
  - sfirstorder use: merge_with_propagate_forward_disjoint.
Qed.

Lemma merge_with_commutative' : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) x,
    (forall y1 y2, m x y1 y2 = m x y2 y1) -> merge_with m f g x = merge_with m g f x.
Proof.
  intros * h. rewrite merge_with_spec0.
  sfirstorder use: Fun.merge_with_commutative.
Qed.

Lemma merge_with_associative' : forall {A B} (m : forall x:A, B x -> B x -> B x) (f g h: T A B) x,
    (forall y1 y2 y3, m x y1 (m x y2 y3) = m x (m x y1 y2) y3) -> merge_with m f (merge_with m g h) x = merge_with m (merge_with m f g) h x.
Proof.
  intros * h. rewrite merge_with_spec0.
  sfirstorder use: Fun.merge_with_associative.
Qed.

Lemma merge_with_associative : forall {A B} (m : forall x:A, B x -> B x -> B x) (f g h: T A B),
    (forall x y1 y2 y3, m x y1 (m x y2 y3) = m x (m x y1 y2) y3) -> merge_with m f (merge_with m g h) = merge_with m (merge_with m f g) h.
Proof.
  intros * h.
  apply ext_eq.
  - sfirstorder use: merge_with_associative'.
  - sfirstorder use: app_assoc.
Qed.

(* This file introduces a type of dependent finite-domain partial
   functions. Basically, a dependent `MMAp`. This will serve as our
   contexts (which need to be dependent because we have two kind of
   binder names).

   We first introduce, in the `Fun` module a type of dependent partial
   functions (with decidable domain). And build our type `T` of finite
   functions ontop of it. The interface we provide is comparable to
   that of `MMap`, though tailored to the precise needs of our proots.

   For the sake of expediency, we do everything up to `eq`, which does
   mean introducing a few axioms. *)

Require List.
Require FMapList.
Require MSetList.
Require Import Psatz.
Require Import Coq.Structures.OrderedType.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.ClassicalEpsilon.

Set Primitive Projections.

(* This file contains the definition of our map type T that is used to represent typing contexts of destination calculus. *)
(* I (Arnaud Spiwack) am a little worried about changing our minds about
   details later. This is why I'm organising proofs in reference to a
   functional semantics. The interface to reprove will be smaller. *)

Module Fun.

  (* Note: this mirrors the design of MMaps. Except that we're
     ignoring everything about setoids since we won't be needing them
     for our use-case. *)

Definition In {A B} (x:A) (f:forall x:A, option (B x)) : Prop := exists y, f x = Some y.

Lemma In_iff_neq_None : forall {A B} (x:A) (f:forall x:A, option (B x)), In x f <-> f x <> None.
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

Lemma nIn_iff_nMapsTo : forall {A B} (x:A) (f:forall x:A, option (B x)), ~(In x f) <-> f x = None.
Proof.
  intros *.
  rewrite In_iff_neq_None.
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
  apply nIn_iff_nMapsTo.
  hauto lq: on use: In_supported.
Qed.

Lemma precomp_propagate_forward : forall {A1 A2 B} (g : A1 -> A2) (f : forall x:A2, option (B x)) (P : forall x, B x -> Prop),
    (forall x y, f x = Some y -> P x y) -> (forall x y, f (g x) = Some y -> P (g x) y).
Proof.
  intros * h **.
  apply h.
  trivial.
Qed.

Lemma precomp_propagate_backward : forall {A1 A2 B} (g : A1 -> A2) (f : forall x:A2, option (B x)) (P : forall x, B x -> Prop),
    (forall x2, exists x1, g x1 = x2) ->
    (forall x y, f (g x) = Some y -> P (g x) y) -> (forall x y, f x = Some y -> P x y).
Proof.
  intros * surj h x y.
  destruct (surj x) as [x' hx']. subst x.
  sfirstorder.
Qed.

Lemma precomp_propagate_both : forall {A1 A2 B} (g : A1 -> A2) (f : forall x:A2, option (B x)) (P : forall x, B x -> Prop),
    (forall x2, exists x1, g x1 = x2) ->
    (forall x y, f x = Some y -> P x y) <-> (forall x y, f (g x) = Some y -> P (g x) y).
Proof.
  intros * h.
  hfcrush use: precomp_propagate_forward, precomp_propagate_backward.
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

Lemma Support_singleton : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), Support (x :: nil) (singleton x discr v).
Proof.
  intros *. unfold Support, singleton. intros y w.
  hauto lq: on.
Qed.

Lemma In_singleton_iff : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A), In y (singleton x discr v) <-> y = x.
Proof.
  intros *. unfold In, singleton.
  hauto q: on.
Qed.

Lemma singleton_MapsTo_at_elt : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), singleton x discr v x = Some v.
Proof.
  intros *. unfold singleton.
  hauto dep: on.
Qed.

Lemma singleton_nMapsTo_iff : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) y, singleton x discr v y = None <-> x <> y.
Proof.
  intros *. unfold singleton.
  hauto dep: on.
Qed.

Lemma singleton_MapsTo_iff : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A) (v': B y), (singleton x discr v) y = Some v' <-> existT B x v = existT B y v'.
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

Lemma In_map_iff : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : forall x:A, option (B1 x)) x, In x (map m f) <-> In x f.
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

Lemma In_merge_forward : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) (x:A),
    In x f \/ In x g -> merge m f g x = m x (f x) (g x).
Proof.
  unfold merge.
  hauto lq: on.
Qed.

Lemma In_merge_backward : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) (x:A),
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

Lemma Support_merge : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : forall x:A, option (B1 x)) (g : forall x:A, option (B2 x)) lf lg, Support lf f -> Support lg g -> Support (lf ++ lg) (merge m f g).
Proof.
  intros * h_suppf h_suppg.
  apply In_supported. intros x h_in.
  qauto l: on use: In_supported, in_or_app, In_merge_backward.
Qed.


Definition on_conflict_do {A B} (m : forall x:A, B x -> B x -> B x) (x:A) (y1 : option (B x)) (y2 : option (B x)) : option (B x) :=
  match y1, y2 with
  | Some y1', Some y2' => Some (m x y1' y2')
  | Some y, None | None, Some y => Some y
  | None, None => None
  end.

(* A most common instance of merge. *)
Definition merge_with {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) : forall (x:A), option (B x) :=
  merge (on_conflict_do m) f g.

Lemma merge_with_Some_Some_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) (y1 y2:B x),
    f x = Some y1 /\ g x = Some y2 -> merge_with m f g x = Some (m x y1 y2).
Proof.
  unfold merge_with.
  hauto lq: on use: @In_merge_forward.
Qed.

Lemma merge_with_Some_None_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) (y1:B x),
    f x = Some y1 /\ g x = None -> merge_with m f g x = Some y1.
Proof.
  unfold merge_with.
  hauto lq: on use: @In_merge_forward.
Qed.

Lemma merge_with_None_Some_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) (y2:B x),
    f x = None /\ g x = Some y2 -> merge_with m f g x = Some y2.
Proof.
  unfold merge_with.
  hauto lq: on use: @In_merge_forward.
Qed.

Lemma merge_with_None_None_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A),
    f x = None /\ g x = None -> merge_with m f g x = None.
Proof.
  unfold merge_with, merge.
  hauto lq: on.
Qed.

Lemma In_merge_iff : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A),
    In x (merge_with m f g) <-> In x f \/ In x g.
Proof.
  split.
  - hauto lq: on use :@In_merge_backward.
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
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?nIn_iff_nMapsTo in *.
  - erewrite merge_with_Some_Some_eq in h0.
    2:{ eauto. }
    hecrush.
  - erewrite merge_with_Some_None_eq in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_None_Some_eq in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_None_None_eq in h0.
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
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?nIn_iff_nMapsTo in *.
  - erewrite merge_with_Some_Some_eq in h0.
    2:{ eauto. }
    hecrush.
  - erewrite merge_with_Some_None_eq in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_None_Some_eq in h0.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_None_None_eq in h0.
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
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?nIn_iff_nMapsTo in *.
  - sfirstorder.
  - erewrite merge_with_Some_None_eq in h.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_None_Some_eq in h.
    2: { eauto. }
    hecrush.
  - erewrite merge_with_None_None_eq in h.
    all: hfcrush.
Qed.

Lemma merge_with_propagate_forward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
     (forall x b1 b2, P x b1 /\ P x b2 -> P x (m x b1 b2)) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b h_merge.
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?nIn_iff_nMapsTo in *.
  - erewrite merge_with_Some_Some_eq in h_merge.
    2:{ eauto. }
    hauto l: on.
  - erewrite merge_with_Some_None_eq in h_merge.
    2:{ eauto. }
    hauto l: on.
  - erewrite merge_with_None_Some_eq in h_merge.
    2:{ eauto. }
    hauto l: on.
  - sblast use: merge_with_None_None_eq.
Qed.

Lemma merge_with_propagate_forward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)),
    (forall x, In x f -> In x g -> False) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b h_merge.
  destruct (In_dec x f) as [[bf h_inf]|h_ninf]; destruct (In_dec x g) as [[bg h_ing]|h_ning]. all: rewrite ?nIn_iff_nMapsTo in *.
  - hauto l: on.
  - erewrite merge_with_Some_None_eq in h_merge.
    2:{ eauto. }
    hauto l: on.
  - erewrite merge_with_None_Some_eq in h_merge.
    2:{ eauto. }
    hauto l: on.
  - hauto lq: on use: merge_with_None_None_eq.
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
  apply merge_commutative. unfold on_conflict_do.
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
    supported : exists l : list A, Fun.Support l underlying;
  }.
Arguments underlying {A B}.
Arguments supported {A B}.

(** Sometimes, rarely, ext_eq' is more useful than ext_eq. *)
Lemma ext_eq' : forall {A B} (f g : T A B), f.(underlying) = g.(underlying) ->f = g.
Proof.
  intros A B [f f_supp] [g g_supp] h_ext. cbn in *.
  subst g.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma ext_eq : forall {A B} (f g : T A B), (forall x, f x = g x) ->f = g.
Proof.
  intros * h_ext.
  apply ext_eq'.
  apply functional_extensionality_dep.
  assumption.
Qed.

Lemma support_ext_eq : forall A B (f g:T A B) (l:list A), Fun.Support l f -> Fun.Support l g -> (forall x, List.In x l -> f x = g x) -> f = g.
Proof.
  intros * h_supp_f h_supp_g h.
  apply ext_eq. intros x.
  destruct (f x) eqn: h_x'.
  - sfirstorder.
  - destruct (g x) eqn: h_x''.
    + sfirstorder.
    + trivial.
Qed.

Definition In {A B} (x : A) (f : T A B) : Prop := Fun.In x f.

Lemma In_iff_exists_Some : forall {A B} (x : A) (f : T A B), In x f <-> exists y, f x = Some y.
Proof.
  sfirstorder.
Qed.

Lemma In_iff_neq_None : forall {A B} (x:A) (f:T A B), In x f <-> f x <> None.
Proof.
  intros *.
  hauto lq: on unfold: In use: Fun.In_iff_neq_None.
Qed.

Lemma nIn_iff_nMapsTo : forall {A B} (x:A) (f: T A B), ~(In x f) <-> f x = None.
Proof.
  intros *.
  hauto lq: on unfold: In use: Fun.nIn_iff_nMapsTo.
Qed.

Lemma In_dec :  forall {A B} (x : A) (f : T A B), In x f \/ ~In x f.
Proof.
  intros *. rewrite !In_iff_exists_Some.
  destruct (f x) as [y|].
  all:sfirstorder.
Qed.

(** An arbitrary support, not really meant to be used outside of this
    module: use `dom` instead. *)
#[program]
Definition a_support {A B} (f : T A B) : list A := constructive_indefinite_description _ f.(supported).

Lemma a_support_supports : forall {A B} (f : T A B), Fun.Support (a_support f) f.
Proof.
  intros *. unfold a_support.
  apply proj2_sig.
Qed.

Definition dom {A B} (f : T A B) : list A :=
  List.nodup (fun x y => excluded_middle_informative _) (List.filter (fun x => match f x with Some _ => true | None => false end) (a_support f)).

Lemma dom_spec : forall {A B} (f : T A B) (x : A), List.In x (dom f) <-> In x f.
Proof.
  intros *. unfold dom. rewrite nodup_In.
  split.
  - rewrite filter_In.
    hauto l: on.
  - rewrite filter_In.
    rewrite <- (Fun.In_supported_r f).
    + sauto.
    + apply a_support_supports.
Qed.

Lemma NoDup_dom : forall {A B} (f : T A B), NoDup (dom f).
Proof.
  intros *. unfold dom.
  apply NoDup_nodup.
Qed.

Lemma Support_dom : forall {A B} (f : T A B), Fun.Support (dom f) f.
Proof.
  intros *.
  rewrite Fun.In_supported.
  hauto lq: on use: dom_spec.
Qed.

#[program]
Definition empty {A B} : T A B :=
  {|
    underlying := fun _ => None;
  |}.
Next Obligation.
  exists nil.
  scongruence.
Qed.

(* Maybe this lemma is somewhere in the standard library. I couldn't find it.
   `in_nil: forall [A : Type] [a : A], ~ List.In a nil` is the converse. *)
Lemma forall_NotIn_eq_nil : forall A (l : list A), (forall x, ~List.In x l) -> l = nil.
Proof.
  induction l.
  - congruence.
  - intros h. specialize (h a).
    contradict h.
    apply in_eq.
Qed.

Lemma dom_empty_eq_nil : forall {A B}, dom (@empty A B) = nil.
Proof.
  intros *. unfold empty.
  apply forall_NotIn_eq_nil. intros x.
  rewrite dom_spec, In_iff_exists_Some. cbn.
  sfirstorder.
Qed.

Lemma Support_nil_is_empty : forall A B (f : T A B), Fun.Support nil f -> f = empty.
Proof.
  intros * h. unfold Fun.Support in h.
  apply ext_eq. intros x. cbn.
  specialize (h x).
  destruct (f x) as [y|].
  - specialize (h y).
    sfirstorder use: in_nil.
  - reflexivity.
Qed.

Corollary dom_nil_is_empty : forall A B (f : T A B), dom f = nil -> f = empty.
Proof.
  intros * h.
  apply Support_nil_is_empty.
  rewrite <- h.
  apply Support_dom.
Qed.

#[program]
Definition singleton {A B} (x : A) (discr : forall x y, {x = y} + {x<>y}) (v : B x) : T A B :=
  {|
    underlying := Fun.singleton x discr v;
  |}.
Next Obligation.
  exists (x::nil).
  hauto lq: on use: Fun.Support_singleton.
Qed.

Lemma singleton_spec : forall {A B} (x : A) (discr : forall x y, {x = y} + {x<>y}) (v : B x) (y : A),
    singleton x discr v y = Fun.singleton x discr v y.
Proof.
  intros *.
  sfirstorder.
Qed.

Lemma In_singleton_iff : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A), In y (singleton x discr v) <-> y = x.
Proof.
  intros *.
  hauto lq: on use: In_iff_exists_Some, singleton_spec, Fun.In_singleton_iff.
Qed.

Lemma singleton_MapsTo_iff : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) (y : A) (v': B y), (singleton x discr v) y = Some v' <-> existT B x v = existT B y v'.
Proof.
  intros *. rewrite singleton_spec. apply Fun.singleton_MapsTo_iff.
Qed.

Lemma dom_singleton_eq : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), dom (singleton x discr v) = x::nil.
Proof.
  intros *.
  assert (forall l, NoDup l -> List.In x l -> (forall y, List.In y l -> x = y) -> l = x::nil) as in_list_singleton.
  { destruct 1 as [|y l h_nin h_nodup].
    - sfirstorder.
    - intros _ h.
      (* Nice that CoqHammer solves this one because otherwise, it's a
         pretty finicky proof for no reason. *)
      hfcrush use: forall_NotIn_eq_nil. }
  apply in_list_singleton.
  - apply NoDup_dom.
  - apply dom_spec. rewrite In_singleton_iff. reflexivity.
  - intros y. rewrite dom_spec, In_singleton_iff. congruence.
Qed.

Lemma singleton_MapsTo_at_elt : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x), singleton x discr v x = Some v.
Proof.
  intros *. rewrite singleton_spec.
 apply Fun.singleton_MapsTo_at_elt.
Qed.

Lemma singleton_nMapsTo_iff : forall {A B} (x : A) (discr : forall x y, {x = y} + {~x=y}) (v : B x) y, singleton x discr v y = None <-> x <> y.
Proof.
  intros *. rewrite singleton_spec.
  apply Fun.singleton_nMapsTo_iff.
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
  |}.
Next Obligation.
  exists (List.flat_map preimg (dom f)).
  sauto lq: on rew: off use: Fun.precomp_support, Support_dom.
Qed.

Lemma precomp_spec : forall {A1 A2 B} (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B),
    (precomp g preimg f).(underlying) = fun x => f (g x).
Proof.
  intros *.
  reflexivity.
Qed.

Lemma In_precomp_iff : forall {A1 A2 B} (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B) x,
    In x (precomp g preimg f) <-> In (g x) f.
Proof.
  intros *. rewrite !In_iff_exists_Some.
  unfold precomp. cbn.
  reflexivity.
Qed.

Lemma precomp_propagate_forward : forall {A1 A2 B} (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B) (P : forall x, B x -> Prop),
    (forall x y, f x = Some y -> P x y) -> (forall x y, precomp g preimg f x = Some y -> P (g x) y).
Proof.
  intros * h **.
  rewrite precomp_spec in *.
  sfirstorder use: Fun.precomp_propagate_forward.
Qed.

Lemma precomp_propagate_backward : forall {A1 A2 B} (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B) (P : forall x, B x -> Prop),
    (forall x2, exists x1, g x1 = x2) ->
    (forall x y, precomp g preimg f x = Some y -> P (g x) y) -> (forall x y, f x = Some y -> P x y).
Proof.
  intros *.
  rewrite precomp_spec in *.
  hfcrush use: Fun.precomp_propagate_forward.
Qed.

Lemma precomp_propagate_both : forall {A1 A2 B} (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B) (P : forall x, B x -> Prop),
    (forall x2, exists x1, g x1 = x2) ->
    (forall x y, f x = Some y -> P x y) <-> (forall x y, precomp g preimg f x = Some y -> P (g x) y).
Proof.
  intros * h.
  hfcrush use: precomp_propagate_forward, precomp_propagate_backward.
Qed.

#[program]
Definition map {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) : T A B2 :=
  {|
    underlying := Fun.map m f;
  |}.
Next Obligation.
  exists (dom f).
  hauto lq: on use: Support_dom, Fun.map_support.
Qed.

Lemma map_spec : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (x : A), map m f x = Fun.map m f x.
Proof.
  trivial.
Qed.

Lemma In_map_iff : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) x, In x (map m f) <-> In x f.
Proof.
  intros *. unfold In, Fun.In.
  rewrite map_spec.
  apply Fun.In_map_iff.
Qed.

Lemma map_ext : forall {A B1 B2} (m1 m2 : forall x, B1 x -> B2 x) (f : T A B1) x,
    (forall x, m1 x = m2 x) -> map m1 f x = map m2 f x.
Proof.
  intros *. rewrite map_spec.
  apply Fun.map_ext.
Qed.

Lemma map_MapsTo_iff : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (x : A) (y : B2 x), map m f x = Some y <-> exists z, f x = Some z /\ y = m x z.
Proof.
  intros *.
  rewrite map_spec.
  split.
- intros issome.
  unfold Fun.map in issome. destruct (f x) eqn:emap in issome.
  assert (m x b = y) as e. { injection issome; tauto. } rewrite <- e.
  exists b. tauto. congruence.
- intros [z [eq1 eq2]]. unfold Fun.map. destruct (f x) eqn:emap. assert (b = z) as e. { injection eq1; tauto. } subst. tauto. congruence.
Qed.

Lemma map_MapsTo_if : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (x : A) (y : B1 x), f x = Some y -> map m f x = Some (m x y).
Proof.
  intros *.
  rewrite map_spec.
  unfold Fun.map.
  destruct (f x); intro H; inversion H; trivial.
Qed.

Lemma map_nMapsTo_iff : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (x : A), map m f x = None <-> f x = None.
Proof.
  intros *.
  rewrite map_spec.
  split.
- intros isnone.
  unfold Fun.map in isnone. destruct (f x) eqn:emap in isnone. congruence. tauto.
- intros isnone. unfold Fun.map. rewrite isnone. tauto.
Qed.

Lemma map_comp : forall {A B1 B2 B3} (m1 : forall x, B1 x -> B2 x) (m2 : forall x, B2 x -> B3 x) (f : T A B1) x, map m2 (map m1 f) x = map (fun x y => m2 x (m1 x y)) f x.
Proof.
  intros *. rewrite !map_spec.
  apply Fun.map_comp.
Qed.

Lemma map_precomp : forall {A1 A2 B1 B2} (m : forall x, B1 x -> B2 x)  (g : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, g w = x -> List.In w (p x)}) (f : T A2 B1),
    map (fun x => m (g x)) (precomp g preimg f) = precomp g preimg (map m f).
Proof.
  intros *. apply ext_eq. intros x. cbn. unfold Fun.map.
  reflexivity.
Qed.

(* Not great: Q can never been inferred. But better than nothing. Easy case: map_propagate_forward'. *)
Lemma map_propagate_forward : forall {A B1 B2} (m : forall x, B1 x -> B2 x) (f : T A B1) (P : forall x, B2 x -> Prop) (Q : forall x, B1 x -> Prop),
    (forall x y1, f x = Some y1 -> Q x y1) -> (forall x y1, Q x y1 -> P x (m x y1)) -> forall x y2, map m f x = Some y2 -> P x y2.
Proof.
  intros * hf hm x y2. rewrite map_spec.
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
  all: hauto l: on use: map_spec, Fun.map_propagate_backward.
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
    all: hauto l: on use: map_spec.
  - intros h *. rewrite map_spec.
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
  |}.
Next Obligation.
  exists (dom f ++ dom g).
  apply Fun.Support_merge.
  all: apply Support_dom.
Qed.

Lemma merge_spec : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2),
    (merge m f g).(underlying) = Fun.merge m f g.
Proof.
  trivial.
Qed.

Lemma In_merge_forward : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2) (x:A),
    In x f \/ In x g -> merge m f g x = m x (f x) (g x).
Proof.
  intros *.
  rewrite merge_spec.
  apply Fun.In_merge_forward.
Qed.

Lemma In_merge_backward : forall {A B1 B2 B3} (m : forall x:A, option (B1 x) -> option (B2 x) -> option (B3 x)) (f : T A B1) (g : T A B2) (x:A),
    In x (merge m f g) -> In x f \/ In x g.
Proof.
  intros *.
  rewrite In_iff_exists_Some, merge_spec.
  apply Fun.In_merge_backward.
Qed.

Definition merge_with {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) : T A B :=
  merge (Fun.on_conflict_do m) f g.

Lemma merge_with_spec : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x : A), merge_with m f g x = Fun.merge_with m f g x.
Proof.
  trivial.
Qed.

Lemma merge_with_Some_Some_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A) (y1 y2:B x),
    f x = Some y1 /\ g x = Some y2 -> merge_with m f g x = Some (m x y1 y2).
Proof.
  intros *.
  rewrite merge_with_spec.
  apply Fun.merge_with_Some_Some_eq.
Qed.

Lemma merge_with_Some_None_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A) (y1:B x),
    f x = Some y1 /\ g x = None -> merge_with m f g x = Some y1.
Proof.
  intros *.
  rewrite merge_with_spec.
  apply Fun.merge_with_Some_None_eq.
Qed.

Lemma merge_with_None_Some_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A) (y2:B x),
    f x = None /\ g x = Some y2 -> merge_with m f g x = Some y2.
Proof.
  intros *.
  rewrite merge_with_spec.
  apply Fun.merge_with_None_Some_eq.
Qed.

Lemma merge_with_None_None_eq : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A),
    f x = None /\ g x = None -> merge_with m f g x = None.
Proof.
  intros *.
  rewrite merge_with_spec.
  apply Fun.merge_with_None_None_eq.
Qed.

Lemma In_merge_iff : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B) (x:A),
    In x (merge_with m f g) <-> In x f \/ In x g.
Proof.
  intros *.
  rewrite !In_iff_exists_Some, merge_with_spec.
  hauto lq: on use: Fun.In_merge_iff.
Qed.

Lemma merge_with_precomp : forall {A1 A2 B} (m : forall x:A2, B x -> B x -> B x) (f : T A2 B) (g : T A2 B) (h : A1 -> A2) (preimg : { p : A2 -> list A1 | forall x w, h w = x -> List.In w (p x)}),
    merge_with (fun x => m (h x)) (precomp h preimg f) (precomp h preimg g) = precomp h preimg (merge_with m f g).
Proof.
  intros *. apply ext_eq. cbn. intros x. unfold Fun.merge. cbn.
  reflexivity.
Qed.

Lemma merge_with_map : forall {A B1 B2} (m : forall x:A, B2 x -> B2 x -> B2 x) (m' : forall x, B1 x -> B2 x) (f : T A B1) (g : T A B1),
    merge_with m (map m' f) (map m' g) = merge (fun x oy1 oy2 => match oy1, oy2 with
                                                              | Some y1, Some y2 => Some (m x (m' x y1) (m' x y2))
                                                              | Some y, None | None, Some y => Some (m' x y)
                                                              | None, None => None
                                                              end) f g.
Proof.
  intros *. apply ext_eq. cbn. intros x. unfold Fun.merge, Fun.map. cbn.
  hauto lq: on.
Qed.

Lemma merge_with_propagate_backward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x b1 b2, P x (m x b1 b2) -> P x b1 /\ P x b2) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h h0.
  assert (forall (x : A) (b : B x), Fun.merge_with m f g x = Some b -> P x b) as h0'.
  { sfirstorder use: merge_with_spec. }
  apply Fun.merge_with_propagate_backward with (m:=m).
  all: sfirstorder.
Qed.

Lemma merge_with_propagate_backward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x b1 b2, ~P x (m x b1 b2)) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b)/\(forall x, In x f -> In x g -> False).
Proof.
  intros * h h0.
  assert (forall (x : A) (b : B x), Fun.merge_with m f g x = Some b -> P x b) as h0'.
  { sfirstorder use: merge_with_spec. }
  apply Fun.merge_with_propagate_backward_disjoint with (m:=m).
  all: sfirstorder.
Qed.

Lemma merge_with_propagate_backward_disjoint' : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x, In x f -> In x g -> False) -> (forall x b, merge_with m f g x = Some b -> P x b) -> (forall x b, f x = Some b -> P x b)/\(forall x b, g x = Some b -> P x b).
Proof.
  intros * h h0.
  assert (forall (x : A) (b : B x), Fun.merge_with m f g x = Some b -> P x b) as h0'.
  { sfirstorder use: merge_with_spec. }
  apply Fun.merge_with_propagate_backward_disjoint' with (m:=m).
  all: sfirstorder.
Qed.

Lemma merge_with_propagate_forward : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
     (forall x b1 b2, P x b1 /\ P x b2 -> P x (m x b1 b2)) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b.
  erewrite merge_with_spec.
  sfirstorder use: Fun.merge_with_propagate_forward.
Qed.

Lemma merge_with_propagate_forward_disjoint : forall {A B} (P : forall x, B x -> Prop) (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x, In x f -> In x g -> False) -> (forall x b, f x = Some b -> P x b) -> (forall x b, g x = Some b -> P x b) -> (forall x b, merge_with m f g x = Some b -> P x b).
Proof.
  intros * h h1 h2 x b.
  erewrite merge_with_spec.
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
  intros * h. rewrite merge_with_spec.
  sfirstorder use: Fun.merge_with_commutative.
Qed.

Lemma merge_with_commutative : forall {A B} (m : forall x:A, B x -> B x -> B x) (f : T A B) (g : T A B),
    (forall x y1 y2, m x y1 y2 = m x y2 y1) -> merge_with m f g = merge_with m g f.
Proof.
  intros * h.
  apply ext_eq.
  sfirstorder use: merge_with_commutative'.
Qed.

Lemma merge_with_associative' : forall {A B} (m : forall x:A, B x -> B x -> B x) (f g h: T A B) x,
    (forall y1 y2 y3, m x y1 (m x y2 y3) = m x (m x y1 y2) y3) -> merge_with m f (merge_with m g h) x = merge_with m (merge_with m f g) h x.
Proof.
  intros * h. rewrite merge_with_spec.
  sfirstorder use: Fun.merge_with_associative.
Qed.

Lemma merge_with_associative : forall {A B} (m : forall x:A, B x -> B x -> B x) (f g h: T A B),
    (forall x y1 y2 y3, m x y1 (m x y2 y3) = m x (m x y1 y2) y3) -> merge_with m f (merge_with m g h) = merge_with m (merge_with m f g) h.
Proof.
  intros * h.
  apply ext_eq.
  sfirstorder use: merge_with_associative'.
Qed.

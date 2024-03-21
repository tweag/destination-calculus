Require List.
Require FMapList.
Require MSetList.
Require Import Psatz.
Require Import Coq.Structures.OrderedType.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
From SMTCoq Require Import SMTCoq.
Require MMaps.OrdList.

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

(* In a plan I had at some point, this notion was relevant. I don't
   know that I still need it. *)
Definition Support {A B} (l : list A) (f : forall x:A, option (B x)) : Prop :=
  forall x:A, ~List.In x l -> f x = None.

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

Definition merge_fun_of_with {A B} (m : forall x:A, B x -> B x -> B x) (x:A) (y1 : option (B x)) (y2 : option (B x)) : option (B x) :=
  match y1, y2 with
  | Some y1', Some y2' => Some (m x y1' y2')
  | Some y, None | None, Some y => Some y
  | None, None => None
  end.

(* A most common instance of merge. *)
Definition merge_with {A B} (m : forall x:A, B x -> B x -> B x) (f : forall x:A, option (B x)) (g : forall x:A, option (B x)) (x:A) : option (B x) :=
  merge (merge_fun_of_with m) f g x.

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
    In x (merge_with m f g) <-> In x f \/ In x g.
Proof.
  split.
  - hauto lq: on use :@merge_spec2.
  - unfold merge_with, merge, In.
    hauto.
Qed.

End Fun.

Module Map.
  Include MMaps.OrdList.Make(PeanoNat.Nat).

  Lemma In_spec_fun : forall {elt} (m : t elt) x, In x m <-> Fun.In x (fun x => find x m).
  Proof.
    sauto use: @find_spec.
  Qed.

  Lemma find_not_In_None : forall {elt} (m:t elt) x,
      ~(In x m) <-> find x m = None.
  Proof.
    intros *.
    hauto l: on use: In_spec_fun, Fun.In_None2.
  Qed.

  (** useful with the rewrite tactic. *)
  Lemma find_not_In_None' : forall {elt} (m:t elt) x,
      ~(In x m) -> find x m = None.
  Proof.
    intros *.
    apply find_not_In_None.
  Qed.

  Lemma merge_spec_fun : forall {elt elt' elt''} (f:key->option elt->option elt'->option elt'') m m' x,
      find x (merge f m m') = Fun.merge f (fun x => find x m) (fun x => find x m') x.
  Proof.
    intros *.
    assert (forall {elt'''} (m'' : t elt'''), In x m'' \/ ~(In x m'')) as h.
    { intros *.
      generalize (find_spec m'' x); intros h.
      destruct (find x m'') as [y|].
      - left. exists y.
        apply h.
        reflexivity.
      - right.
        sfirstorder.
    }
    destruct (h _ m) as [h_in_m|h_in_m].
    {
      rewrite Fun.merge_spec1.
      2:{ sauto use: @In_spec_fun. }
      generalize (@merge_spec1 _ _ _ f m m' x); intros h'.
      destruct h' as [y [-> h']].
      { tauto. }
      auto.
    }
    destruct (h _ m') as [h_in_m'|h_in_m'].
    {
      rewrite Fun.merge_spec1.
      2:{ sauto use: @In_spec_fun. }
      generalize (@merge_spec1 _ _ _ f m m' x); intros h'.
      destruct h' as [y [-> h']].
      { tauto. }
      auto.
    }
    rewrite find_not_In_None'.
    2:{ hauto use: merge_spec2. }
    unfold Fun.merge.
    rewrite !find_not_In_None'.
    all: trivial.
  Qed.

End Map.

(* I [aspiwack] have no good idea for a name, so CoBinder it'll be. *)
Record CoBinderT (A : Type) := {
    vart : A;
    plust : A;
    negt : A;
  }.
Arguments vart {A}.
Arguments plust {A}.
Arguments negt {A}.

(* TODO: namespace the CoBinder functions. They will otherwise
   interfere with the normal definitions. *)

Definition pure {A:Type} (x:A) : CoBinderT A := {|
    vart := x;
    plust := x;
    negt := x;
  |}.

Definition ap {A B:Type} (f:CoBinderT (A -> B)) (x:CoBinderT A) : CoBinderT B := {|
    vart := f.(vart) x.(vart);
    plust := f.(plust) x.(plust);
    negt := f.(negt) x.(negt);
  |}.

Notation "f '<*>' x" := (ap f x) (at level 10, left associativity).

Definition map {A B:Type} (f:A -> B) (x:CoBinderT A) : CoBinderT B
  := pure f <*> x.

Notation "f '<$>' x" := (map f x) (at level 10, left associativity).

Definition domain : CoBinderT Type := pure (nat : Type). (* Some universe polymorphism stuff going on *)

Record CoBinder (r : CoBinderT Type) := {
    var : r.(vart);
    plus : r.(plust);
    neg : r.(negt);
  }.
Arguments var {r}.
Arguments plus {r}.
Arguments neg {r}.


Variant Binder :=
  | Var : domain.(vart) -> Binder
  | Plus : domain.(plust) -> Binder
  | Neg : domain.(negt) -> Binder
.

(* We don't have to make the return type generic, but it's likely to
   simplify proofs. And it may come in handy later. *)
Definition CtxM (r : CoBinderT Type) : Type := CoBinder (map Map.t r).

Definition CtxRangeType (r : CoBinderT Type) (v : Binder) : Type :=
  match v with
  | Var _ => r.(vart)
  | Plus _ => r.(plust)
  | Neg _ => r.(negt)
  end.

Definition find {r : CoBinderT Type} (v : Binder) (m : CtxM r) : option (CtxRangeType r v) :=
  match v with
  | Var n => Map.find n m.(var)
  | Plus n => Map.find n m.(plus)
  | Neg n => Map.find n m.(neg)
  end.

Definition merge {r1 r2 r3 : CoBinderT Type}
  (fs : CoBinder ((fun v t1 t2 t3 => v -> option t1 -> option t2 -> option t3) <$> domain <*> r1 <*> r2 <*> r3)) (m1 : CtxM r1) (m2 : CtxM r2) : CtxM r3 :=
    {|
      var := (Map.merge fs.(var) m1.(var) m2.(var) : (map Map.t r3).(vart));
      plus := Map.merge fs.(plus) m1.(plus) m2.(plus);
      neg := Map.merge fs.(neg) m1.(neg) m2.(neg);
    |}.

Definition merge_function {r1 r2 r3 : CoBinderT Type} (fs : CoBinder ((fun v t1 t2 t3 => v -> option t1 -> option t2 -> option t3) <$> domain <*> r1 <*> r2 <*> r3)) (v : Binder) : option (CtxRangeType r1 v) -> option (CtxRangeType r2 v) -> option (CtxRangeType r3 v) :=
  match v with
  | Var n => fs.(var) n
  | Plus n => fs.(plus) n
  | Neg n => fs.(neg) n
  end.

Lemma merge_spec_fun : forall {r1 r2 r3 : CoBinderT Type} (fs : CoBinder ((fun v t1 t2 t3 => v -> option t1 -> option t2 -> option t3) <$> domain <*> r1 <*> r2 <*> r3)) (m1 : CtxM r1) (m2 : CtxM r2) (x : Binder),
      find x (merge fs m1 m2) = Fun.merge (merge_function fs) (fun x => find x m1) (fun x => find x m2) x.
Proof.
  intros *. unfold Fun.merge, find.
  destruct x as [n|n|n].
  all: simpl.
  all: rewrite Map.merge_spec_fun; unfold Fun.merge.
  all: trivial.
Qed.

Definition merge_with {r} (fs : CoBinder ((fun t => t -> t -> t) <$> r)) (m1 : CtxM r) (m2 : CtxM r) : CtxM r :=

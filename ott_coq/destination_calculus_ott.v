(* generated by Ott 0.33 from: rules.ott grammar.ott *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Ott.ott_list_core.


Require Import Ott.ext_nat.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetFacts.

Inductive name : Type :=
  | name_X : nat -> name
  | name_HD : nat -> name.

Module Name_as_UDT <: UsualDecidableType.
  Definition t := name.

  Definition eq := @eq name.
  Definition eq_refl := @eq_refl name.
  Definition eq_sym := @eq_sym name.
  Definition eq_trans := @eq_trans name.

  (* Define the eq_dec function *)
  Theorem eq_dec : forall x y : name, {x = y} + {x <> y}.
  Proof.
    intros x y. decide equality. apply Nat.eq_dec. apply Nat.eq_dec.
  Defined.

  Instance eq_equiv : Equivalence Name_as_UDT.eq. split. exact eq_refl. exact eq_sym. exact eq_trans. Defined.

End Name_as_UDT.

Module Nat_as_UDTOrig := Backport_DT(Nat_as_OT).
Module HdnsM := FSetWeakList.Make(Nat_as_UDTOrig).
Module Name_as_UDTOrig := Backport_DT(Name_as_UDT).
Module CtxM := FMapWeakList.Make(Name_as_UDTOrig).

(* We need to predefine eq_dec for mode so that Ott can generate eq_dec for type *)

(* Will be aliased later to mul *)
Inductive _mul : Type :=
  | Lin : _mul
  | Ur : _mul.
Theorem mul_eq_dec : forall (p1 p2: _mul), {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.
Definition age_eq_dec : forall (a1 a2: ext_nat), {a1 = a2} + {a1 <> a2} := ext_eq_dec.
Theorem mode_eq_dec : forall (m1 m2: option (_mul * ext_nat)), {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality. destruct a, p.
  - destruct (mul_eq_dec _m _m0), (age_eq_dec e e0); subst; auto.
    * right. congruence.
    * right. congruence.
    * right. congruence.
Defined.

Definition var : Type := nat. (*r Term-level variable name *)
Definition k : Type := nat. (*r Index for ranges *)

Definition hdn : Type := nat.

Definition age : Type := ext_nat.

Definition mul : Type := _mul.

Definition hdns : Type := HdnsM.t.

Definition mode : Type := option (mul * age).

Inductive term : Type :=  (*r Term *)
 | term_Val (v:val) (*r Value *)
 | term_Var (x:var) (*r Variable *)
 | term_App (t:term) (u:term) (*r Application *)
 | term_PatU (t:term) (u:term) (*r Pattern-match on unit *)
 | term_PatS (t:term) (m:mode) (x1:var) (u1:term) (x2:var) (u2:term) (*r Pattern-match on sum *)
 | term_PatP (t:term) (m:mode) (x1:var) (x2:var) (u:term) (*r Pattern-match on product *)
 | term_PatE (t:term) (m:mode) (n:mode) (x:var) (u:term) (*r Pattern-match on exponential *)
 | term_Map (t:term) (x:var) (u:term) (*r Map over the right side of ampar $(t:term)$ *)
 | term_ToA (t:term) (*r Wrap $(t:term)$ into a trivial ampar *)
 | term_FromA (t:term) (*r Extract value from trivial ampar *)
 | term_Alloc : term (*r Return a fresh "identity" ampar object *)
 | term_FillU (t:term) (*r Fill destination with unit *)
 | term_FillF (t:term) (x:var) (m:mode) (u:term) (*r Fill destination with function *)
 | term_FillL (t:term) (*r Fill destination with left variant *)
 | term_FillR (t:term) (*r Fill destination with right variant *)
 | term_FillP (t:term) (*r Fill destination with product constructor *)
 | term_FillE (t:term) (m:mode) (*r Fill destination with exponential constructor *)
 | term_FillC (t:term) (u:term) (*r Fill destination with root of ampar $(u:term)$ *)
with val : Type :=  (*r Term value *)
 | val_H (h:hdn) (*r Hole *)
 | val_D (h:hdn) (*r Destination *)
 | val_U : val (*r Unit *)
 | val_F (x:var) (m:mode) (t:term) (*r Lambda abstraction *)
 | val_L (v:val) (*r Left variant for sum *)
 | val_R (v:val) (*r Right variant for sum *)
 | val_E (m:mode) (v:val) (*r Exponential *)
 | val_P (v1:val) (v2:val) (*r Product *)
 | val_A (H:hdns) (v1:val) (v2:val) (*r Ampar *).

Inductive type : Type :=  (*r Type *)
 | type_U : type (*r Unit *)
 | type_S (T1:type) (T2:type) (*r Sum *)
 | type_P (T1:type) (T2:type) (*r Product *)
 | type_E (m:mode) (T:type) (*r Exponential *)
 | type_A (T1:type) (T2:type) (*r Ampar type (consuming $(T2:type)$ yields $(T1:type)$) *)
 | type_F (T1:type) (m1:mode) (T2:type) (*r Function *)
 | type_D (T:type) (m:mode) (*r Destination *)
 | type_C (T1:type) (T2:type) (*r Evaluation contexts *).

Inductive ectx : Type :=  (*r Evaluation context *)
 | ectx_Id : ectx (*r Identity *)
 | ectx_AOpen (H:hdns) (v1:val) (C:ectx) (*r Open ampar *)
 | ectx_Comp (C:ectx) (C':ectx) (*r Compose evaluation contexts *).

Inductive bndr : Type :=  (*r Type assignment to either variable, destination or hole *)
 | bndr_V (x:var) (m:mode) (T:type) (*r Variable *)
 | bndr_D (h:hdn) (m:mode) (T:type) (n:mode) (*r Destination ($(m:mode)$ is its own modality; $(n:mode)$ is the modality for values it accepts) *)
 | bndr_H (h:hdn) (T:type) (n:mode) (*r Hole ($(n:mode)$ is the modality for values it accepts, it doesn't have a modality on its own) *).

Inductive eterm : Type :=  (*r Pseudo-term *)
 | eterm_ECtxApp (C:ectx) (t:term).

Definition ctx : Type := (CtxM.t bndr).
Lemma eq_type: forall (x y : type), {x = y} + {x <> y}.
Proof.
decide equality. apply mode_eq_dec. apply mode_eq_dec. apply mode_eq_dec.
Defined.
Hint Resolve eq_type : ott_coq_equality.
(******************************************************************************
 * NAMES
 *****************************************************************************)

Definition name_eq_dec := Name_as_UDT.eq_dec.

Fixpoint hdns_from_list (l : list nat) : HdnsM.t :=
  match l with
  | nil => HdnsM.empty
  | h :: t => HdnsM.add h (hdns_from_list t)
  end.

Definition hdns_max_hnames (H : HdnsM.t) : nat :=
  HdnsM.fold (fun k acc => max k acc) H 0.

Definition hdns_incr_hnames (H : HdnsM.t) (h' : nat) : HdnsM.t :=
  HdnsM.fold (fun h acc => HdnsM.add (h + h') acc) H HdnsM.empty.

Definition hdns_from_ctx (G : CtxM.t bndr) : HdnsM.t :=
  CtxM.fold (fun n b acc =>
    match b with
    | bndr_H h _ _ => HdnsM.add h acc
    | _ => acc
    end
  ) G HdnsM.empty.

(* TODO: check definition *)
Fixpoint hdns_from_ectx (C : ectx) : HdnsM.t :=
  match C with
  | ectx_Id => HdnsM.empty
  | ectx_AOpen H v C' => HdnsM.union H (hdns_from_ectx C')
  | ectx_Comp C1 C2 => HdnsM.union (hdns_from_ectx C1) (hdns_from_ectx C2)
  end.

(******************************************************************************
 * TERMS DYNAMIC BEHAVIOUR
 *****************************************************************************)

Fixpoint term_sub_name (t: term) (n : name) (v : val) : term := match t with
  | term_Val v' => term_Val (val_sub_name v' n v)
  | term_Var y => match name_eq_dec n (name_X y) with
    | left _ => term_Val v
    | right _ => term_Var y
    end
  | term_App t1 t2 => term_App (term_sub_name t1 n v) (term_sub_name t2 n v)
  | term_PatU t1 t2 => term_PatU (term_sub_name t1 n v) (term_sub_name t2 n v)
  | term_PatS t' m x1 u1 x2 u2 =>
    let u1' := match name_eq_dec n (name_X x1) with
      | left _ => (* shadowing *) u1
      | right _ => term_sub_name u1 n v
    end in
    let u2' := match name_eq_dec n (name_X x2) with
      | left _ => (* shadowing *) u2
      | right _ => term_sub_name u2 n v
    end in term_PatS (term_sub_name t' n v) m x1 u1' x2 u2'
  | term_PatP t' m x1 x2 u => match name_eq_dec n (name_X x1), name_eq_dec n (name_X x2) with
    | right _, right _ => term_PatP (term_sub_name t' n v) m x1 x2 (term_sub_name u n v)
    | _, _ => (* at least one shadowing *) term_PatP (term_sub_name t' n v) m x1 x2 u
    end
  | term_PatE t' m m' x' u => let u' := match name_eq_dec n (name_X x') with
      | left _ => (* shadowing *) u
      | right _ => term_sub_name u n v
    end in term_PatE (term_sub_name t' n v) m m' x' u'
  | term_Map t' x' u => let u' := match name_eq_dec n (name_X x') with
      | left _ => (* shadowing *) u
      | right _ => term_sub_name u n v
    end in term_Map (term_sub_name t' n v) x' u'
  | term_ToA t' => term_ToA (term_sub_name t' n v)
  | term_FromA t' => term_FromA (term_sub_name t' n v)
  | term_Alloc => term_Alloc
  | term_FillU t1 => term_FillU (term_sub_name t1 n v)
  | term_FillF t1 x' m u => let u' := match name_eq_dec n (name_X x') with
    | left _ => (* shadowing *) u
    | right _ => term_sub_name u n v
    end in term_FillF (term_sub_name t1 n v) x' m u'
  | term_FillL t1 => term_FillL (term_sub_name t1 n v)
  | term_FillR t1 => term_FillR (term_sub_name t1 n v)
  | term_FillP t1 => term_FillP (term_sub_name t1 n v)
  | term_FillE t1 m => term_FillE (term_sub_name t1 n v) m
  | term_FillC t u => term_FillC (term_sub_name t n v) (term_sub_name u n v)
end
with val_sub_name (v': val) (n:name) (v:val) : val := match v' with
  | val_F x' m u => let u' := match name_eq_dec n (name_X x') with
    | left _ => (* shadowing *) u
    | right _ => term_sub_name u n v
    end in val_F x' m u'
  | val_H h => match name_eq_dec n (name_HD h) with
    | left _ => v
    | right _ => val_H h
  end
  | val_D h => val_D h
  | val_U => val_U
  | val_L v'' => val_L (val_sub_name v'' n v)
  | val_R v'' => val_R (val_sub_name v'' n v)
  | val_E m v'' => val_E m (val_sub_name v'' n v)
  | val_P v1 v2 => val_P (val_sub_name v1 n v) (val_sub_name v2 n v)
  | val_A H v1 v2 => val_A H (val_sub_name v1 n v) (val_sub_name v2 n v) (* TODO: false, need to update H by removing name (maybe) and adding new ones *)
end.

Definition term_sub (t: term) (x:var) (v:val) : term := term_sub_name t (name_X x) v.
Definition ectx_fill (C: ectx) (h:hdn) (v:val) : ectx := C. (* TODO complete *)
Definition val_incr_hnames (v : val) (h : hdn) : val := v. (* TODO complete *)

(******************************************************************************
 * TYPE
 *****************************************************************************)

(* Alias to the one defined by Ott *)
Definition type_eq_dec : forall (T1 T2: type), {T1 = T2} + {T1 <> T2} := eq_type.

(******************************************************************************
 * MULTIPLICITY
 *****************************************************************************)

Definition mul_plus (p1 p2: _mul) : _mul := Ur.
Definition mul_times (p1 p2: _mul) : _mul :=
  match p1, p2 with
  | Lin, Lin => Lin
  | _, _ => Ur
  end.
Definition mul_times' (pl: list _mul) : _mul :=
  List.fold_right mul_times Lin pl.
Inductive mul_IsSubtype : _mul -> _mul -> Prop :=
  | mul_IsSubtypeProofEq : forall (p : _mul), mul_IsSubtype p p
  | mul_IsSubtypeProofUr : forall (p2 : _mul), mul_IsSubtype Ur p2.
Theorem mul_IsSubtype_dec : forall (p1 p2: _mul), {mul_IsSubtype p1 p2} + {~mul_IsSubtype p1 p2}.
Proof.
  intros p1 p2. destruct p1, p2.
  - left. exact (mul_IsSubtypeProofEq Lin).
  - right. intros contra. inversion contra.
  - left. exact (mul_IsSubtypeProofUr Lin).
  - left. exact (mul_IsSubtypeProofEq Ur).
Defined.

(******************************************************************************
 * AGE
 *****************************************************************************)

Definition age_times (a1 a2 : age) : age := ext_plus a1 a2.
Definition age_times' (al: list age) : age := ext_plus' al.
Inductive age_IsSubtype : age -> age -> Prop :=
  | age_IsSubtypeProofEq : forall (a : age), age_IsSubtype a a
  | age_IsSubtypeProofInf : forall (a2 : age), age_IsSubtype Inf a2.
Theorem age_IsSubtype_dec : forall (a1 a2: age), {age_IsSubtype a1 a2} + {~(age_IsSubtype a1 a2)}.
Proof.
  intros a1 a2. destruct a1, a2.
  - assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. destruct H.
    * rewrite e. left. exact (age_IsSubtypeProofEq (Fin n0)).
    * right. intros contra. inversion contra. congruence.
  - right. intros contra. inversion contra.
  - left. exact (age_IsSubtypeProofInf (Fin n)).
  - left. exact (age_IsSubtypeProofEq Inf).
Defined.

(******************************************************************************
 * MODE
 *****************************************************************************)

Definition mode_plus (m1 m2: mode) : mode :=
  match m1, m2 with
  | None, _ => None
  | _, None => None
  | Some (p1, a1), Some (p2, a2) => match a1, a2 with
    | _, Inf => Some (mul_plus p1 p2, Inf)
    | Inf, _ => Some (mul_plus p1 p2, Inf)
    | _, _ => match a1, a2 with
      | Fin n1, Fin n2 => match Nat.eq_dec n1 n2 with
        | left _ => (* true *) Some (mul_plus p1 p2, Fin n1)
        | right _ => (* false *) None
        end
      | Inf, Inf => Some (mul_plus p1 p2, Inf)
      | _, _ => None
      end
    end
  end.
Definition mode_times (m1 m2: mode) : mode :=
  match m1, m2 with
  | None, _ => None
  | _, None => None
  | Some (p1, a1), Some (p2, a2) => Some (mul_times p1 p2, age_times a1 a2)
  end.
Definition mode_times' (ml: list mode) : mode :=
  List.fold_right mode_times (Some (Lin, Fin 0)) ml.
Inductive mode_IsSubtype : mode -> mode -> Prop :=
  | mode_IsSubtypeProofNone : forall (m1 : mode), mode_IsSubtype m1 None
  | mode_IsSubtypeProofPair : forall (p1 p2 : _mul) (a1 a2 : age), mul_IsSubtype p1 p2 -> age_IsSubtype a1 a2 -> mode_IsSubtype (Some (p1, a1)) (Some (p2, a2)).
Theorem mode_IsSubtype_dec : forall (m1 m2: mode), {mode_IsSubtype m1 m2} + {~mode_IsSubtype m1 m2}.
Proof.
  intros m1 m2. destruct m1 as [(p1 & a1)|], m2 as [(p2 & a2)|].
  - destruct (mul_IsSubtype_dec p1 p2), (age_IsSubtype_dec a1 a2).
    + left. exact (mode_IsSubtypeProofPair p1 p2 a1 a2 m a).
    + right. intros contra. inversion contra. congruence.
    + right. intros contra. inversion contra. congruence.
    + right. intros contra. inversion contra. congruence.
  - left. exact (mode_IsSubtypeProofNone (Some (p1, a1))).
  - right. intros contra. inversion contra.
  - left. exact (mode_IsSubtypeProofNone None).
Defined.
Inductive mode_IsValid : mode -> Prop :=
  mode_IsValidProof : forall (pa : mul * age), mode_IsValid (Some pa).
Theorem mode_IsValid_dec : forall (m : mode), {mode_IsValid m} + {~mode_IsValid m}.
Proof.
  intros m. destruct m as [pa|].
  - left. exact (mode_IsValidProof pa).
  - right. intros contra. inversion contra.
Qed.
Inductive mode_IsLin : mode -> Prop :=
  mode_IsLinProof : forall (a : age), mode_IsLin (Some (Lin, a)).
Theorem mode_IsLin_dec : forall (m : mode), {mode_IsLin m} + {~mode_IsLin m}.
Proof.
  intros m. destruct m as [pa|].
  - destruct pa as [p a]. destruct p.
    + left. exact (mode_IsLinProof a).
    + right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
Qed.
Inductive mode_IsUr : mode -> Prop :=
  mode_IsUrProof : forall (a : age), mode_IsUr (Some (Ur, a)).
Theorem mode_IsUr_dec : forall (m : mode), {mode_IsUr m} + {~mode_IsUr m}.
Proof.
  intros m. destruct m as [pa|].
  - destruct pa as [p a]. destruct p.
    + right. intros contra. inversion contra.
    + left. exact (mode_IsUrProof a).
  - right. intros contra. inversion contra.
Qed.

(******************************************************************************
 * BINDERS
 *****************************************************************************)

Definition bndr_name (b : bndr) : name :=
  match b with
  | bndr_V x m T => name_X x
  | bndr_H h T m => name_HD h
  | bndr_D h m1 T m2 => name_HD h
  end.

Definition bndr_mode (b : bndr) : mode := match b with
  | bndr_V _ m _ => m
  | bndr_H _ _ m => m
  | bndr_D _ m1 _ m2 => m1
  end.

Inductive bndr_IsVar : bndr -> Prop :=
  bndr_IsVarProof : forall x m T, bndr_IsVar (bndr_V x m T).
Theorem bndr_IsVar_dec : forall (b: bndr), {bndr_IsVar b} + {~bndr_IsVar b}.
Proof.
  intros b. destruct b.
  - left. exact (bndr_IsVarProof x m T).
  - right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
Qed.

Inductive bndr_IsDest : bndr -> Prop :=
  bndr_IsDestProof : forall h m T n, bndr_IsDest (bndr_D h m T n).
Theorem bndr_IsDest_dec : forall (b: bndr), {bndr_IsDest b} + {~bndr_IsDest b}.
Proof.
  intros b. destruct b.
  - right. intros contra. inversion contra.
  - left. exact (bndr_IsDestProof h m T n).
  - right. intros contra. inversion contra.
Qed.

Inductive bndr_IsHole : bndr -> Prop :=
  bndr_IsHoleProof : forall h m T, bndr_IsHole (bndr_H h m T).
Theorem bndr_IsHole_dec : forall (b: bndr), {bndr_IsHole b} + {~bndr_IsHole b}.
Proof.
  intros b. destruct b.
  - right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
  - left. exact (bndr_IsHoleProof h T n).
Qed.

(******************************************************************************
 * CONTEXTS
 *****************************************************************************)

Axiom ctx_Coherent: forall (G : CtxM.t bndr) n b, CtxM.MapsTo n b G -> (bndr_name b) = n.

Definition ctx_DestOnly (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> bndr_IsDest b.
Definition ctx_HoleOnly (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> bndr_IsHole b.
Definition ctx_VarOnly (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> bndr_IsVar b.
Definition ctx_NoDest (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> ~ (bndr_IsDest b).
Definition ctx_NoHole (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> ~ (bndr_IsHole b).
Definition ctx_NoVar (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> ~ (bndr_IsVar b).
Definition ctx_IsValid (G: CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> mode_IsValid (bndr_mode b).
Definition ctx_SubsetEq (G1 G2 : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G1 -> CtxM.MapsTo n b G2.
Definition ctx_HdnmNotMem (h : hdn) (G : CtxM.t bndr) : Prop :=
  ~CtxM.In (name_HD h) G.
Definition ctx_OnlyLin (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> mode_IsLin (bndr_mode b).
Definition ctx_OnlyUr (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> mode_IsUr (bndr_mode b).
Definition ctx_Disjoint (G1 G2 : CtxM.t bndr) : Prop :=
  forall n, (CtxM.In n G1 -> ~CtxM.In n G2) /\ (CtxM.In n G2 -> ~CtxM.In n G1).
Inductive ctx_Compatible : CtxM.t bndr -> bndr -> Prop :=
  | ctx_CompatibleProofV : forall G x m1 m2 T, CtxM.MapsTo (name_X x) (bndr_V x m1 T) G -> mode_IsSubtype m1 m2 -> ctx_OnlyUr (CtxM.remove (name_X x) G) -> ctx_Compatible G (bndr_V x m2 T)
  | ctx_CompatibleProofD : forall G h m11 m2 m21 T, CtxM.MapsTo (name_HD h) (bndr_D h m11 T m2) G -> mode_IsSubtype m11 m21 -> ctx_OnlyUr (CtxM.remove (name_HD h) G) -> ctx_Compatible G (bndr_D h m21 T m2)
  | ctx_CompatibleProofH : forall G h m1 m2 T, CtxM.MapsTo (name_HD h) (bndr_H h T m1) G -> mode_IsSubtype m1 m2 -> ctx_OnlyUr (CtxM.remove (name_HD h) G) -> ctx_Compatible G (bndr_H h T m2).

(* Actually a function; not really a theorem *)
Theorem ctx_add (b' : bndr) (G : CtxM.t bndr) : CtxM.t bndr.
Proof.
  destruct (CtxM.find (bndr_name b') G) eqn:eq_find.
  * (* Some b *)
    assert (CtxM.MapsTo (bndr_name b') b G). apply CtxM.find_2. exact eq_find.
    apply ctx_Coherent in H. destruct b as [x m1 T1 | h m11 T1 m12 | h T1 m1], b' as [x' m2 T2 | h' m21 T2 m22 | h' T2 m2].
    all: unfold bndr_name in H, eq_find.
    - assert (x = x') as name_eq by (injection H ; tauto). rewrite (eq_sym name_eq) in eq_find. destruct (type_eq_dec T1 T2).
      (* T1 = T2 *) exact (CtxM.add (name_X x) (bndr_V x (mode_plus m1 m2) T1) G).
      (* T1 != T2 *) all: exact (CtxM.add (name_X x) (bndr_V x None type_U) G).
    - congruence.
    - congruence.
    - congruence.
    - assert (h = h') as name_eq by (injection H ; tauto). rewrite (eq_sym name_eq) in eq_find. destruct (type_eq_dec T1 T2), (mode_eq_dec m12 m22).
      (* T1 = T2, m12 = m22 *) exact (CtxM.add (name_HD h) (bndr_D h (mode_plus m11 m21) T1 m12) G).
      (* T1 != T2 \/ m12 != m22 *) all: exact (CtxM.add (name_HD h) (bndr_D h None type_U None) G).
    - (* bndr_D vs bndr_H *) exact (CtxM.add (name_HD h) (bndr_D h None type_U None) G).
    - congruence.
    - (* bndr_H vs bndr_D *) exact (CtxM.add (name_HD h) (bndr_D h None type_U None) G).
    - assert (h = h') as name_eq by (injection H ; tauto). rewrite (eq_sym name_eq) in eq_find. destruct (type_eq_dec T1 T2).
      (* T1 = T2 *) exact (CtxM.add (name_HD h) (bndr_H h T1 (mode_plus m1 m2)) G).
      (* T1 != T2 *) all: exact (CtxM.add (name_HD h) (bndr_H h type_U None) G).
  * (* None *)
    exact (CtxM.add (bndr_name b') b' G).
Defined.

Definition ctx_from_list (bs : list bndr) : CtxM.t bndr :=
  List.fold_right (fun b G => ctx_add b G) (CtxM.empty bndr) bs.

Definition ctx_union (G1 G2 : CtxM.t bndr) : CtxM.t bndr :=
  (* G1 is acc, G2 is iterated over *)
  CtxM.fold (fun n b G => ctx_add b G) G2 G1.

Definition ctx_stimes (m1 : mode) (G : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.map (fun b =>
    match b with
    | bndr_V x m2 T2 => bndr_V x (mode_times m1 m2) T2
    | bndr_D h m2 T2 m3 => bndr_D h (mode_times m1 m2) T2 m3
    | bndr_H h T2 m2 => bndr_H h T2 (mode_times m1 m2)
    end
  ) G.

Definition ctx_minus (G : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.map (fun b =>
    match b with
    | bndr_V x m2 T2 => bndr_V x None type_U (* error *)
    | bndr_D h m2 T2 m3 => bndr_H h T2 m3
    | bndr_H h T2 m2 => bndr_H h type_U None (* error *)
    end
  ) G.

(*****************************************************************************)


Inductive pred : Type :=  (*r Serves for the .mng file. Isn't used in the actual rules *)
 | _ctx_DestOnly (G:ctx)
 | _ctx_HoleOnly (G:ctx)
 | _ctx_VarOnly (G:ctx)
 | _ctx_NoDest (G:ctx)
 | _ctx_NoHole (G:ctx)
 | _ctx_NoVar (G:ctx)
 | _ctx_IsValid (G:ctx)
 | _ctx_SubsetEq (G1:ctx) (G2:ctx)
 | _ctx_HdnmNotMem (h:hdn) (G:ctx)
 | _ctx_Compatible (G:ctx) (b:bndr)
 | _ctx_OnlyLin (G:ctx)
 | _ctx_OnlyUr (G:ctx)
 | _ctx_Disjoint (G1:ctx) (G2:ctx)
 | _mode_IsValid (m:mode)
 | _mode_IsLin (m:mode)
 | _mode_IsUr (m:mode)
 | _TyR_val (G:ctx) (v:val) (T:type)
 | _Ty_eterm (G:ctx) (j:eterm) (T:type)
 | _TyR_ectx (G:ctx) (C:ectx) (T:type).
(** definitions *)

(* defns Ty *)
Inductive TyR_val : ctx -> val -> type -> Prop :=    (* defn TyR_val *)
 | TyR_val_H : forall (h:hdn) (T:type) (a:age),
     TyR_val  (ctx_from_list  (cons (bndr_H h T  (Some (pair   Lin    a )) ) nil) )  (val_H h) T
 | TyR_val_D : forall (G:ctx) (h:hdn) (T:type) (n:mode),
     ctx_Compatible G (bndr_D h  (Some (pair   Lin     (Fin 0)  ))  T n)  ->
     TyR_val G (val_D h) (type_D T n)
 | TyR_val_U : 
     TyR_val  (ctx_from_list  nil )  val_U type_U
 | TyR_val_F : forall (G:ctx) (x:var) (m:mode) (t:term) (T1 T2:type)
     (TYt: Ty_eterm  (ctx_union  G    (ctx_from_list  (cons (bndr_V x m T1) nil) )  )   (eterm_ECtxApp ectx_Id  t )  T2),
     ctx_DestOnly G  ->
     TyR_val G (val_F x m t) (type_F T1 m T2)
 | TyR_val_L : forall (G:ctx) (v:val) (T1 T2:type)
     (TYRv: TyR_val G v T1),
     TyR_val G (val_L v) (type_S T1 T2)
 | TyR_val_R : forall (G:ctx) (v:val) (T1 T2:type)
     (TYRv: TyR_val G v T2),
     TyR_val G (val_R v) (type_S T1 T2)
 | TyR_val_P : forall (G1 G2:ctx) (v1 v2:val) (T1 T2:type)
     (TYRv1: TyR_val G1 v1 T1)
     (TYRv2: TyR_val G2 v2 T2),
     TyR_val  (ctx_union  G1   G2 )  (val_P v1 v2) (type_P T1 T2)
 | TyR_val_E : forall (m:mode) (G:ctx) (v:val) (T:type)
     (TYRv: TyR_val G v T),
     TyR_val  (ctx_stimes  m   G )  (val_E m v) (type_E m T)
 | TyR_val_A : forall (G1 G2 G3:ctx) (v1 v2:val) (T1 T2:type)
     (TYRv1: TyR_val  (ctx_union  G1     (ctx_minus  G3 )   )  v1 T1)
     (TYRv2: TyR_val  (ctx_union  G2   G3 )  v2 T2),
     ctx_Disjoint G1 G2  ->
     ctx_DestOnly  (ctx_union  G2   G3 )   ->
     ctx_DestOnly G1  ->
     TyR_val  (ctx_union  G1   G2 )  (val_A  (hdns_from_ctx   (ctx_minus  G3 )  )  v1 v2) (type_A T1 T2)
with Ty_eterm : ctx -> eterm -> type -> Prop :=    (* defn Ty_eterm *)
 | Ty_eterm_Val : forall (G:ctx) (v:val) (T:type),
     ctx_NoHole G  ->
     TyR_val G v T ->
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_Val v) )  T
 | Ty_eterm_Var : forall (G:ctx) (x:var) (T:type),
     ctx_Compatible G (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T)  ->
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_Var x) )  T
 | Ty_eterm_App : forall (m:mode) (G1 G2:ctx) (t u:term) (T2 T1:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  T1)
     (TYu: Ty_eterm G2  (eterm_ECtxApp ectx_Id  u )  (type_F T1 m T2)),
     Ty_eterm  (ctx_union   (ctx_stimes  m   G1 )    G2 )   (eterm_ECtxApp ectx_Id  (term_App t u) )  T2
 | Ty_eterm_PatU : forall (G1 G2:ctx) (t u:term) (U:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  type_U)
     (TYu: Ty_eterm G2  (eterm_ECtxApp ectx_Id  u )  U),
     Ty_eterm  (ctx_union  G1   G2 )   (eterm_ECtxApp ectx_Id  (term_PatU t u) )  U
 | Ty_eterm_PatS : forall (m:mode) (G1 G2:ctx) (t:term) (x1:var) (u1:term) (x2:var) (u2:term) (U T1 T2:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  (type_S T1 T2))
     (TYu1: Ty_eterm  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x1 m T1) nil) )  )   (eterm_ECtxApp ectx_Id  u1 )  U)
     (TYu2: Ty_eterm  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x2 m T2) nil) )  )   (eterm_ECtxApp ectx_Id  u2 )  U),
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x1 m T1) nil) )   ->
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x2 m T2) nil) )   ->
     Ty_eterm  (ctx_union   (ctx_stimes  m   G1 )    G2 )   (eterm_ECtxApp ectx_Id  (term_PatS t m x1 u1 x2 u2) )  U
 | Ty_eterm_PatP : forall (m:mode) (G1 G2:ctx) (t:term) (x1 x2:var) (u:term) (U T1 T2:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  (type_P T1 T2))
     (TYu: Ty_eterm  (ctx_union  G2    (ctx_from_list  ((app (cons (bndr_V x1 m T1) nil) (app (cons (bndr_V x2 m T2) nil) nil))) )  )   (eterm_ECtxApp ectx_Id  u )  U),
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x1 m T1) nil) )   ->
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x2 m T2) nil) )   ->
     ctx_Disjoint  (ctx_from_list  (cons (bndr_V x1 m T1) nil) )   (ctx_from_list  (cons (bndr_V x2 m T2) nil) )   ->
     Ty_eterm  (ctx_union   (ctx_stimes  m   G1 )    G2 )   (eterm_ECtxApp ectx_Id  (term_PatP t m x1 x2 u) )  U
 | Ty_eterm_PatE : forall (m:mode) (G1 G2:ctx) (t:term) (n:mode) (x:var) (u:term) (U T:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  (type_E n T))
     (TYu: Ty_eterm  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )  T) nil) )  )   (eterm_ECtxApp ectx_Id  u )  U),
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )  T) nil) )   ->
     Ty_eterm  (ctx_union   (ctx_stimes  m   G1 )    G2 )   (eterm_ECtxApp ectx_Id  (term_PatE t m n x u) )  U
 | Ty_eterm_Map : forall (G1 G2:ctx) (t:term) (x:var) (u:term) (T1 U T2:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  (type_A T1 T2))
     (TYu: Ty_eterm  (ctx_union   (ctx_stimes   (Some (pair   Lin     (Fin 1)  ))    G2 )     (ctx_from_list  (cons (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T2) nil) )  )   (eterm_ECtxApp ectx_Id  u )  U),
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T2) nil) )   ->
     Ty_eterm  (ctx_union  G1   G2 )   (eterm_ECtxApp ectx_Id  (term_Map t x u) )  (type_A T1 U)
 | Ty_eterm_FillU : forall (G:ctx) (t:term) (n:mode)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  (type_D type_U n)),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_FillU t) )  type_U
 | Ty_eterm_FillF : forall (G1:ctx) (n:mode) (G2:ctx) (t:term) (x:var) (m:mode) (u:term) (T1 T2:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  (type_D (type_F T1 m T2) n))
     (TYu: Ty_eterm  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x m T1) nil) )  )   (eterm_ECtxApp ectx_Id  u )  T2),
     ctx_Disjoint G2  (ctx_from_list  (cons (bndr_V x m T1) nil) )   ->
     Ty_eterm  (ctx_union  G1    (ctx_stimes    (mode_times'  ((app (cons  (Some (pair   Lin     (Fin 1)  ))  nil) (app (cons n nil) nil))) )     G2 )  )   (eterm_ECtxApp ectx_Id  (term_FillF t x m u) )  type_U
 | Ty_eterm_FillL : forall (G:ctx) (t:term) (T1:type) (n:mode) (T2:type)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  (type_D (type_S T1 T2) n)),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_FillL t) )  (type_D T1 n)
 | Ty_eterm_FillR : forall (G:ctx) (t:term) (T2:type) (n:mode) (T1:type)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  (type_D (type_S T1 T2) n)),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_FillR t) )  (type_D T2 n)
 | Ty_eterm_FillP : forall (G:ctx) (t:term) (T1:type) (n:mode) (T2:type)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  (type_D (type_P T1 T2) n)),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_FillP t) )  (type_P (type_D T1 n) (type_D T2 n))
 | Ty_eterm_FillE : forall (G:ctx) (t:term) (m:mode) (T:type) (n:mode)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  (type_D (type_E m T) n)),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_FillE t m) )  (type_D T  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) ) )
 | Ty_eterm_FillC : forall (G1:ctx) (n:mode) (G2:ctx) (t u:term) (T2 T1:type)
     (TYt: Ty_eterm G1  (eterm_ECtxApp ectx_Id  t )  (type_D T1 n))
     (TYu: Ty_eterm G2  (eterm_ECtxApp ectx_Id  u )  (type_A T1 T2)),
     Ty_eterm  (ctx_union  G1    (ctx_stimes    (mode_times'  ((app (cons  (Some (pair   Lin     (Fin 1)  ))  nil) (app (cons n nil) nil))) )     G2 )  )   (eterm_ECtxApp ectx_Id  (term_FillC t u) )  T2
 | Ty_eterm_Alloc : forall (T:type),
     Ty_eterm  (ctx_from_list  nil )   (eterm_ECtxApp ectx_Id  term_Alloc )  (type_A T (type_D T  (Some (pair   Lin     (Fin 0)  )) ))
 | Ty_eterm_ToA : forall (G:ctx) (t:term) (T:type)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  T),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_ToA t) )  (type_A T type_U)
 | Ty_eterm_FromA : forall (G:ctx) (t:term) (T:type)
     (TYt: Ty_eterm G  (eterm_ECtxApp ectx_Id  t )  (type_A T type_U)),
     Ty_eterm G  (eterm_ECtxApp ectx_Id  (term_FromA t) )  T
with TyR_ectx : ctx -> ectx -> type -> Prop :=    (* defn TyR_ectx *)
 | TyR_ectx_T : forall (G1 G2:ctx) (C:ectx) (T1 T2:type) (G3:ctx) (t:term)
     (TYt: Ty_eterm  (ctx_union  G2   G3 )   (eterm_ECtxApp ectx_Id  t )  T1)
     (TYj: Ty_eterm G1 (eterm_ECtxApp C t) T2),
     ctx_Disjoint G1 G2  ->
     ctx_Disjoint G2 G3  ->
     ctx_NoVar  (ctx_union  G2   G3 )   ->
     ctx_NoVar G1  ->
     TyR_ectx  (ctx_union  G1     (ctx_minus  G2 )   )  C (type_C T1 T2).
(** definitions *)

(* defns Sem *)
Inductive Sem_eterm : eterm -> eterm -> Prop :=    (* defn Sem_eterm *)
 | Sem_eterm_App : forall (C:ectx) (v:val) (x:var) (m:mode) (t:term),
     Sem_eterm (eterm_ECtxApp C (term_App (term_Val v) (term_Val  (val_F x m t) ))) (eterm_ECtxApp C  (term_sub  t   x   v ) )
 | Sem_eterm_PatU : forall (C:ectx) (t2:term),
     Sem_eterm (eterm_ECtxApp C (term_PatU (term_Val val_U) t2)) (eterm_ECtxApp C t2)
 | Sem_eterm_PatL : forall (C:ectx) (v:val) (m:mode) (x1:var) (u1:term) (x2:var) (u2:term) (x:var),
     Sem_eterm (eterm_ECtxApp C (term_PatS (term_Val  (val_L v) ) m x1 u1 x2 u2)) (eterm_ECtxApp C  (term_sub  u1   x   v ) )
 | Sem_eterm_PatR : forall (C:ectx) (v:val) (m:mode) (x1:var) (u1:term) (x2:var) (u2:term) (x:var),
     Sem_eterm (eterm_ECtxApp C (term_PatS (term_Val  (val_R v) ) m x1 u1 x2 u2)) (eterm_ECtxApp C  (term_sub  u2   x   v ) )
 | Sem_eterm_PatP : forall (C:ectx) (v1 v2:val) (m:mode) (x1 x2:var) (u:term),
     Sem_eterm (eterm_ECtxApp C (term_PatP (term_Val (val_P v1 v2)) m x1 x2 u)) (eterm_ECtxApp C  (term_sub   (term_sub  u   x1   v1 )    x2   v2 ) )
 | Sem_eterm_PatE : forall (C:ectx) (n:mode) (v:val) (m:mode) (x:var) (u:term),
     Sem_eterm (eterm_ECtxApp C (term_PatE (term_Val (val_E n v)) m n x u)) (eterm_ECtxApp C  (term_sub  u   x   v ) )
 | Sem_eterm_MapOpen : forall (C:ectx) (H:hdns) (v1 v2:val) (x:var) (u:term) (h':hdn),
     h' =  (hdns_max_hnames   (hdns_from_ectx  C )  )   ->
     Sem_eterm (eterm_ECtxApp C (term_Map (term_Val (val_A H v1 v2)) x u)) (eterm_ECtxApp  (ectx_Comp C  (ectx_AOpen  (hdns_incr_hnames  H   h' )   (val_incr_hnames  v1   h' )  ectx_Id) )   (term_sub  u   x    (val_incr_hnames  v2   h' )  ) )
 | Sem_eterm_MapClose : forall (C:ectx) (H:hdns) (v1 v2:val),
     Sem_eterm (eterm_ECtxApp  (ectx_Comp C (ectx_AOpen H v1 ectx_Id))  (term_Val v2)) (eterm_ECtxApp C (term_Val (val_A H v1 v2)))
 | Sem_eterm_Alloc : 
     Sem_eterm  (eterm_ECtxApp ectx_Id  term_Alloc )   (eterm_ECtxApp ectx_Id  (term_Val (val_A  (hdns_from_list  (cons  1  nil) )  (val_D  1 ) (val_H  1 ))) ) 
 | Sem_eterm_ToA : forall (C:ectx) (v:val),
     Sem_eterm (eterm_ECtxApp C (term_ToA (term_Val v))) (eterm_ECtxApp C (term_Val (val_A  (hdns_from_list  nil )  v val_U)))
 | Sem_eterm_FromA : forall (C:ectx) (v:val),
     Sem_eterm (eterm_ECtxApp C (term_FromA (term_Val (val_A  (hdns_from_list  nil )  v val_U))))  (eterm_ECtxApp ectx_Id  (term_Val v) ) 
 | Sem_eterm_FillU : forall (C:ectx) (h:hdn),
     Sem_eterm (eterm_ECtxApp C (term_FillU (term_Val (val_D h)))) (eterm_ECtxApp  (ectx_fill  C   h   val_U )  (term_Val val_U))
 | Sem_eterm_FillF : forall (C:ectx) (h:hdn) (x:var) (m:mode) (u:term),
     Sem_eterm (eterm_ECtxApp C (term_FillF (term_Val (val_D h)) x m u)) (eterm_ECtxApp  (ectx_fill  C   h   (val_F x m u) )  (term_Val val_U))
 | Sem_eterm_FillL : forall (C:ectx) (h h':hdn),
     h' =  (hdns_max_hnames   (HdnsM.union   (hdns_from_ectx  C )     (hdns_from_list  (cons h nil) )  )  )   ->
     Sem_eterm (eterm_ECtxApp C (term_FillL (term_Val (val_D h)))) (eterm_ECtxApp  (ectx_fill  C   h   (val_L (val_H   ( h'  +   1  )  )) )  (term_Val (val_D   ( h'  +   1  )  )))
 | Sem_eterm_FillR : forall (C:ectx) (h h':hdn),
     h' =  (hdns_max_hnames   (HdnsM.union   (hdns_from_ectx  C )     (hdns_from_list  (cons h nil) )  )  )   ->
     Sem_eterm (eterm_ECtxApp C (term_FillR (term_Val (val_D h)))) (eterm_ECtxApp  (ectx_fill  C   h   (val_R (val_H   ( h'  +   1  )  )) )  (term_Val (val_D   ( h'  +   1  )  )))
 | Sem_eterm_FillE : forall (C:ectx) (h:hdn) (m:mode) (h':hdn),
     h' =  (hdns_max_hnames   (HdnsM.union   (hdns_from_ectx  C )     (hdns_from_list  (cons h nil) )  )  )   ->
     Sem_eterm (eterm_ECtxApp C (term_FillE (term_Val (val_D h)) m)) (eterm_ECtxApp  (ectx_fill  C   h   (val_E m (val_H   ( h'  +   1  )  )) )  (term_Val (val_D   ( h'  +   1  )  )))
 | Sem_eterm_FillP : forall (C:ectx) (h h':hdn),
     h' =  (hdns_max_hnames   (HdnsM.union   (hdns_from_ectx  C )     (hdns_from_list  (cons h nil) )  )  )   ->
     Sem_eterm (eterm_ECtxApp C (term_FillP (term_Val (val_D h)))) (eterm_ECtxApp  (ectx_fill  C   h   (val_P (val_H   ( h'  +   1  )  ) (val_H   ( h'  +   2  )  )) )  (term_Val (val_P (val_D   ( h'  +   1  )  ) (val_D   ( h'  +   2  )  ))))
 | Sem_eterm_FillC : forall (C:ectx) (h:hdn) (H:hdns) (v1 v2:val) (h':hdn),
     h' =  (hdns_max_hnames   (HdnsM.union   (hdns_from_ectx  C )     (hdns_from_list  (cons h nil) )  )  )   ->
     Sem_eterm (eterm_ECtxApp C (term_FillC (term_Val (val_D h)) (term_Val (val_A H v1 v2)))) (eterm_ECtxApp  (ectx_fill  C   h    (val_incr_hnames  v1   h' )  )  (term_Val  (val_incr_hnames  v2   h' ) )).



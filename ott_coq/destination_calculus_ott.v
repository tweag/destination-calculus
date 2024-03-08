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
Require Import Coq.FSets.FMapFacts.

Definition var : Type := nat. (*r Term-level variable name *)
Definition hdn : Type := nat. (*r Hole or destination static name *)
Definition k : Type := nat. (*r Index for ranges *)

(* Will be aliased later to mul *)
Inductive _mul : Type :=
  | Lin : _mul
  | Ur : _mul.

Definition mul_plus (p1 p2: _mul) : _mul := Ur.

Definition mul_times (p1 p2: _mul) : _mul :=
  match p1, p2 with
  | Lin, Lin => Lin
  | _, _ => Ur
  end.

Definition mul_times' (pl: list _mul) : _mul :=
  List.fold_right mul_times Lin pl.

Theorem mul_eq_dec : forall (p1 p2: _mul), {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.

Inductive mul_IsSubtype : _mul -> _mul -> Prop :=
  | mul_IsSubtypeProofEq : forall (p : _mul), mul_IsSubtype p p
  | mul_IsSubtypeProofUr : forall (p2 : _mul), mul_IsSubtype Ur p2.
Theorem mul_IsSubtype_dec : forall (p1 p2: _mul), mul_IsSubtype p1 p2 + (notT (mul_IsSubtype p1 p2)).
Proof.
  intros p1 p2. destruct p1, p2.
  - left. exact (mul_IsSubtypeProofEq Lin).
  - right. intros contra. inversion contra.
  - left. exact (mul_IsSubtypeProofUr Lin).
  - left. exact (mul_IsSubtypeProofEq Ur).
Defined.

(* Will be aliased later to ext_nat *)

Theorem mode_eq_dec : forall (m1 m2: option (_mul * ext_nat)), {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality. destruct a, p.
  - destruct (mul_eq_dec _m _m0), (ext_eq_dec e e0); subst; auto.
    * right. congruence.
    * right. congruence.
    * right. congruence.
Defined.


Definition mul : Type := _mul.

Definition age : Type := ext_nat.

Definition mode : Type := option (mul * age).

Inductive type : Type :=  (*r Type *)
 | type_U : type (*r Unit *)
 | type_S (T1:type) (T2:type) (*r Sum *)
 | type_P (T1:type) (T2:type) (*r Product *)
 | type_E (m:mode) (T:type) (*r Exponential *)
 | type_A (T1:type) (T2:type) (*r Ampar type (consuming $(T2:type)$ yields $(T1:type)$) *)
 | type_F (T1:type) (m1:mode) (T2:type) (*r Function *)
 | type_D (T:type) (m:mode) (*r Destination *).

Inductive bndr : Type :=  (*r Type assignment to either variable, destination or hole *)
 | bndr_V (x:var) (m:mode) (T:type) (*r Variable *)
 | bndr_D (h:hdn) (m:mode) (T:type) (n:mode) (*r Destination ($(m:mode)$ is its own modality; $(n:mode)$ is the modality for values it accepts) *)
 | bndr_H (h:hdn) (n:mode) (T:type) (*r Hole ($(n:mode)$ is the modality for values it accepts, it doesn't have a modality on its own) *).
Lemma eq_type: forall (x y : type), {x = y} + {x <> y}.
Proof.
decide equality. apply mode_eq_dec. apply mode_eq_dec. apply mode_eq_dec.
Defined.
Hint Resolve eq_type : ott_coq_equality.
Inductive name : Type :=
  | name_X : var -> name
  | name_HD : hdn -> name.

Module Name_as_UDT <: UsualDecidableType.
  Definition t := name.

  Definition eq := @eq name.
  Definition eq_refl := @eq_refl name.
  Definition eq_sym := @eq_sym name.
  Definition eq_trans := @eq_trans name.

  (* Define the eq_dec function *)
  Theorem eq_dec : forall x y : name, {x = y} + {x <> y}.
  Proof.
    intros x y. induction x.
    - induction y.
        + assert ({v = v0} + {v <> v0}) by apply Nat.eq_dec. destruct H.
           * left. rewrite e. reflexivity.
           * right. congruence.
        + right. congruence.
    - induction y.
        + right. congruence.
        + induction h, h0.
          * assert ({d = d0} + {d <> d0}) by apply (list_eq_dec Nat.eq_dec). destruct H.
            ** left. rewrite e. reflexivity.
            ** right. congruence.
          * right. congruence.
          * right. congruence.
          * assert ({hdn5 = hdn0} + {hdn5 <> hdn0}) by apply Nat.eq_dec. destruct H.
            ** left. rewrite e. reflexivity.
            ** right. congruence.
    Defined.

  Instance eq_equiv : Equivalence Name_as_UDT.eq. split. exact eq_refl. exact eq_sym. exact eq_trans. Defined.

End Name_as_UDT.

Definition name_eq_dec := Name_as_UDT.eq_dec.

Module Name_as_UDTOrig := Backport_DT(Name_as_UDT).
Module CtxM := FMapWeakList.Make(Name_as_UDTOrig).

Definition type_eq_dec : forall (T1 T2: type), {T1 = T2} + {T1 <> T2} := eq_type.

Definition age_eq_dec : forall (a1 a2: age), {a1 = a2} + {a1 <> a2} := ext_eq_dec.
Definition age_times (a1 a2 : age) : age := ext_plus a1 a2.
Definition age_times' (al: list age) : age := ext_plus' al.
Inductive age_IsSubtype : age -> age -> Type :=
  | age_IsSubtypeProofEq : forall (a : age), age_IsSubtype a a
  | age_IsSubtypeProofInf : forall (a2 : age), age_IsSubtype Inf a2.
Theorem age_IsSubtype_dec : forall (a1 a2: age), age_IsSubtype a1 a2 + (notT (age_IsSubtype a1 a2)).
Proof.
  intros a1 a2. destruct a1, a2.
  - assert ({n = n0} + {n <> n0}) by apply Nat.eq_dec. destruct H.
    - rewrite e. left. exact (age_IsSubtypeProofEq (Fin n0)).
    - right. intros contra. inversion contra. congruence.
  - right. intros contra. inversion contra.
  - left. exact (age_IsSubtypeProofInf (Fin n)).
  - left. exact (age_IsSubtypeProofEq Inf).
Defined.

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

Inductive mode_IsSubtype : mode -> mode -> Type :=
  | mode_IsSubtypeProofNone : forall (m1 : mode), mode_IsSubtype m1 None
  | mode_IsSubtypeProofPair : forall (p1 p2 : _mul) (a1 a2 : age), mul_IsSubtype p1 p2 -> age_IsSubtype a1 a2 -> mode_IsSubtype (Some (p1, a1)) (Some (p2, a2)).
Theorem mode_IsSubtype_dec : forall (m1 m2: mode), mode_IsSubtype m1 m2 + (notT (mode_IsSubtype m1 m2)).
Proof.
  intros m1 m2. destruct m1 as [pa1|], m2 as [pa2|].
  - destruct pa1 as [p1 a1], pa2 as [p2 a2]. assert ({mul_IsSubtype p1 p2} + {~mul_IsSubtype p1 p2}) as H1 by apply mul_IsSubtype_dec.

Inductive mode_IsValid : mode -> Prop :=
  mode_IsValidProof : forall (pa : mul * age), mode_IsValid (Some pa).
Theorem mode_IsValid_dec : forall (m : mode), mode_IsValid m + (notT (mode_IsValid m)).
Proof.
  intros m. destruct m as [pa|].
  - left. exact (mode_IsValidProof pa).
  - right. intros contra. inversion contra.
Qed.

Inductive mode_IsLin : mode -> Prop :=
  mode_IsLinProof : forall (a : age), mode_IsLin (Some (Lin, a)).
Theorem mode_IsLin_dec : forall (m : mode), mode_IsLin m + (notT (mode_IsLin m)).
Proof.
  intros m. destruct m as [pa|].
  - destruct pa as [p a]. destruct p.
    + left. exact (mode_IsLinProof a).
    + right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
Qed.

Inductive mode_IsUr : mode -> Prop :=
  mode_IsUrProof : forall (a : age), mode_IsUr (Some (Ur, a)).
Theorem mode_IsUr_dec : forall (m : mode), mode_IsUr m + (notT (mode_IsUr m)).
Proof.
  intros m. destruct m as [pa|].
  - destruct pa as [p a]. destruct p.
    + right. intros contra. inversion contra.
    + left. exact (mode_IsUrProof a).
  - right. intros contra. inversion contra.
Qed.

Definition bndr_name (b : bndr) : name :=
  match b with
  | bndr_V x m T => name_X x
  | bndr_H h m T => name_HD h
  | bndr_D h m1 T m2 => name_HD h
  end.

Definition bndr_mode (b : bndr) : mode := match b with
  | bndr_V _ m _ => m
  | bndr_H _ m _ => m
  | bndr_D _ m1 _ m2 => m1
  end.

Definition bndr_update_mode (b:bndr) (m:mode) := match b with
  | bndr_V x _ T => bndr_V x m T
  | bndr_H h _ T => bndr_H h m T
  | bndr_D h _ T m2 => bndr_D h m T m2
  end.

Inductive bndr_IsVar : bndr -> Prop :=
  bndr_IsVarProof : forall x m T, bndr_IsVar (bndr_V x m T).
Theorem bndr_IsVar_dec : forall (b: bndr), bndr_IsVar b + (notT (bndr_IsVar b)).
Proof.
  intros b. destruct b.
  - left. exact (bndr_IsVarProof x m T).
  - right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
Qed.

Inductive bndr_IsDest : bndr -> Prop :=
  bndr_IsDestProof : forall h m T n, bndr_IsDest (bndr_D h m T n).
Theorem bndr_IsDest_dec : forall (b: bndr), bndr_IsDest b + (notT (bndr_IsDest b)).
Proof.
  intros b. destruct b.
  - right. intros contra. inversion contra.
  - left. exact (bndr_IsDestProof h m T n).
  - right. intros contra. inversion contra.
Qed.

Inductive bndr_IsHole : bndr -> Prop :=
  bndr_IsHoleProof : forall h m T, bndr_IsHole (bndr_H h m T).
Theorem bndr_IsHole_dec : forall (b: bndr), bndr_IsHole b + (notT (bndr_IsHole b)).
Proof.
  intros b. destruct b.
  - right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
  - left. exact (bndr_IsHoleProof h n T).
Qed.

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
Inductive ctx_Compatible : CtxM.t bndr -> bndr -> Prop :=
  | ctx_CompatibleProofV : forall G x m1 m2 T, CtxM.MapsTo (name_X x) (bndr_V x m1 T) G -> mode_IsSubtype m1 m2 -> ctx_OnlyUr (CtxM.remove (name_X x) G) -> ctx_Compatible G (bndr_V x m2 T)
  | ctx_CompatibleProofD : forall G h m11 m2 m21 T, CtxM.MapsTo (name_HD h) (bndr_D h m11 T m2) G -> mode_IsSubtype m11 m21 -> ctx_OnlyUr (CtxM.remove (name_HD h) G) -> ctx_Compatible G (bndr_D h m21 T m2)
  | ctx_CompatibleProofH : forall G h m1 m2 T, CtxM.MapsTo (name_HD h) (bndr_H h m1 T) G -> mode_IsSubtype m1 m2 -> ctx_OnlyUr (CtxM.remove (name_HD h) G) -> ctx_Compatible G (bndr_H h m2 T).

Axiom ctx_Coherent: forall (G : CtxM.t bndr) n b, CtxM.MapsTo n b G -> (bndr_name b) = n.

Inductive bndr_CompatibleTypes : bndr -> bndr -> Type :=
  | bndr_CompatibleTypesProofV : forall x m1 m2 T, bndr_CompatibleTypes (bndr_V x m1 T) (bndr_V x m2 T)
  | bndr_CompatibleTypesProofD : forall h m11 m2 m21 T, bndr_CompatibleTypes (bndr_D h m11 T m2) (bndr_D h m21 T m2)
  | bndr_CompatibleTypesProofH : forall h m1 m2 T, bndr_CompatibleTypes (bndr_H h m1 T) (bndr_H h m2 T).

Theorem bndr_CompatibleTypes_dec : forall (b b' : bndr), bndr_CompatibleTypes b b'+notT (bndr_CompatibleTypes b b').
Proof.
  intros b b'. assert ({bndr_name b = bndr_name b'} + {bndr_name b <> bndr_name b'}) by apply name_eq_dec. destruct H as [name_eq|name_neq].
  - unfold bndr_name in name_eq. destruct b eqn:Hb in name_eq. destruct b' eqn:Hb' in name_eq. assert ({T = T0} + {T <> T0}) by apply type_eq_dec. destruct H as [T_eq|T_neq].
    * left. assert (x = x0) as x_eq. injection name_eq. tauto. rewrite Hb, Hb'. rewrite (eq_sym x_eq). rewrite (eq_sym T_eq). exact (bndr_CompatibleTypesProofV x m m0 T).
    * right. intros contra. inversion contra. rewrite Hb in H. congruence. rewrite Hb in H. congruence. rewrite Hb in H. congruence.
    * right. intros contra. inversion contra. rewrite Hb in H. congruence. rewrite Hb in H. congruence. rewrite Hb in H. congruence.
    * right. intros contra. inversion contra. rewrite Hb in H. congruence. rewrite Hb in H. congruence. rewrite Hb in H. congruence.
    * destruct b' eqn:Hb' in name_eq. congruence.
      ** assert (h = h0) as h_eq. injection name_eq. tauto. rewrite Hb, Hb'. rewrite (eq_sym h_eq). assert ({n = n0} + {n <> n0}) by apply mode_eq_dec. destruct H as [n_eq|n_neq]. assert ({T = T0} + {T <> T0}) by apply type_eq_dec. destruct H as [T_eq|T_neq]. left. rewrite (eq_sym T_eq). rewrite (eq_sym n_eq). exact (bndr_CompatibleTypesProofD h m n m0 T).
      right. intros contra. inversion contra. congruence. right. intros contra. inversion contra. congruence.
      ** right. intros contra. inversion contra. rewrite Hb in H. congruence. rewrite Hb in H. congruence. rewrite Hb in H. congruence.
    * destruct b' eqn:Hb' in name_eq. congruence.
      ** right. intros contra. inversion contra. rewrite Hb in H. congruence. rewrite Hb in H. congruence. rewrite Hb in H. congruence.
      ** assert (h = h0) as h_eq. injection name_eq. tauto. rewrite Hb, Hb'. rewrite (eq_sym h_eq). assert ({T = T0} + {T <> T0}) by apply type_eq_dec. destruct H as [T_eq|T_neq]. left. rewrite (eq_sym T_eq).  exact (bndr_CompatibleTypesProofH h n n0 T).
      right. intros contra. inversion contra. congruence.
  - right. intros contra. inversion contra. rewrite (eq_sym H) in name_neq. rewrite (eq_sym H0) in name_neq. unfold bndr_name in name_neq. congruence. rewrite (eq_sym H) in name_neq. rewrite (eq_sym H0) in name_neq. unfold bndr_name in name_neq. congruence. rewrite (eq_sym H) in name_neq. rewrite (eq_sym H0) in name_neq. unfold bndr_name in name_neq. congruence.
Qed.

Inductive bndr_IncompatibleTypes : bndr -> bndr -> Type :=
  | bndr_IncompatibleTypesProofV : forall x m1 m2 T1 T2, T1 <> T2 -> bndr_IncompatibleTypes (bndr_V x m1 T1) (bndr_V x m2 T2)
  | bndr_IncompatibleTypesProofD : forall h m11 m12 m21 m22 T1 T2, (type_D T1 m12) <> (type_D T2 m22) -> bndr_IncompatibleTypes (bndr_D h m11 T1 m12) (bndr_D h m21 T2 m22)
  | bndr_IncompatibleTypesProofH : forall h m1 m2 T1 T2, T1 <> T2 -> bndr_IncompatibleTypes (bndr_H h m1 T1) (bndr_H h m2 T2).

Theorem bndr_IncompatibleTypes_dec : forall (b b' : bndr), bndr_IncompatibleTypes b b'+ (notT (bndr_IncompatibleTypes b b')).
Proof. Admitted.

Inductive bndr_Interact : bndr -> bndr -> Type :=
  bndr_InteractProof : forall h m1 m21 m22 T, (m1 = (mode_plus m21 m22)) -> mode_IsLin m1 -> bndr_Interact (bndr_H h m1 T) (bndr_D h m21 T m22). (* case bndr_DestHoleOrHoleDestProofHDInt *)

Inductive bndr_DestHoleOrHoleDest : bndr -> bndr -> Type :=
  | bndr_DestHoleOrHoleDestProofHDInt : forall b b', bndr_Interact b b' -> bndr_DestHoleOrHoleDest b b'
  | bndr_DestHoleOrHoleDestProofHDNoInt : forall h m1 m21 m22 T1 T2, ((m1 <> (mode_plus m21 m22)) + (notT (mode_IsLin m1)) + (T1 <> T2)) -> bndr_DestHoleOrHoleDest (bndr_H h m1 T1) (bndr_D h m21 T2 m22)
  | bndr_DestHoleOrHoleDestProofDH : forall h m11 m12 m2 T1 T2, bndr_DestHoleOrHoleDest (bndr_D h m11 T1 m12) (bndr_H h m2 T2).

Theorem bndr_DestHoleOrHoleDest_dec : forall (b b' : bndr), bndr_DestHoleOrHoleDest b b'+ (notT (bndr_DestHoleOrHoleDest b b')).
Proof. Admitted.

Theorem bndr_AddCases_dec : forall (b b' : bndr), (bndr_name b = bndr_name b') ->
    ((bndr_CompatibleTypes b b' * (notT (bndr_IncompatibleTypes b b')) * (notT (bndr_DestHoleOrHoleDest b b')))
  + ((notT (bndr_CompatibleTypes b b')) * bndr_IncompatibleTypes b b' * (notT (bndr_DestHoleOrHoleDest b b')))
  + ((notT (bndr_CompatibleTypes b b')) * (notT (bndr_IncompatibleTypes b b')) * bndr_DestHoleOrHoleDest b b')).
Proof. Admitted.

Theorem ctx_add (b' : bndr) (G : CtxM.t bndr) : CtxM.t bndr.
Proof.
  destruct (CtxM.find (bndr_name b') G) eqn:Hr.
  * (* Some b *)
    assert (CtxM.MapsTo (bndr_name b') b G). apply CtxM.find_2. exact Hr.
    apply ctx_Coherent in H. destruct (bndr_AddCases_dec b b') as [ [caseComp|caseIncomp]|caseDHHD]. exact H.
    ** destruct caseComp as [ [Comp nIncomp] nDHHD]. destruct Comp.
      (* V *) exact (CtxM.add (name_X x) (bndr_V x (mode_plus m1 m2) T) G).
      (* D *) exact (CtxM.add (name_HD h) (bndr_D h (mode_plus m11 m21) T m2) G).
      (* H *) exact (CtxM.add (name_HD h) (bndr_H h (mode_plus m1 m2) T) G).
    ** destruct caseIncomp as [ [nComp Incomp] nDHHD]. destruct Incomp.
      (* V *) exact (CtxM.add (name_X x) (bndr_V x None T1) G).
      (* D *) exact (CtxM.add (name_HD h) (bndr_D h None T1 m12) G).
      (* H *) exact (CtxM.add (name_HD h) (bndr_H h None T1) G).
    ** destruct caseDHHD as [ [nComp nIncomp] DHHD]. destruct DHHD.
      (* HDInt *) destruct b0. exact (CtxM.add (name_HD h) (bndr_H h None T) G).
      (* HDNoInt *) exact (CtxM.add (name_HD h) (bndr_H h None T1) G).
      (* DH *) exact (CtxM.add (name_HD h) (bndr_D h None T1 m12) G).
  * (* None *)
    exact (CtxM.add (bndr_name b') b' G).
Defined.

Theorem ctx_add_hdint (b':bndr) (G: CtxM.t bndr) : CtxM.t bndr.
Proof.
  destruct (CtxM.find (bndr_name b') G) eqn:Hr.
  * (* Some b *)
    assert (CtxM.MapsTo (bndr_name b') b G). apply CtxM.find_2. exact Hr.
    apply ctx_Coherent in H. destruct (bndr_AddCases_dec b b') as [ [caseComp|caseIncomp]|caseDHHD]. exact H.
    ** destruct caseComp as [ [Comp nIncomp] nDHHD]. destruct Comp.
      (* V *) exact (CtxM.add (name_X x) (bndr_V x (mode_plus m1 m2) T) G).
      (* D *) exact (CtxM.add (name_HD h) (bndr_D h (mode_plus m11 m21) T m2) G).
      (* H *) exact (CtxM.add (name_HD h) (bndr_H h (mode_plus m1 m2) T) G).
    ** destruct caseIncomp as [ [nComp Incomp] nDHHD]. destruct Incomp.
      (* V *) exact (CtxM.add (name_X x) (bndr_V x None T1) G).
      (* D *) exact (CtxM.add (name_HD h) (bndr_D h None T1 m12) G).
      (* H *) exact (CtxM.add (name_HD h) (bndr_H h None T1) G).
    ** destruct caseDHHD as [ [nComp nIncomp] DHHD]. destruct DHHD.
      (* HDInt *) destruct b0. exact (CtxM.remove (name_HD h) G). (* only change compared to ctx_add *)
      (* HDNoInt *) exact (CtxM.add (name_HD h) (bndr_H h None T1) G).
      (* DH *) exact (CtxM.add (name_HD h) (bndr_D h None T1 m12) G).
  * (* None *)
    exact (CtxM.add (bndr_name b') b' G).
Defined.

Definition ctx_from_list (bs : list bndr) : CtxM.t bndr :=
  List.fold_right (fun b G => ctx_add b G) (CtxM.empty bndr) bs.

Definition ctx_union (G1 G2 : CtxM.t bndr) : CtxM.t bndr :=
  (* G1 is acc, G2 is iterated over *)
  CtxM.fold (fun n b G => ctx_add b G) G2 G1.

Definition ctx_interact (G1 G2 : CtxM.t bndr) : CtxM.t bndr :=
  (* G1 is acc, G2 is iterated over *)
  CtxM.fold (fun n b G => ctx_add_hdint b G) G2 G1.

Definition ctx_stimes (m1 : mode) (G : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.map (fun b =>
    match b with
    | bndr_V x m2 T2 => bndr_V x (mode_times m1 m2) T2
    | bndr_D h m2 T2 m3 => bndr_D h (mode_times m1 m2) T2 m3
    | bndr_H h m2 T2 => bndr_H h (mode_times m1 m2) T2
    end
  ) G.

Definition ctx_minus (G : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.map (fun b =>
    match b with
    | bndr_V x m2 T2 => bndr_V x None T2 (* error *)
    | bndr_D h m2 T2 m3 => bndr_H h (mode_times m2 m3) T2
    | bndr_H h m2 T2 => bndr_H h None T2 (* error *)
    end
  ) G.

Definition concat {A : Type} (ll : list (list A)) : list A :=
  List.fold_right (fun x1 x2 => x1 ++ x2) nil ll.


Definition ctx : Type := (CtxM.t bndr).

Inductive term : Type :=  (*r Term *)
 | term_Val (v:val) (*r Value *)
 | term_Var (x:var) (*r Variable *)
 | term_App (t:term) (u:term) (*r Application *)
 | term_PatU (t:term) (u:term) (*r Pattern-match on unit *)
 | term_PatS (t:term) (x1:var) (u1:term) (x2:var) (u2:term) (*r Pattern-match on sum *)
 | term_PatP (t:term) (x1:var) (x2:var) (u:term) (*r Pattern-match on product *)
 | term_PatE (t:term) (m:mode) (x:var) (u:term) (*r Pattern-match on exponential *)
 | term_Map (t:term) (x:var) (u:term) (*r Map over the right side of the ampar *)
 | term_ToA (t:term) (*r Wrap $(t:term)$ into a trivial ampar *)
 | term_FromA (t:term) (*r Extract value from trivial ampar *)
 | term_Alloc (T:type) (*r Return a fresh "identity" ampar object *)
 | term_FillU (t:term) (*r Fill destination with unit *)
 | term_FillL (t:term) (*r Fill destination with left variant *)
 | term_FillR (t:term) (*r Fill destination with right variant *)
 | term_FillP (t:term) (*r Fill destination with product constructor *)
 | term_FillE (t:term) (m:mode) (*r Fill destination with exponential constructor *)
 | term_FillC (t:term) (u:term) (*r Fill destination with root of ampar $(u:term)$ *)
with val : Type :=  (*r Term value *)
 | val_H (h:hdn) (*r Hole *)
 | val_D (h:hdn) (*r Destination *)
 | val_U : val (*r Unit *)
 | val_F (x:var) (t:term) (*r Lambda abstraction *)
 | val_L (v:val) (*r Left variant for sum *)
 | val_R (v:val) (*r Right variant for sum *)
 | val_E (m:mode) (v:val) (*r Exponential *)
 | val_P (v1:val) (v2:val) (*r Product *)
 | val_A (v1:val) (v2:val) (D:ctx) (*r Ampar *).

Inductive hf : Type :=  (*r Hole filling *)
 | hf_F (h:hdn) (v:val) (*r Fill $(h:hdn)$ with value $(v:val)$ (that may contain holes) *).

Definition eff : Type := list hf.
Fixpoint term_sub_name (t: term) (n : name) (v : val) : term := match t with
  | term_Val v' => term_Val (val_sub_name v' n v)
  | term_Var y => match name_eq_dec n (name_X y) with
    | left _ => term_Val v
    | right _ => term_Var y
    end
  | term_App t1 t2 => term_App (term_sub_name t1 n v) (term_sub_name t2 n v)
  | term_PatU t1 t2 => term_PatU (term_sub_name t1 n v) (term_sub_name t2 n v)
  | term_PatS t' x1 u1 x2 u2 =>
    let u1' := match name_eq_dec n (name_X x1) with
      | left _ => (* shadowing *) u1
      | right _ => term_sub_name u1 n v
    end in
    let u2' := match name_eq_dec n (name_X x2) with
      | left _ => (* shadowing *) u2
      | right _ => term_sub_name u2 n v
    end in term_PatS (term_sub_name t' n v) x1 u1' x2 u2'
  | term_PatP t' x1 x2 u => match name_eq_dec n (name_X x1), name_eq_dec n (name_X x2) with
    | right _, right _ => term_PatP (term_sub_name t' n v) x1 x2 (term_sub_name u n v)
    | _, _ => (* at least one shadowing *) term_PatP (term_sub_name t' n v) x1 x2 u
    end
  | term_PatE t' m x' u => let u' := match name_eq_dec n (name_X x') with
      | left _ => (* shadowing *) u
      | right _ => term_sub_name u n v
    end in term_PatE (term_sub_name t' n v) m x' u'
  | term_Map t' x' u => let u' := match name_eq_dec n (name_X x') with
      | left _ => (* shadowing *) u
      | right _ => term_sub_name u n v
    end in term_Map (term_sub_name t' n v) x' u'
  | term_ToA t' => term_ToA (term_sub_name t' n v)
  | term_FromA t' => term_FromA (term_sub_name t' n v)
  | term_Alloc T => term_Alloc T
  | term_FillU t1 => term_FillU (term_sub_name t1 n v)
  | term_FillL t1 => term_FillL (term_sub_name t1 n v)
  | term_FillR t1 => term_FillR (term_sub_name t1 n v)
  | term_FillP t1 => term_FillP (term_sub_name t1 n v)
  | term_FillE t1 m => term_FillE (term_sub_name t1 n v) m
  | term_FillC t u => term_FillC (term_sub_name t n v) (term_sub_name u n v)
end
with val_sub_name (v': val) (n:name) (v:val) : val := match v' with
  | val_F x' u => let u' := match name_eq_dec n (name_X x') with
    | left _ => (* shadowing *) u
    | right _ => term_sub_name u n v
    end in val_F x' u'
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
  | val_A v1 v2 D => val_A (val_sub_name v1 n v) (val_sub_name v2 n v) D
end.

Definition term_sub (t: term) (x:var) (v:val) : term := term_sub_name t (name_X x) v.
Definition val_hfill (v' : val) (f : hf) : val := match f with
  | hf_F h v => val_sub_name v' (name_HD h) v
  end.


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
 | _mode_IsValid (m:mode)
 | _mode_IsLin (m:mode)
 | _mode_IsUr (m:mode)
 | _ctx_Disjoint (G1:ctx) (G2:ctx) (*r TODO: Just for legacy proof; remove *)
 | _TyR_eff (G:ctx) (e:eff)
 | _TyR_term (G:ctx) (t:term) (T:type)
 | _Ty_eff (G:ctx) (e:eff)
 | _Ty_term (G:ctx) (t:term) (T:type)
 | _Ty_cmd (G:ctx) (v:val) (e:eff) (T:type)
 | _Sem_eff (v1:val) (D1:ctx) (e1:eff) (v2:val) (D2:ctx) (e2:eff)
 | _Sem_term (t:term) (d:hddyn) (v:val) (e:eff).
(** definitions *)

(* defns Ty *)
Inductive TyR_eff : ctx -> eff -> Prop :=    (* defn TyR_eff *)
 | TyR_eff_N : 
     TyR_eff  (ctx_from_list  nil )   nil 
 | TyR_eff_A : forall (m n:mode) (G:ctx) (h:hdn) (T:type) (D:ctx) (v:val)
     (TYRv: TyR_term  (ctx_union  G   D )  (term_Val v) T),
     ctx_DestOnly G  ->
     ctx_HoleOnly D  ->
     mode_IsValid m  ->
     mode_IsValid n  ->
     TyR_eff  (ctx_union   (ctx_union   (ctx_stimes    (mode_times'  ((app (cons  (Some (pair   Lin     (Fin 1)  ))  nil) (app (cons m nil) (app (cons n nil) nil)))) )     G )     (ctx_from_list  (cons (bndr_D h m T n) nil) )  )     (ctx_stimes    (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )     D )  )   (cons  (hf_F h v)  nil) 
 | TyR_eff_C : forall (G1 G2:ctx) (e1 e2:eff)
     (TYRe1: TyR_eff G1 e1)
     (TYRe2: TyR_eff G2 e2),
     TyR_eff  (ctx_interact  G1   G2 )   (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
with Ty_eff : ctx -> eff -> Prop :=    (* defn Ty_eff *)
 | Ty_eff_T : forall (G:ctx) (e:eff)
     (TYRe: TyR_eff G e),
     ctx_IsValid G  ->
     Ty_eff G e
with TyR_term : ctx -> term -> type -> Prop :=    (* defn TyR_term *)
 | TyR_term_H : forall (h:hdn) (T:type),
     TyR_term  (ctx_from_list  (cons (bndr_H h  (Some (pair   Lin     (Fin 0)  ))  T) nil) )  (term_Val (val_H h)) T
 | TyR_term_D : forall (h:hdn) (T:type) (n:mode),
     TyR_term  (ctx_from_list  (cons (bndr_D h  (Some (pair   Lin     (Fin 0)  ))  T n) nil) )  (term_Val (val_D h)) (type_D T n)
 | TyR_term_U : 
     TyR_term  (ctx_from_list  nil )  (term_Val val_U) type_U
 | TyR_term_L : forall (G:ctx) (v:val) (T1 T2:type)
     (TYRv: TyR_term G (term_Val v) T1),
     TyR_term G (term_Val (val_L v)) (type_S T1 T2)
 | TyR_term_R : forall (G:ctx) (v:val) (T1 T2:type)
     (TYRv: TyR_term G (term_Val v) T2),
     TyR_term G (term_Val (val_R v)) (type_S T1 T2)
 | TyR_term_P : forall (G1 G2:ctx) (v1 v2:val) (T1 T2:type)
     (TYRv1: TyR_term G1 (term_Val v1) T1)
     (TYRv2: TyR_term G2 (term_Val v2) T2),
     TyR_term  (ctx_union  G1   G2 )  (term_Val (val_P v1 v2)) (type_P T1 T2)
 | TyR_term_E : forall (m:mode) (G:ctx) (v:val) (T:type)
     (TYRv: TyR_term G (term_Val v) T),
     mode_IsValid m  ->
     TyR_term  (ctx_stimes  m   G )  (term_Val (val_E m v)) (type_E m T)
 | TyR_term_A : forall (G1 G2:ctx) (v1 v2:val) (T1 T2:type)
     (TYRv1: TyR_term G1 (term_Val v1) T1)
     (TYRv2: TyR_term G2 (term_Val v2) T2),
     ctx_DestOnly G2  ->
     ctx_SubsetEq  (ctx_minus  G2 )  G1  ->
     TyR_term  (ctx_interact  G1   G2 )  (term_Val (val_A v1 v2  (ctx_minus  G2 ) )) (type_A T1 T2)
 | TyR_term_F : forall (G:ctx) (x:var) (t:term) (T1:type) (m:mode) (T2:type)
     (TYt: TyR_term  (ctx_union  G    (ctx_from_list  (cons (bndr_V x m T1) nil) )  )  t T2),
     mode_IsValid m  ->
     TyR_term G (term_Val (val_F x t)) (type_F T1 m T2)
 | TyR_term_Var : forall (G:ctx) (x:var) (T:type),
     ctx_Compatible G (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T)  ->
     TyR_term G (term_Var x) T
 | TyR_term_App : forall (m:mode) (G1 G2:ctx) (t u:term) (T2 T1:type)
     (TYt: TyR_term G1 t T1)
     (TYu: TyR_term G2 u (type_F T1 m T2)),
     mode_IsValid m  ->
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_App t u) T2
 | TyR_term_PatU : forall (G1 G2:ctx) (t u:term) (U:type)
     (TYt: TyR_term G1 t type_U)
     (TYu: TyR_term G2 u U),
     TyR_term  (ctx_union  G1   G2 )  (term_PatU t u) U
 | TyR_term_PatS : forall (m:mode) (G1 G2:ctx) (t:term) (x1:var) (u1:term) (x2:var) (u2:term) (U T1 T2:type)
     (TYt: TyR_term G1 t (type_S T1 T2))
     (TYu1: TyR_term  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x1 m T1) nil) )  )  u1 U)
     (TYu2: TyR_term  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x2 m T2) nil) )  )  u2 U),
     mode_IsValid m  ->
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_PatS t x1 u1 x2 u2) U
 | TyR_term_PatP : forall (m:mode) (G1 G2:ctx) (t:term) (x1 x2:var) (u:term) (U T1 T2:type)
     (TYt: TyR_term G1 t (type_P T1 T2))
     (TYu: TyR_term  (ctx_union  G2    (ctx_from_list  ((app (cons (bndr_V x1 m T1) nil) (app (cons (bndr_V x2 m T2) nil) nil))) )  )  u U),
     mode_IsValid m  ->
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_PatP t x1 x2 u) U
 | TyR_term_PatE : forall (m:mode) (G1 G2:ctx) (t:term) (n:mode) (x:var) (u:term) (U T:type)
     (TYt: TyR_term G1 t (type_E n T))
     (TYu: TyR_term  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )  T) nil) )  )  u U),
     mode_IsValid m  ->
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_PatE t n x u) U
 | TyR_term_Map : forall (G1 G2:ctx) (t:term) (x:var) (u:term) (T1 U:type) (m:mode) (T2:type)
     (TYt: TyR_term G1 t (type_A T1 T2))
     (TYu: TyR_term  (ctx_union   (ctx_stimes   (Some (pair   Lin     (Fin 1)  ))    G2 )     (ctx_from_list  (cons (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T2) nil) )  )  u U),
     mode_IsValid m  ->
     TyR_term  (ctx_union  G1   G2 )  (term_Map t x u) (type_A T1 U)
 | TyR_term_FillC : forall (G1:ctx) (n:mode) (G2:ctx) (t u:term) (T2 T1:type)
     (TYt: TyR_term G1 t (type_D T1 n))
     (TYu: TyR_term G2 u (type_A T1 T2)),
     mode_IsValid n  ->
     TyR_term  (ctx_union  G1    (ctx_stimes    (mode_times'  ((app (cons  (Some (pair   Lin     (Fin 1)  ))  nil) (app (cons n nil) nil))) )     G2 )  )  (term_FillC t u) T2
 | TyR_term_FillU : forall (G:ctx) (t:term) (n:mode)
     (TYt: TyR_term G t (type_D type_U n)),
     TyR_term G (term_FillU t) type_U
 | TyR_term_FillL : forall (G:ctx) (t:term) (T1:type) (n:mode) (T2:type)
     (TYt: TyR_term G t (type_D (type_S T1 T2) n)),
     TyR_term G (term_FillL t) (type_D T1 n)
 | TyR_term_FillR : forall (G:ctx) (t:term) (T2:type) (n:mode) (T1:type)
     (TYt: TyR_term G t (type_D (type_S T1 T2) n)),
     TyR_term G (term_FillR t) (type_D T2 n)
 | TyR_term_FillP : forall (G:ctx) (t:term) (T1:type) (n:mode) (T2:type)
     (TYt: TyR_term G t (type_D (type_P T1 T2) n)),
     TyR_term G (term_FillP t) (type_P (type_D T1 n) (type_D T2 n))
 | TyR_term_FillE : forall (G:ctx) (t:term) (n:mode) (T:type) (m:mode)
     (TYt: TyR_term G t (type_D (type_E n T) m)),
     TyR_term G (term_FillE t n) (type_D T  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) ) )
 | TyR_term_Alloc : forall (T:type),
     TyR_term  (ctx_from_list  nil )  (term_Alloc T) (type_A T (type_D T  (Some (pair   Lin     (Fin 0)  )) ))
 | TyR_term_ToA : forall (G:ctx) (t:term) (T:type)
     (TYt: TyR_term G t T),
     TyR_term G (term_ToA t) (type_A T type_U)
 | TyR_term_FromA : forall (G:ctx) (t:term) (T:type)
     (TYt: TyR_term G t (type_A T type_U)),
     TyR_term G (term_FromA t) T
with Ty_term : ctx -> term -> type -> Prop :=    (* defn Ty_term *)
 | Ty_term_T : forall (G:ctx) (t:term) (T:type)
     (TYt: TyR_term G t T),
     ctx_IsValid G  ->
     ctx_NoHole G  ->
     Ty_term G t T
with Ty_cmd : ctx -> val -> eff -> type -> Prop :=    (* defn Ty_cmd *)
 | Ty_cmd_C : forall (G1 G2:ctx) (v:val) (e:eff) (T:type)
     (TYe: Ty_eff G1 e)
     (TYv: Ty_term G2 (term_Val v) T),
     ctx_DestOnly  (ctx_interact  G1   G2 )   ->
     Ty_cmd  (ctx_interact  G1   G2 )  v e T.
(** definitions *)

(* defns Sem *)
Inductive Sem_eff : val -> ctx -> eff -> val -> ctx -> eff -> Prop :=    (* defn Sem_eff *)
 | Sem_eff_N : forall (v1:val) (G1:ctx),
     Sem_eff v1 G1  nil  v1 G1  nil 
 | Sem_eff_S : forall (v1:val) (G1:ctx) (h:hdn) (v':val) (e1:eff) (v2:val) (G2:ctx) (e2:eff)
     (EAPPv1e1: Sem_eff v1 G1 e1 v2 G2 e2),
     ctx_HdnmNotMem h G1  ->
     Sem_eff v1 G1  (concat  ((app (cons  (cons  (hf_F h v')  nil)  nil) (app (cons e1 nil) nil))) )  v2 G2  (concat  ((app (cons  (cons  (hf_F h v')  nil)  nil) (app (cons e2 nil) nil))) ) 
 | Sem_eff_F : forall (v1:val) (G1:ctx) (h:hdn) (n:mode) (T:type) (v0:val) (e1:eff) (v2:val) (G2:ctx) (e2:eff) (G0:ctx)
     (TYRv0: TyR_term G0 (term_Val v0) T)
     (EAPPv1sube1: Sem_eff  (val_hfill  v1   (hf_F h v0) )    (ctx_union  G1    (ctx_stimes  n   G0 )  )   e1 v2 G2 e2),
     mode_IsValid n  ->
     ctx_IsValid G0  ->
     Sem_eff v1  (ctx_union  G1    (ctx_from_list  (cons (bndr_H h n T) nil) )  )   (concat  ((app (cons  (cons  (hf_F h v0)  nil)  nil) (app (cons e1 nil) nil))) )  v2 G2 e2
with Sem_term : term -> hddyn -> val -> eff -> Prop :=    (* defn Sem_term *)
 | Sem_term_V : forall (v:val) (d:hddyn),
     Sem_term (term_Val v) d v  nil 
 | Sem_term_App : forall (t1 t2:term) (d:hddyn) (v3:val) (e1 e2 e3:eff) (v1:val) (x:var) (u:term)
     (REDt1: Sem_term t1  ( d  ++ (cons 1 nil))  v1 e1)
     (REDt2: Sem_term t2  ( d  ++ (cons 2 nil))  (val_F x u) e2)
     (REDusub: Sem_term  (term_sub  u   x   v1 )   ( d  ++ (cons 3 nil))  v3 e3),
     Sem_term (term_App t1 t2) d v3  (concat  ((app (cons e1 nil) (app (cons e2 nil) (app (cons e3 nil) nil)))) ) 
 | Sem_term_PatU : forall (t1 t2:term) (d:hddyn) (v2:val) (e1 e2:eff)
     (REDt1: Sem_term t1  ( d  ++ (cons 1 nil))  val_U e1)
     (REDt2: Sem_term t2  ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatU t1 t2) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_PatL : forall (t:term) (x1:var) (u1:term) (x2:var) (u2:term) (d:hddyn) (v2:val) (e1 e2:eff) (v1:val)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_L v1) e1)
     (REDu1sub: Sem_term  (term_sub  u1   x1   v1 )   ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatS t x1 u1 x2 u2) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_PatR : forall (t:term) (x1:var) (u1:term) (x2:var) (u2:term) (d:hddyn) (v2:val) (e1 e2:eff) (v1:val)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_R v1) e1)
     (REDu2sub: Sem_term  (term_sub  u2   x2   v1 )   ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatS t x1 u1 x2 u2) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_PatP : forall (t:term) (x1 x2:var) (u:term) (d:hddyn) (v2:val) (e1 e2:eff) (v1:val)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_P v1 v2) e1)
     (REDusub: Sem_term  (term_sub   (term_sub  u   x1   v1 )    x2   v2 )   ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatP t x1 x2 u) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_Map : forall (t:term) (x:var) (u:term) (d:hddyn) (v3 v4:val) (D':ctx) (e1 e3:eff) (v1 v2:val) (D:ctx) (e2:eff)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_A v1 v2 D) e1)
     (REDusub: Sem_term  (term_sub  u   x   v1 )   ( d  ++ (cons 2 nil))  v3 e2)
     (EAPPv2e2: Sem_eff v2 D e2 v4 D' e3),
     Sem_term (term_Map t x u) d (val_A v3 v4 D')  (concat  ((app (cons e1 nil) (app (cons e3 nil) nil))) ) 
 | Sem_term_Alloc : forall (T:type) (d:hddyn),
     Sem_term (term_Alloc T) d (val_A (val_D (hdn_D d)) (val_H (hdn_D d))  (ctx_from_list  (cons (bndr_H (hdn_D d)  (Some (pair   Lin     (Fin 0)  ))  T) nil) ) )  nil 
 | Sem_term_ToA : forall (t:term) (d:hddyn) (v:val) (e:eff)
     (REDt: Sem_term t d v e),
     Sem_term (term_ToA t) d (val_A val_U v  (ctx_from_list  nil ) ) e
 | Sem_term_FromA : forall (t:term) (d:hddyn) (v:val) (e:eff)
     (REDt: Sem_term t d (val_A val_U v  (ctx_from_list  nil ) ) e),
     Sem_term (term_FromA t) d v e
 | Sem_term_FillU : forall (t:term) (d:hddyn) (e:eff) (h:hdn)
     (REDt: Sem_term t d (val_D h) e),
     Sem_term (term_FillU t) d val_U  (concat  ((app (cons e nil) (app (cons  (cons  (hf_F h val_U)  nil)  nil) nil))) ) 
 | Sem_term_FillL : forall (t:term) (d:hddyn) (e:eff) (h:hdn)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e),
     Sem_term (term_FillL t) d (val_D (hdn_D  ( d  ++ (cons 2 nil)) ))  (concat  ((app (cons e nil) (app (cons  (cons  (hf_F h (val_L (val_H (hdn_D  ( d  ++ (cons 2 nil)) ))))  nil)  nil) nil))) ) 
 | Sem_term_FillR : forall (t:term) (d:hddyn) (e:eff) (h:hdn)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e),
     Sem_term (term_FillR t) d (val_D (hdn_D  ( d  ++ (cons 2 nil)) ))  (concat  ((app (cons e nil) (app (cons  (cons  (hf_F h (val_R (val_H (hdn_D  ( d  ++ (cons 2 nil)) ))))  nil)  nil) nil))) ) 
 | Sem_term_FillP : forall (t:term) (d:hddyn) (e:eff) (h:hdn)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e),
     Sem_term (term_FillP t) d (val_P (val_D (hdn_D  ( d  ++ (cons 2 nil)) )) (val_D (hdn_D  ( d  ++ (cons 3 nil)) )))  (concat  ((app (cons e nil) (app (cons  (cons  (hf_F h (val_P (val_H (hdn_D  ( d  ++ (cons 2 nil)) )) (val_H (hdn_D  ( d  ++ (cons 3 nil)) ))))  nil)  nil) nil))) ) 
 | Sem_term_FillC : forall (t u:term) (d:hddyn) (v1:val) (e1 e2:eff) (h:hdn) (v2:val) (D:ctx)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e1)
     (REDu: Sem_term u  ( d  ++ (cons 2 nil))  (val_A v1 v2 D) e2),
     Sem_term (term_FillC t u) d v1  (concat  ((app (cons e1 nil) (app (cons e2 nil) (app (cons  (cons  (hf_F h v2)  nil)  nil) nil)))) ) .



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

Definition tmv : Type := nat. (*r Term-level variable name *)
Definition hdmv : Type := nat. (*r Hole or destination static name *)
Definition k : Type := nat. (*r Index for ranges *)

Definition hddyn : Type := list nat.

Inductive hdnm : Type :=  (*r Hole or destination name *)
 | hdnm_D (d:hddyn) (*r Dynamic name *)
 | hdnm_S (hdmv5:hdmv) (*r Static name *).
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

(* Astuce fresh : liste de nombres = prefixe *)


Definition mul : Type := _mul.

Definition age : Type := ext_nat.

Definition mode : Type := option (mul * age).

Inductive type : Type :=  (*r Type *)
 | type_U : type (*r Unit *)
 | type_S (T1:type) (T2:type) (*r Sum *)
 | type_P (T1:type) (T2:type) (*r Product *)
 | type_E (m:mode) (T:type) (*r Exponential *)
 | type_A (T1:type) (T2:type) (*r Ampar type (consuming $(T1:type)$ yields $(T2:type)$) *)
 | type_F (T1:type) (m1:mode) (T2:type) (*r Linear function *)
 | type_D (m:mode) (T:type) (*r Destination *).

Inductive bndr : Type :=  (*r Type assignment to either variable, destination or hole *)
 | bndr_V (x:tmv) (m:mode) (T:type) (*r Variable *)
 | bndr_D (h:hdnm) (m:mode) (n:mode) (T:type) (*r Destination ($(m:mode)$ is its own modality; $(n:mode)$ is the modality for values it accepts) *)
 | bndr_H (h:hdnm) (n:mode) (T:type) (*r Hole ($(n:mode)$ is the modality for values it accepts, it doesn't have a modality on its own) *).
Inductive name : Type :=
  | name_X : tmv -> name
  | name_HD : hdnm -> name.

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
        + assert ({t0 = t1} + {t0 <> t1}) by apply Nat.eq_dec. destruct H.
           * left. rewrite e. reflexivity.
           * right. congruence.
        + right. congruence.
    - induction y. give_up.
    Admitted.

  Instance eq_equiv : Equivalence Name_as_UDT.eq. split. exact eq_refl. exact eq_sym. exact eq_trans. Defined.

End Name_as_UDT.

Module Name_as_UDTOrig := Backport_DT(Name_as_UDT).
Module CtxM := FMapWeakList.Make(Name_as_UDTOrig).

Definition age_times (a1 a2 : age) : age := ext_plus a1 a2.
Definition age_times' (al: list age) : age := ext_plus' al.

Definition mode_plus (m1 m2: mode) : mode :=
  match m1, m2 with
  | None, _ => None
  | _, None => None
  | Some (p1, a1), Some (p2, a2) => match a1, a2 with
    | _, Inf => Some (mul_plus p1 p2, Inf)
    | Inf, _ => Some (mul_plus p1 p2, Inf)
    | _, _ => if a1 = a2 then Some (mul_plus p1 p2, a1) else None
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

Definition bndr_name (b : bndr) : name :=
  match b with
  | bndr_V x m T => name_X x
  | bndr_H h m T => name_HD h
  | bndr_D h m1 m2 T => name_HD h
  end.

Definition bndr_mode (b : bndr) : mode := match b with
  | bndr_V _ m _ => m
  | bndr_H _ m _ => m
  | bndr_D _ m1 m2 _ => m1
  end.

Definition bndr_update_mode (b:bndr) (m:mode) := match b with
  | bndr_V x _ T => bndr_V x m T
  | bndr_H h _ T => bndr_H h m T
  | bndr_D h _ m2 T => bndr_D h m m2 T
  end.

Definition bndr_IsDest (b: bndr) : Prop :=
  match b with
    | bndr_D _ _ _ _ => True
    | _ => False
  end.
Definition bndr_IsVar (b: bndr) : Prop :=
  match b with
    | bndr_V _ _ _ => True
    | _ => False
  end.
Definition bndr_IsHole (b: bndr) : Prop :=
  match b with
    | bndr_H _ _ _ => True
    | _ => False
  end.
Definition ctx_DestOnly (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> bndr_IsDest b.
Definition ctx_HoleOnly (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> bndr_IsHole b.
Definition ctx_VarOnly (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> bndr_IsVar b.
Definition ctx_NoDest (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> ~bndr_IsDest b.
Definition ctx_NoHole (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> ~bndr_IsHole b.
Definition ctx_NoVar (G : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> ~bndr_IsVar b.
Definition ctx_Valid (G: CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G -> exists m, bndr_mode b = Some m.
Definition ctx_SubsetEq (G1 G2 : CtxM.t bndr) : Prop :=
  forall n b, CtxM.MapsTo n b G1 -> CtxM.MapsTo n b G2.
Definition ctx_HdnmNotMem (h : hdnm) (G : CtxM.t bndr) : Prop :=
  ~CtxM.In (name_HD h) G.
Definition ctx_Compatible (G1 G2 : CtxM.t bndr) : Prop := True. (* TODO : define *)

Axiom ctx_Coherent: forall (G : CtxM.t bndr) n b, CtxM.MapsTo n b G -> bndr_name b = n.

Definition ctx_add (b' : bndr) (G : CtxM.t bndr) : CtxM.t bndr :=
  match CtxM.find (bndr_name b') G with
  | None => CtxM.add (bndr_name b') b' G
  | Some b => match b, b' with
    | bndr_V x1 m1 T1, bndr_V x2 m2 T2 =>
      (* assert x1 = x2 *)
      if T1 = T2 then bndr_V x1 (mode_plus m1 m2) T1 else bndr_update_mode b None
    | bndr_D h1 m11 m12 T1, bndr_D h2 m21 m22 T2 =>
      (* assert h1 = h2 *)
      if m12 = m22 and T1 = T2 then bndr_D h1 (mode_plus m11 m21) m12 T1 else bndr_update_mode b None
    | bndr_H h1 m1 T1, bndr_H h2 m2 T2 =>
      (* assert h1 = h2 *)
      if T1 = T2 then bndr_D h1 (mode_plus m1 m2) T1 else bndr_update_mode b None
    | _, _ => bndr_update_mode b None
    end
  end.

Definition ctx_interact (b':bndr) (G: CtxM.t bndr) : CtxM.t bndr :=
  let fallback = ctx_add b' G in
  match CtxM.find (bndr_name b') G with
  | None => fallback
  | Some b => match b, b' with
    | bndr_D h1 m11 m12 T1, bndr_H h2 m2 T2 =>
      (* assert h1 = h2 *)
      if (mode_plus m11 m12) = m2 and T1 = T2 then G else fallback
    | bndr_H h2 m2 T2, bndr_D h1 m11 m12 T1 =>
      (* assert h1 = h2 *)
      if (mode_plus m11 m12) = m2 and T1 = T2 then G else fallback
    | _, _ => fallback
    end
  end.

Definition ctx_from_list (bs : list bndr) : CtxM.t bndr :=
  List.fold_right (fun b G => CtxM.add (bndr_name b) b G) (CtxM.empty bndr) bs.

Definition ctx_union (G1 G2 : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.fold (fun n b G => CtxM.add n b G) G2 G1.

Definition ctx_stimes (m1 : mode) (G : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.map (fun b =>
    match b with
    | bndr_V x m2 T2 => bndr_V x (mode_times m1 m2) T2
    | bndr_D h m2 m3 T2 => bndr_D h (mode_times m1 m2) m3 T2
    | bndr_H h m2 T2 => bndr_H h (mode_times m1 m2) T2
    end
  ) G.

Definition ctx_minus (G : CtxM.t bndr) : CtxM.t bndr :=
  CtxM.map (fun b =>
    match b with
    | bndr_V x m2 T2 => bndr_V x None T2 (* error *)
    | bndr_D h m2 m3 T2 => bndr_H h (mode_times m2 m3) T2
    | bndr_H h m2 T2 => bndr_H h None T2 (* error *)
    end
  ) G.

Definition concat {A : Type} (ll : list (list A)) : list A :=
  List.fold_right (fun x1 x2 => x1 ++ x2) nil ll.


Definition ctx : Type := (CtxM.t bndr).

Inductive term : Type :=  (*r Term *)
 | term_Val (v:val) (*r Term value *)
 | term_Var (x:tmv) (*r Variable *)
 | term_App (t:term) (u:term) (*r Application *)
 | term_PatU (t:term) (u:term) (*r Pattern-match on unit *)
 | term_PatS (t:term) (x1:tmv) (u1:term) (x2:tmv) (u2:term) (*r Pattern-match on sum *)
 | term_PatP (t:term) (x1:tmv) (x2:tmv) (u:term) (*r Pattern-match on product *)
 | term_PatE (t:term) (m:mode) (x:tmv) (u:term) (*r Pattern-match on exponential *)
 | term_Map (t:term) (x:tmv) (u:term) (*r Map over the left side of the ampar *)
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
 | val_H (h:hdnm) (*r Hole *)
 | val_D (h:hdnm) (*r Destination *)
 | val_U : val (*r Unit *)
 | val_F (x:tmv) (t:term) (*r Linear function *)
 | val_L (v:val) (*r Left variant for sum *)
 | val_R (v:val) (*r Right variant for sum *)
 | val_E (m:mode) (v:val) (*r Exponential *)
 | val_P (v1:val) (v2:val) (*r Product *)
 | val_A (v1:val) (v2:val) (D:ctx) (*r Ampar *).

Inductive has : Type :=  (*r Hole assignment *)
 | has_A (h:hdnm) (v:val).

Definition eff : Type := list has.
Definition term_sub (t: term) (x : tmv) (v : val) : term := t.
(* TODO *)
Definition val_effapp (v : val) (e : eff) : val := v.
(* TODO *)


Inductive pred : Type :=  (*r Serves for the .mng file. Isn't used in the actual rules *)
 | _ctx_DestOnly (G:ctx)
 | _ctx_HoleOnly (G:ctx)
 | _ctx_VarOnly (G:ctx)
 | _ctx_NoDest (G:ctx)
 | _ctx_NoHole (G:ctx)
 | _ctx_NoVar (G:ctx)
 | _ctx_Valid (G:ctx)
 | _ctx_SubsetEq (G1:ctx) (G2:ctx)
 | _ctx_HdnmNotMem (h:hdnm) (G:ctx)
 | _ctx_Compatible (G1:ctx) (G2:ctx)
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
 | TyR_eff_A : forall (m n:mode) (G:ctx) (h:hdnm) (T:type) (D:ctx) (v:val)
     (TYRv: TyR_term  (ctx_union  G   D )  (term_Val v) T),
     ctx_DestOnly G  ->
     ctx_HoleOnly D  ->
     TyR_eff  (ctx_union   (ctx_union   (ctx_stimes    (mode_times'  ((app (cons  (Some (pair   Lin     (Fin 1)  ))  nil) (app (cons m nil) (app (cons n nil) nil)))) )     G )     (ctx_from_list  (cons (bndr_D h m n T) nil) )  )     (ctx_stimes    (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )     D )  )   (cons  (has_A h v)  nil) 
 | TyR_eff_C : forall (G1 G2:ctx) (e1 e2:eff)
     (TYRe1: TyR_eff G1 e1)
     (TYRe2: TyR_eff G2 e2),
     TyR_eff  (ctx_interact  G1   G2 )   (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
with Ty_eff : ctx -> eff -> Prop :=    (* defn Ty_eff *)
 | Ty_eff_T : forall (G:ctx) (e:eff)
     (TYRe: TyR_eff G e),
     ctx_Valid G  ->
     Ty_eff G e
with TyR_term : ctx -> term -> type -> Prop :=    (* defn TyR_term *)
 | TyR_term_H : forall (h:hdnm) (T:type),
     TyR_term  (ctx_from_list  (cons (bndr_H h  (Some (pair   Lin     (Fin 0)  ))  T) nil) )  (term_Val (val_H h)) T
 | TyR_term_D : forall (h:hdnm) (n:mode) (T:type),
     TyR_term  (ctx_from_list  (cons (bndr_D h  (Some (pair   Lin     (Fin 0)  ))  n T) nil) )  (term_Val (val_D h)) (type_D n T)
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
     TyR_term  (ctx_stimes  m   G )  (term_Val (val_E m v)) (type_E m T)
 | TyR_term_A : forall (G1 G2:ctx) (v1 v2:val) (T1 T2:type)
     (TYRv1: TyR_term G1 (term_Val v1) T1)
     (TYRv2: TyR_term G2 (term_Val v2) T2),
     ctx_DestOnly G1  ->
     ctx_SubsetEq  (ctx_minus  G1 )  G2  ->
     TyR_term  (ctx_interact  G1   G2 )  (term_Val (val_A v1 v2  (ctx_minus  G1 ) )) (type_A T1 T2)
 | TyR_term_F : forall (G:ctx) (x:tmv) (t:term) (T1:type) (m:mode) (T2:type)
     (TYRt: TyR_term  (ctx_union  G    (ctx_from_list  (cons (bndr_V x m T1) nil) )  )  t T2),
     TyR_term G (term_Val (val_F x t)) (type_F T1 m T2)
 | TyR_term_Var : forall (G:ctx) (x:tmv) (T:type),
     ctx_Compatible G  (ctx_from_list  (cons (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T) nil) )   ->
     TyR_term G (term_Var x) T
 | TyR_term_App : forall (m:mode) (G1 G2:ctx) (t u:term) (T2 T1:type)
     (TYRt: TyR_term G1 t T1)
     (TYRu: TyR_term G2 u (type_F T1 m T2)),
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_App t u) T2
 | TyR_term_PatU : forall (G1 G2:ctx) (t u:term) (U:type)
     (TYRt: TyR_term G1 t type_U)
     (TYRu: TyR_term G2 u U),
     TyR_term  (ctx_union  G1   G2 )  (term_PatU t u) U
 | TyR_term_PatS : forall (m:mode) (G1 G2:ctx) (t:term) (x1:tmv) (u1:term) (x2:tmv) (u2:term) (U T1 T2:type)
     (TYRt: TyR_term G1 t (type_S T1 T2))
     (TYRu1: TyR_term  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x1 m T1) nil) )  )  u1 U)
     (TYRu2: TyR_term  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x2 m T2) nil) )  )  u2 U),
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_PatS t x1 u1 x2 u2) U
 | TyR_term_PatP : forall (m:mode) (G1 G2:ctx) (t:term) (x1 x2:tmv) (u:term) (U T1 T2:type)
     (TYRt: TyR_term G1 t (type_P T1 T2))
     (TYRu: TyR_term  (ctx_union  G2    (ctx_from_list  ((app (cons (bndr_V x1 m T1) nil) (app (cons (bndr_V x2 m T2) nil) nil))) )  )  u U),
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_PatP t x1 x2 u) U
 | TyR_term_PatE : forall (m:mode) (G1 G2:ctx) (t:term) (n:mode) (x:tmv) (u:term) (U T:type)
     (TYRt: TyR_term G1 t (type_E n T))
     (TYRu: TyR_term  (ctx_union  G2    (ctx_from_list  (cons (bndr_V x  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )  T) nil) )  )  u U),
     TyR_term  (ctx_union   (ctx_stimes  m   G1 )    G2 )  (term_PatE t n x u) U
 | TyR_term_Map : forall (G1 G2:ctx) (t:term) (x:tmv) (u:term) (U T2 T1:type)
     (TYRt: TyR_term G1 t (type_A T1 T2))
     (TYRu: TyR_term  (ctx_union   (ctx_stimes   (Some (pair   Lin     (Fin 1)  ))    G2 )     (ctx_from_list  (cons (bndr_V x  (Some (pair   Lin     (Fin 0)  ))  T1) nil) )  )  u U),
     TyR_term  (ctx_union  G1   G2 )  (term_Map t x u) (type_A U T2)
 | TyR_term_FillC : forall (G1:ctx) (n:mode) (G2:ctx) (t u:term) (T1 T2:type)
     (TYRt: TyR_term G1 t (type_D n T2))
     (TYRu: TyR_term G2 u (type_A T1 T2)),
     TyR_term  (ctx_union  G1    (ctx_stimes    (mode_times'  ((app (cons  (Some (pair   Lin     (Fin 1)  ))  nil) (app (cons n nil) nil))) )     G2 )  )  (term_FillC t u) T1
 | TyR_term_FillU : forall (G:ctx) (t:term) (n:mode)
     (TYRt: TyR_term G t (type_D n type_U)),
     TyR_term G (term_FillU t) type_U
 | TyR_term_FillL : forall (G:ctx) (t:term) (n:mode) (T1 T2:type)
     (TYRt: TyR_term G t (type_D n (type_S T1 T2))),
     TyR_term G (term_FillL t) (type_D n T1)
 | TyR_term_FillR : forall (G:ctx) (t:term) (n:mode) (T2 T1:type)
     (TYRt: TyR_term G t (type_D n (type_S T1 T2))),
     TyR_term G (term_FillR t) (type_D n T2)
 | TyR_term_FillP : forall (G:ctx) (t:term) (n:mode) (T1 T2:type)
     (TYRt: TyR_term G t (type_D n (type_P T1 T2))),
     TyR_term G (term_FillP t) (type_P (type_D n T1) (type_D n T2))
 | TyR_term_FillE : forall (G:ctx) (t:term) (n m:mode) (T:type)
     (TYRt: TyR_term G t (type_D m (type_E n T))),
     TyR_term G (term_FillE t n) (type_D  (mode_times'  ((app (cons m nil) (app (cons n nil) nil))) )  T)
 | TyR_term_Alloc : forall (T:type),
     TyR_term  (ctx_from_list  nil )  (term_Alloc T) (type_A (type_D  (Some (pair   Lin     (Fin 0)  ))  T) T)
 | TyR_term_ToA : forall (G:ctx) (t:term) (T:type)
     (TYRt: TyR_term G t T),
     TyR_term G (term_ToA t) (type_A type_U T)
 | TyR_term_FromA : forall (G:ctx) (t:term) (T:type)
     (TYRt: TyR_term G t (type_A type_U T)),
     TyR_term G (term_FromA t) T
with Ty_term : ctx -> term -> type -> Prop :=    (* defn Ty_term *)
 | Ty_term_T : forall (G:ctx) (t:term) (T:type)
     (TYRt: TyR_term G t T),
     ctx_Valid G  ->
     ctx_NoHole G  ->
     Ty_term G t T
with Ty_cmd : ctx -> val -> eff -> type -> Prop :=    (* defn Ty_cmd *)
 | Ty_cmd_C : forall (G1 G2:ctx) (v:val) (e:eff) (T:type)
     (TYv: Ty_term G1 (term_Val v) T)
     (TYe: Ty_eff G2 e),
     ctx_DestOnly  (ctx_interact  G1   G2 )   ->
     Ty_cmd  (ctx_interact  G1   G2 )  v e T.
(** definitions *)

(* defns Sem *)
Inductive Sem_eff : val -> ctx -> eff -> val -> ctx -> eff -> Prop :=    (* defn Sem_eff *)
 | Sem_eff_N : forall (v1:val) (G1:ctx),
     Sem_eff v1 G1  nil  v1 G1  nil 
 | Sem_eff_S : forall (v1:val) (G1:ctx) (h:hdnm) (v':val) (e1:eff) (v2:val) (G2:ctx) (e2:eff)
     (EAPPv1e1: Sem_eff v1 G1 e1 v2 G2 e2),
     ctx_HdnmNotMem h G1  ->
     Sem_eff v1 G1  (concat  ((app (cons  (cons  (has_A h v')  nil)  nil) (app (cons e1 nil) nil))) )  v2 G2  (concat  ((app (cons  (cons  (has_A h v')  nil)  nil) (app (cons e2 nil) nil))) ) 
 | Sem_eff_F : forall (v1:val) (G1:ctx) (h:hdnm) (n:mode) (T:type) (v0:val) (e1:eff) (v2:val) (G2:ctx) (e2:eff) (G0:ctx)
     (TYRv0: TyR_term G0 (term_Val v0) T)
     (EAPPv1sube1: Sem_eff  (val_effapp  v1    (cons  (has_A h v0)  nil)  )    (ctx_union  G1    (ctx_stimes  n   G0 )  )   e1 v2 G2 e2),
     ctx_Valid G0  ->
     Sem_eff v1  (ctx_union  G1    (ctx_from_list  (cons (bndr_H h n T) nil) )  )   (concat  ((app (cons  (cons  (has_A h v0)  nil)  nil) (app (cons e1 nil) nil))) )  v2 G2 e2
with Sem_term : term -> hddyn -> val -> eff -> Prop :=    (* defn Sem_term *)
 | Sem_term_V : forall (v:val) (d:hddyn),
     Sem_term (term_Val v) d v  nil 
 | Sem_term_App : forall (t1 t2:term) (d:hddyn) (v3:val) (e1 e2 e3:eff) (v1:val) (x:tmv) (u:term)
     (REDt1: Sem_term t1  ( d  ++ (cons 1 nil))  v1 e1)
     (REDt2: Sem_term t2  ( d  ++ (cons 2 nil))  (val_F x u) e2)
     (REDusub: Sem_term  (term_sub  u   x   v1 )   ( d  ++ (cons 3 nil))  v3 e3),
     Sem_term (term_App t1 t2) d v3  (concat  ((app (cons e1 nil) (app (cons e2 nil) (app (cons e3 nil) nil)))) ) 
 | Sem_term_PatU : forall (t1 t2:term) (d:hddyn) (v2:val) (e1 e2:eff)
     (REDt1: Sem_term t1  ( d  ++ (cons 1 nil))  val_U e1)
     (REDt2: Sem_term t2  ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatU t1 t2) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_PatL : forall (t:term) (x1:tmv) (u1:term) (x2:tmv) (u2:term) (d:hddyn) (v2:val) (e1 e2:eff) (v1:val)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_L v1) e1)
     (REDu1sub: Sem_term  (term_sub  u1   x1   v1 )   ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatS t x1 u1 x2 u2) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_PatR : forall (t:term) (x1:tmv) (u1:term) (x2:tmv) (u2:term) (d:hddyn) (v2:val) (e1 e2:eff) (v1:val)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_R v1) e1)
     (REDu2sub: Sem_term  (term_sub  u2   x2   v1 )   ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatS t x1 u1 x2 u2) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_PatP : forall (t:term) (x1 x2:tmv) (u:term) (d:hddyn) (v2:val) (e1 e2:eff) (v1:val)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_P v1 v2) e1)
     (REDusub: Sem_term  (term_sub   (term_sub  u   x1   v1 )    x2   v2 )   ( d  ++ (cons 2 nil))  v2 e2),
     Sem_term (term_PatP t x1 x2 u) d v2  (concat  ((app (cons e1 nil) (app (cons e2 nil) nil))) ) 
 | Sem_term_Map : forall (t:term) (x:tmv) (u:term) (d:hddyn) (v3 v4:val) (D':ctx) (e1 e3:eff) (v1 v2:val) (D:ctx) (e2:eff)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_A v1 v2 D) e1)
     (REDusub: Sem_term  (term_sub  u   x   v1 )   ( d  ++ (cons 2 nil))  v3 e2)
     (EAPPv2e2: Sem_eff v2 D e2 v4 D' e3),
     Sem_term (term_Map t x u) d (val_A v3 v4 D')  (concat  ((app (cons e1 nil) (app (cons e3 nil) nil))) ) 
 | Sem_term_Alloc : forall (T:type) (d:hddyn),
     Sem_term (term_Alloc T) d (val_A (val_D (hdnm_D d)) (val_H (hdnm_D d))  (ctx_from_list  (cons (bndr_H (hdnm_D d)  (Some (pair   Lin     (Fin 0)  ))  T) nil) ) )  nil 
 | Sem_term_ToA : forall (t:term) (d:hddyn) (v:val) (e:eff)
     (REDt: Sem_term t d v e),
     Sem_term (term_ToA t) d (val_A val_U v  (ctx_from_list  nil ) ) e
 | Sem_term_FromA : forall (t:term) (d:hddyn) (v:val) (e:eff)
     (REDt: Sem_term t d (val_A val_U v  (ctx_from_list  nil ) ) e),
     Sem_term (term_FromA t) d v e
 | Sem_term_FillU : forall (t:term) (d:hddyn) (e:eff) (h:hdnm)
     (REDt: Sem_term t d (val_D h) e),
     Sem_term (term_FillU t) d val_U  (concat  ((app (cons e nil) (app (cons  (cons  (has_A h val_U)  nil)  nil) nil))) ) 
 | Sem_term_FillL : forall (t:term) (d:hddyn) (e:eff) (h:hdnm)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e),
     Sem_term (term_FillL t) d (val_D (hdnm_D  ( d  ++ (cons 2 nil)) ))  (concat  ((app (cons e nil) (app (cons  (cons  (has_A h (val_L (val_H (hdnm_D  ( d  ++ (cons 2 nil)) ))))  nil)  nil) nil))) ) 
 | Sem_term_FillR : forall (t:term) (d:hddyn) (e:eff) (h:hdnm)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e),
     Sem_term (term_FillR t) d (val_D (hdnm_D  ( d  ++ (cons 2 nil)) ))  (concat  ((app (cons e nil) (app (cons  (cons  (has_A h (val_R (val_H (hdnm_D  ( d  ++ (cons 2 nil)) ))))  nil)  nil) nil))) ) 
 | Sem_term_FillP : forall (t:term) (d:hddyn) (e:eff) (h:hdnm)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e),
     Sem_term (term_FillP t) d (val_P (val_D (hdnm_D  ( d  ++ (cons 2 nil)) )) (val_D (hdnm_D  ( d  ++ (cons 3 nil)) )))  (concat  ((app (cons e nil) (app (cons  (cons  (has_A h (val_P (val_H (hdnm_D  ( d  ++ (cons 2 nil)) )) (val_H (hdnm_D  ( d  ++ (cons 3 nil)) ))))  nil)  nil) nil))) ) 
 | Sem_term_FillC : forall (t u:term) (d:hddyn) (v1:val) (e1 e2:eff) (h:hdnm) (v2:val) (D:ctx)
     (REDt: Sem_term t  ( d  ++ (cons 1 nil))  (val_D h) e1)
     (REDu: Sem_term u  ( d  ++ (cons 2 nil))  (val_A v1 v2 D) e2),
     Sem_term (term_FillC t u) d v1  (concat  ((app (cons e1 nil) (app (cons e2 nil) (app (cons  (cons  (has_A h v2)  nil)  nil) nil)))) ) .



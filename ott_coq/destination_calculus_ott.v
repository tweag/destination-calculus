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
Require Import Coq.FSets.FMapList.

Definition tvar : Type := nat. (*r Term-level variable *)
Definition hvar : Type := nat. (*r Hole *)
Definition n : Type := nat.

Definition M : Type := ext_nat.

Inductive T : Type :=  (*r Type *)
 | T_U : T (*r Unit *)
 | T_S (T1:T) (T2:T) (*r Sum *)
 | T_P (T1:T) (T2:T) (*r Product *)
 | T_E (M5:M) (T5:T) (*r Exponential *)
 | T_A (T1:T) (T2:T) (*r Ampar type (consuming $(T1:T)$ yields $(T2:T)$) *)
 | T_F (T1:T) (M5:M) (T2:T) (*r Linear function *)
 | T_D (T5:T) (M5:M) (*r Destination *).

Inductive PA : Type :=  (*r Positive type assignment *)
 | PA_V (x:tvar) (M5:M) (T5:T) (*r Variable *)
 | PA_D (h:hvar) (M5:M) (T5:T) (N:M) (*r Destination ($(M5:M)$ is its own age; $(N:M)$ is the age of values it accepts) *).

Inductive NA : Type :=  (*r Negative type assignment *)
 | NA_H (h:hvar) (N:M) (T5:T) (*r Hole ($(N:M)$ is the age of values it accepts, its own age is undefined) *).
Inductive key : Type :=
  | N_X : tvar -> key
  | N_HD : hvar -> key.

Module Key_as_OT <: OrderedType.
  Definition t := key.

  Definition lt (x y : key) :=
    match x, y with
    | N_X n, N_X m => Nat.lt n m
    | N_HD n, N_HD m => Nat.lt n m
    | N_X _, N_HD _ => True
    | N_HD _, N_X _ => False
    end.
  
  Definition compare: key -> key -> comparison :=
    fun x y => match x, y with
    | N_X n, N_X m => Nat.compare n m
    | N_HD n, N_HD m => Nat.compare n m
    | N_X _, N_HD _ => Lt
    | N_HD _, N_X _ => Gt
    end.

    Lemma lt_trans: forall x y z : key, lt x y -> lt y z -> lt x z.
    Proof.
      intros x y z. destruct x, y, z.
      - unfold lt. apply Nat.lt_trans.
      - unfold lt. tauto.
      - unfold lt. tauto.
      - unfold lt. tauto.
      - unfold lt. tauto.
      - unfold lt. tauto.
      - unfold lt. tauto.
      - unfold lt. apply Nat.lt_trans.
    Defined.

    Lemma lt_not_eq : forall x y : key, lt x y -> ~ x = y.
    Proof.
        intros x y. destruct x, y.
        - unfold lt. intro h. apply Nat.lt_neq in h. congruence.
        - unfold lt. congruence.
        - unfold lt. congruence.
        - unfold lt. intro h'. apply Nat.lt_neq in h'. congruence.
    Defined.

    Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof. unfold Proper. unfold respectful. intros x y H x0 y0 H0. rewrite H. rewrite H0. reflexivity. Defined.
 
  Definition eq := @eq key.
  Definition eq_refl := @eq_refl key.
  Definition eq_sym := @eq_sym key.
  Definition eq_trans := @eq_trans key.

  (* Define the eq_dec function *)
  Theorem eq_dec : forall x y : key, {x = y} + {x <> y}.
  Proof.
    intros x y. induction x.
    - induction y.
        + assert ({t0 = t1} + {t0 <> t1}) by apply Nat.eq_dec. destruct H.
           * left. rewrite e. reflexivity.
           * right. congruence.
        + right. congruence.
    - induction y.
        + right. congruence.
        + assert ({h = h0} + {h <> h0}) by apply Nat.eq_dec. destruct H.
           * left. rewrite e. reflexivity.
           * right. congruence.
    Defined.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof. Admitted.
  (* TODO *)

  Instance eq_equiv : Equivalence Key_as_OT.eq. split. exact eq_refl. exact eq_sym. exact eq_trans. Defined.

  Instance lt_strorder : StrictOrder Key_as_OT.lt. split. unfold Irreflexive. unfold Reflexive. unfold complement. intros x h. apply lt_not_eq in h. congruence. exact lt_trans. Defined.
End Key_as_OT.

Module Key_as_OTOrig := Backport_OT(Key_as_OT).

Module ValidCtx := FMapList.Make(Key_as_OTOrig).

Definition option_bind {A B} (f : A -> option B) (x : option A) : option B :=
  match x with
  | Some x => f x
  | None => None
  end.

Definition PA_key (x : PA) : key :=
  match x with
  | PA_V x M2 T2 => N_X x
  | PA_D h M2 T2 M3 => N_HD h
  end.

Definition PC_add_PA (b : PA) (G : option (ValidCtx.t PA)) : option (ValidCtx.t PA) :=
  option_bind (fun G' =>
    if ValidCtx.mem (PA_key b) G'
      then None
      else Some (ValidCtx.add (PA_key b) b G')
  ) G.

Definition PC_from_PA_list (bs : list PA) : option (ValidCtx.t PA) :=
  List.fold_left (fun G b => PC_add_PA b G) bs (Some (ValidCtx.empty PA)).

Definition NA_key (x : NA) : key :=
  match x with
  | NA_H h M2 T2 => N_HD h
  end.

Definition NC_add_NA (b : NA) (D : option (ValidCtx.t NA)) : option (ValidCtx.t NA) :=
  option_bind (fun D' =>
    if ValidCtx.mem (NA_key b) D'
      then None
      else Some (ValidCtx.add (NA_key b) b D')
  ) D.

Definition NC_from_NA_list (bs : list NA) : option (ValidCtx.t NA) :=
  List.fold_left (fun D b => NC_add_NA b D) bs (Some (ValidCtx.empty NA)).

Definition PC_union (G1 G2 : option (ValidCtx.t PA)) : option (ValidCtx.t PA) :=
  option_bind (fun G2' =>
    ValidCtx.fold (fun k x G => PC_add_PA x G) G2' G1
  ) G2.

Definition NC_union (D1 D2 : option (ValidCtx.t NA)) : option (ValidCtx.t NA) :=
  option_bind (fun D2' =>
    ValidCtx.fold (fun k x D => NC_add_NA x D) D2' D1
  ) D2.

Definition PC_S (M1 : M) (G : option (ValidCtx.t PA)) : option (ValidCtx.t PA) :=
  option_map (fun G' =>
    ValidCtx.map (fun x =>
      match x with
      | PA_V x M2 T2 => PA_V x (ext_plus M1 M2) T2
      | PA_D h M2 T2 M3 => PA_D h (ext_plus M1 M2) T2 M3
      end
    ) G'
  ) G.

Definition NC_S (M1 : M) (D : option (ValidCtx.t NA)) : option (ValidCtx.t NA) :=
  option_map (fun D' =>
    ValidCtx.map (fun x =>
      match x with
      | NA_H h M2 T2 => NA_H h (ext_plus M1 M2) T2
      end
    ) D'
  ) D.

Definition NC_minus (G : option (ValidCtx.t PA)) : option (ValidCtx.t NA) :=
  option_bind (fun G' =>
    ValidCtx.fold (fun k x D =>
      match x with
      | PA_V x M2 T2 => None
      | PA_D h M2 T2 M3 => NC_add_NA (NA_H h (ext_plus M2 M3) T2) D
      end
    ) G' (Some (ValidCtx.empty NA))
  ) G.


Definition PC : Type := option (ValidCtx.t PA).

Definition NC : Type := option (ValidCtx.t NA).

Inductive t : Type :=  (*r Term *)
 | t_Val (v5:v) (*r Term value *)
 | t_Var (x:tvar) (*r Variable *)
 | t_App (t5:t) (u:t) (*r Application *)
 | t_PatU (t5:t) (u:t) (*r Pattern-match on unit *)
 | t_PatS (t5:t) (x1:tvar) (u1:t) (x2:tvar) (u2:t) (*r Pattern-match on sum *)
 | t_PatP (t5:t) (x1:tvar) (x2:tvar) (u:t) (*r Pattern-match on product *)
 | t_PatE (t5:t) (M5:M) (x:tvar) (u:t) (*r Pattern-match on exponential *)
 | t_Map (t5:t) (x:tvar) (u:t) (*r Map over the left side of the ampar *)
 | t_ToA (t5:t) (*r Wrap $(t5:t)$ into a trivial ampar *)
 | t_FromA (t5:t) (*r Extract value from trivial ampar *)
 | t_Alloc (T5:T) (*r Return a fresh "identity" ampar object *)
 | t_FillU (t5:t) (*r Fill destination with unit *)
 | t_FillL (t5:t) (*r Fill destination with left variant *)
 | t_FillR (t5:t) (*r Fill destination with right variant *)
 | t_FillP (t5:t) (*r Fill destination with product constructor *)
 | t_FillE (t5:t) (M5:M) (*r Fill destination with exponential constructor *)
 | t_FillC (t5:t) (u:t) (*r Fill destination with root of ampar $(u:t)$ *)
with v : Type :=  (*r Term value *)
 | v_A (v1:v) (w2:w) (D:NC) (*r Ampar *)
 | v_D (h:hvar) (*r Destination *)
 | v_U : v (*r Unit *)
 | v_L (v5:v) (*r Left variant for sum *)
 | v_R (v5:v) (*r Right variant for sum *)
 | v_P (v1:v) (v2:v) (*r Product *)
 | v_E (M5:M) (v5:v) (*r Exponential *)
 | v_F (x:tvar) (t5:t) (*r Linear function *)
with w : Type :=  (*r Pseudo-value that may contain holes *)
 | w_V (v5:v) (*r Term value *)
 | w_H (h:hvar) (*r Hole *)
 | w_L (w5:w) (*r Left variant with val or hole *)
 | w_R (w5:w) (*r Right variant with val or hole *)
 | w_P (w1:w) (w2:w) (*r Product with val or hole *)
 | w_E (M5:M) (w5:w) (*r Exponential with val or hole *).

Inductive e : Type :=  (*r Effect *)
 | e_N : e
 | e_A (h:hvar) (w5:w)
 | e_P (_:list e) (*r Chain effects *).

Inductive C : Type :=  (*r Context *)
 | C_P (PC5:PC)
 | C_N (NC5:NC).
(** induction principles *)
Section e_rect.

Variables
  (P_e : e -> Prop)
  (P_list_e : list e -> Prop).

Hypothesis
  (H_e_N : P_e e_N)
  (H_e_A : forall (h:hvar), forall (w5:w), P_e (e_A h w5))
  (H_e_P : forall (e_list:list e), P_list_e e_list -> P_e (e_P e_list))
  (H_list_e_nil : P_list_e nil)
  (H_list_e_cons : forall (e0:e), P_e e0 -> forall (e_l:list e), P_list_e e_l -> P_list_e (cons e0 e_l)).

Fixpoint e_ott_ind (n:e) : P_e n :=
  match n as x return P_e x with
  | e_N => H_e_N 
  | (e_A h w5) => H_e_A h w5
  | (e_P e_list) => H_e_P e_list (((fix e_list_ott_ind (e_l:list e) : P_list_e e_l := match e_l as x return P_list_e x with nil => H_list_e_nil | cons e1 xl => H_list_e_cons e1(e_ott_ind e1)xl (e_list_ott_ind xl) end)) e_list)
end.

End e_rect.
Definition t_sub (t1: t) (x : tvar) (v1 : v) : t := t1.
(* TODO *)
Definition w_eapp (w1 : w) (e1 : e) : w := w1.
(* TODO *)


Inductive P : Type := 
 | _C_D (C1:C) (C2:C)
 | _C_NI (h:hvar) (C5:C)
 | _PC_DO (G:PC)
 | _C_FH (h:hvar)
 | _Ty_e (G:PC) (u:t) (D:NC) (e5:e) (*r Typing of effects (require both positive and negative contexts) *)
 | _Ty_c (G:PC) (v5:v) (e5:e) (T5:T) (*r Typing of commands (only a positive context is needed) *)
 | _Ty_w (G:PC) (u:t) (D:NC) (w5:w) (T5:T) (*r Typing of extended values (require both positive and negative contexts) *)
 | _Ty_t (G:PC) (t5:t) (T5:T) (*r Typing of terms (only a positive context is needed) *)
 | _Sem_e (w1:w) (D1:NC) (e1:e) (w2:w) (D2:NC) (e2:e) (*r Semantics of effects *)
 | _Sem_t (t5:t) (v5:v) (e5:e) (*r Big-step evaluation into commands *).
(** definitions *)

(* defns Ty *)
Inductive C_D : C -> C -> Prop :=    (* defn C_D *)
with C_NI : hvar -> C -> Prop :=    (* defn C_NI *)
with PC_DO : PC -> Prop :=    (* defn PC_DO *)
with C_FH : hvar -> Prop :=    (* defn C_FH *)
with Ty_e : PC -> t -> NC -> e -> Prop :=    (* defn Ty_e *)
 | Ty_e_N : forall (u:t),
     Ty_e  (PC_from_PA_list  nil )  u  (NC_from_NA_list  nil )  e_N
 | Ty_e_A : forall (M5 N:M) (G:PC) (h:hvar) (T5:T) (u:t) (D:NC) (w5:w),
     Ty_w G u D w5 T5 ->
     C_D (C_P G) (C_P  (PC_from_PA_list  (cons (PA_D h M5 T5 N) nil) ) ) ->
     C_D (C_P G) (C_N D) ->
     C_D (C_P  (PC_from_PA_list  (cons (PA_D h M5 T5 N) nil) ) ) (C_N D) ->
     Ty_e  (PC_union   (PC_S    (ext_plus'  ((app (cons  (Fin 1)  nil) (app (cons M5 nil) (app (cons N nil) nil)))) )     G )     (PC_from_PA_list  (cons (PA_D h M5 T5 N) nil) )  )  u  (NC_S    (ext_plus'  ((app (cons M5 nil) (app (cons N nil) nil))) )     D )  (e_A h w5)
 | Ty_e_P : forall (G1 G21:PC) (u:t) (D1 D2:NC) (e1 e2:e) (G22:PC),
     Ty_e G1 u  (NC_union  D1    (NC_minus  G22 )  )  e1 ->
     Ty_e  (PC_union  G21   G22 )  u D2 e2 ->
     C_D (C_P G1) (C_P G21) ->
     C_D (C_P G1) (C_P G22) ->
     C_D (C_P G1) (C_N D1) ->
     C_D (C_P G1) (C_N D2) ->
     C_D (C_P G21) (C_P G22) ->
     C_D (C_P G21) (C_N D1) ->
     C_D (C_P G21) (C_N D2) ->
     C_D (C_P G22) (C_N D1) ->
     C_D (C_P G22) (C_N D2) ->
     C_D (C_N D1) (C_N D2) ->
     Ty_e  (PC_union  G1   G21 )  u  (NC_union  D1   D2 )  (e_P ((app (cons e1 nil) (app (cons e2 nil) nil))))
with Ty_c : PC -> v -> e -> T -> Prop :=    (* defn Ty_c *)
 | Ty_c_C : forall (G11 G2:PC) (v5:v) (e5:e) (T5:T) (G12:PC) (u:t),
     Ty_t  (PC_union  G11   G12 )  (t_Val v5) T5 ->
     Ty_e G2 u  (NC_minus  G12 )  e5 ->
     C_D (C_P G11) (C_P G12) ->
     C_D (C_P G11) (C_P G2) ->
     C_D (C_P G12) (C_P G2) ->
     Ty_c  (PC_union  G11   G2 )  v5 e5 T5
with Ty_w : PC -> t -> NC -> w -> T -> Prop :=    (* defn Ty_w *)
 | Ty_w_H : forall (u:t) (h:hvar) (T5:T),
     Ty_w  (PC_from_PA_list  nil )  u  (NC_from_NA_list  (cons (NA_H h  (Fin 0)  T5) nil) )  (w_H h) T5
 | Ty_w_D : forall (h:hvar) (T5:T) (N:M) (u:t),
     Ty_w  (PC_from_PA_list  (cons (PA_D h  (Fin 0)  T5 N) nil) )  u  (NC_from_NA_list  nil )  (w_V (v_D h)) (T_D T5 N)
 | Ty_w_U : forall (u:t),
     Ty_w  (PC_from_PA_list  nil )  u  (NC_from_NA_list  nil )  (w_V v_U) T_U
 | Ty_w_L : forall (G:PC) (u:t) (D:NC) (w5:w) (T1 T2:T),
     Ty_w G u D w5 T1 ->
     C_D (C_P G) (C_N D) ->
     Ty_w G u D (w_L w5) (T_S T1 T2)
 | Ty_w_R : forall (G:PC) (u:t) (D:NC) (w5:w) (T1 T2:T),
     Ty_w G u D w5 T2 ->
     C_D (C_P G) (C_N D) ->
     Ty_w G u D (w_R w5) (T_S T1 T2)
 | Ty_w_P : forall (G1 G2:PC) (u:t) (D1 D2:NC) (w1 w2:w) (T1 T2:T),
     Ty_w G1 u D1 w1 T1 ->
     Ty_w G2 u D2 w2 T2 ->
     C_D (C_P G1) (C_P G2) ->
     C_D (C_P G1) (C_N D1) ->
     C_D (C_P G1) (C_N D2) ->
     C_D (C_P G2) (C_N D1) ->
     C_D (C_P G2) (C_N D2) ->
     C_D (C_N D1) (C_N D2) ->
     Ty_w  (PC_union  G1   G2 )  u  (NC_union  D1   D2 )  (w_P w1 w2) (T_P T1 T2)
 | Ty_w_E : forall (M5:M) (G:PC) (u:t) (D:NC) (w5:w) (T5:T),
     Ty_w G u D w5 T5 ->
     C_D (C_P G) (C_N D) ->
     Ty_w  (PC_S  M5   G )  u  (NC_S  M5   D )  (w_E M5 w5) (T_E M5 T5)
 | Ty_w_A : forall (G2:PC) (u:t) (v1:v) (w2:w) (G1:PC) (T1 T2:T),
     Ty_w G1 u  (NC_from_NA_list  nil )  (w_V v1) T1 ->
     Ty_w G2 u  (NC_minus  G1 )  w2 T2 ->
     C_D (C_P G1) (C_P G2) ->
     Ty_w G2 u  (NC_from_NA_list  nil )  (w_V (v_A v1 w2  (NC_minus  G1 ) )) (T_A T1 T2)
 | Ty_w_F : forall (G:PC) (u:t) (x:tvar) (t5:t) (T1:T) (M5:M) (T2:T),
     Ty_t  (PC_union  G    (PC_from_PA_list  (cons (PA_V x M5 T1) nil) )  )  t5 T2 ->
     C_D (C_P G) (C_P  (PC_from_PA_list  (cons (PA_V x M5 T1) nil) ) ) ->
     Ty_w G u  (NC_from_NA_list  nil )  (w_V (v_F x t5)) (T_F T1 M5 T2)
with Ty_t : PC -> t -> T -> Prop :=    (* defn Ty_t *)
 | Ty_t_V : forall (G:PC) (v5:v) (T5:T) (u:t),
     Ty_w G u  (NC_from_NA_list  nil )  (w_V v5) T5 ->
     Ty_t G (t_Val v5) T5
 | Ty_t_X0 : forall (x:tvar) (T5:T),
     Ty_t  (PC_from_PA_list  (cons (PA_V x  (Fin 0)  T5) nil) )  (t_Var x) T5
 | Ty_t_XInf : forall (x:tvar) (T5:T),
     Ty_t  (PC_from_PA_list  (cons (PA_V x  Inf  T5) nil) )  (t_Var x) T5
 | Ty_t_App : forall (M5:M) (G1 G2:PC) (t5 u:t) (T2 T1:T),
     Ty_t G1 t5 T1 ->
     Ty_t G2 u (T_F T1 M5 T2) ->
     C_D (C_P G1) (C_P G2) ->
     Ty_t  (PC_union   (PC_S  M5   G1 )    G2 )  (t_App t5 u) T2
 | Ty_t_PatU : forall (G1 G2:PC) (t5 u:t) (U:T),
     Ty_t G1 t5 T_U ->
     Ty_t G2 u U ->
     C_D (C_P G1) (C_P G2) ->
     Ty_t  (PC_union  G1   G2 )  (t_PatU t5 u) U
 | Ty_t_PatS : forall (M5:M) (G1 G2:PC) (t5:t) (x1:tvar) (u1:t) (x2:tvar) (u2:t) (U T1 T2:T),
     Ty_t G1 t5 (T_S T1 T2) ->
     Ty_t  (PC_union  G2    (PC_from_PA_list  (cons (PA_V x1 M5 T1) nil) )  )  u1 U ->
     Ty_t  (PC_union  G2    (PC_from_PA_list  (cons (PA_V x2 M5 T2) nil) )  )  u2 U ->
     C_D (C_P G1) (C_P G2) ->
     C_D (C_P G2) (C_P  (PC_from_PA_list  (cons (PA_V x1 M5 T1) nil) ) ) ->
     C_D (C_P G2) (C_P  (PC_from_PA_list  (cons (PA_V x2 M5 T2) nil) ) ) ->
     Ty_t  (PC_union   (PC_S  M5   G1 )    G2 )  (t_PatS t5 x1 u1 x2 u2) U
 | Ty_t_PatP : forall (M5:M) (G1 G2:PC) (t5:t) (x1 x2:tvar) (u:t) (U T1 T2:T),
     Ty_t G1 t5 (T_P T1 T2) ->
     Ty_t  (PC_union  G2    (PC_from_PA_list  ((app (cons (PA_V x1 M5 T1) nil) (app (cons (PA_V x2 M5 T2) nil) nil))) )  )  u U ->
     C_D (C_P G1) (C_P G2) ->
     C_D (C_P G2) (C_P  (PC_from_PA_list  (cons (PA_V x1 M5 T1) nil) ) ) ->
     C_D (C_P G2) (C_P  (PC_from_PA_list  (cons (PA_V x2 M5 T2) nil) ) ) ->
     C_D (C_P  (PC_from_PA_list  (cons (PA_V x1 M5 T1) nil) ) ) (C_P  (PC_from_PA_list  (cons (PA_V x2 M5 T2) nil) ) ) ->
     Ty_t  (PC_union   (PC_S  M5   G1 )    G2 )  (t_PatP t5 x1 x2 u) U
 | Ty_t_PatE : forall (M5:M) (G1 G2:PC) (t5:t) (N:M) (x:tvar) (u:t) (U T5:T),
     Ty_t G1 t5 (T_E N T5) ->
     Ty_t  (PC_union  G2    (PC_from_PA_list  (cons (PA_V x  (ext_plus'  ((app (cons M5 nil) (app (cons N nil) nil))) )  T5) nil) )  )  u U ->
     C_D (C_P G1) (C_P G2) ->
     C_D (C_P G2) (C_P  (PC_from_PA_list  (cons (PA_V x  (ext_plus'  ((app (cons M5 nil) (app (cons N nil) nil))) )  T5) nil) ) ) ->
     Ty_t  (PC_union   (PC_S  M5   G1 )    G2 )  (t_PatE t5 N x u) U
 | Ty_t_Map : forall (G1 G2:PC) (t5:t) (x:tvar) (u:t) (U T2 T1:T),
     Ty_t G1 t5 (T_A T1 T2) ->
     Ty_t  (PC_union   (PC_S   (Fin 1)    G2 )     (PC_from_PA_list  (cons (PA_V x  (Fin 0)  T1) nil) )  )  u U ->
     C_D (C_P G1) (C_P G2) ->
     C_D (C_P G2) (C_P  (PC_from_PA_list  (cons (PA_V x  (Fin 0)  T1) nil) ) ) ->
     Ty_t  (PC_union  G1   G2 )  (t_Map t5 x u) (T_A U T2)
 | Ty_t_FillC : forall (G1:PC) (N:M) (G2:PC) (t5 u:t) (T1 T2:T),
     Ty_t G1 t5 (T_D T2 N) ->
     Ty_t G2 u (T_A T1 T2) ->
     C_D (C_P G1) (C_P G2) ->
     Ty_t  (PC_union  G1    (PC_S    (ext_plus'  ((app (cons  (Fin 1)  nil) (app (cons N nil) nil))) )     G2 )  )  (t_FillC t5 u) T1
 | Ty_t_FillU : forall (G:PC) (t5:t) (N:M),
     Ty_t G t5 (T_D T_U N) ->
     Ty_t G (t_FillU t5) T_U
 | Ty_t_FillL : forall (G:PC) (t5:t) (T1:T) (N:M) (T2:T),
     Ty_t G t5 (T_D (T_S T1 T2) N) ->
     Ty_t G (t_FillL t5) (T_D T1 N)
 | Ty_t_FillR : forall (G:PC) (t5:t) (T2:T) (N:M) (T1:T),
     Ty_t G t5 (T_D (T_S T1 T2) N) ->
     Ty_t G (t_FillR t5) (T_D T2 N)
 | Ty_t_FillP : forall (G:PC) (t5:t) (T1:T) (N:M) (T2:T),
     Ty_t G t5 (T_D (T_P T1 T2) N) ->
     Ty_t G (t_FillP t5) (T_P (T_D T1 N) (T_D T2 N))
 | Ty_t_FillE : forall (G:PC) (t5:t) (N:M) (T5:T) (M5:M),
     Ty_t G t5 (T_D (T_E N T5) M5) ->
     Ty_t G (t_FillE t5 N) (T_D T5  (ext_plus'  ((app (cons M5 nil) (app (cons N nil) nil))) ) )
 | Ty_t_Alloc : forall (T5:T),
     Ty_t  (PC_from_PA_list  nil )  (t_Alloc T5) (T_A (T_D T5  (Fin 0) ) T5)
 | Ty_t_ToA : forall (G:PC) (t5:t) (T5:T),
     Ty_t G t5 T5 ->
     Ty_t G (t_ToA t5) (T_A T_U T5)
 | Ty_t_FromA : forall (G:PC) (t5:t) (T5:T),
     Ty_t G t5 (T_A T_U T5) ->
     Ty_t G (t_FromA t5) T5.
(** definitions *)

(* defns Sem *)
Inductive Sem_e : w -> NC -> e -> w -> NC -> e -> Prop :=    (* defn Sem_e *)
 | Sem_e_N : forall (w1:w) (D1:NC),
     Sem_e w1 D1 e_N w1 D1 e_N
 | Sem_e_S : forall (w1:w) (D1:NC) (h:hvar) (w':w) (e1:e) (w2:w) (D2:NC) (e2:e),
     C_NI h (C_N D1) ->
     Sem_e w1 D1 e1 w2 D2 e2 ->
     Sem_e w1 D1 (e_P ((app (cons (e_A h w') nil) (app (cons e1 nil) nil)))) w2 D2 (e_P ((app (cons (e_A h w') nil) (app (cons e2 nil) nil))))
 | Sem_e_F : forall (w1:w) (D1:NC) (h:hvar) (N:M) (T5:T) (w':w) (e1:e) (w2:w) (D2:NC) (e2:e) (G1':PC) (u:t) (D1':NC),
     Ty_w G1' u D1' w' T5 ->
     C_D (C_P G1') (C_N D1') ->
     C_D (C_N D1) (C_N  (NC_from_NA_list  (cons (NA_H h N T5) nil) ) ) ->
     C_D (C_N D1) (C_N D1') ->
     Sem_e  (w_eapp  w1   (e_A h w') )    (NC_union  D1    (NC_S  N   D1' )  )   e1 w2 D2 e2 ->
     Sem_e w1  (NC_union  D1    (NC_from_NA_list  (cons (NA_H h N T5) nil) )  )  (e_P ((app (cons (e_A h w') nil) (app (cons e1 nil) nil)))) w2 D2 e2
with Sem_t : t -> v -> e -> Prop :=    (* defn Sem_t *)
 | Sem_t_V : forall (v5:v),
     Sem_t (t_Val v5) v5 e_N
 | Sem_t_App : forall (t1 t2:t) (v3:v) (e1 e2 e3:e) (v1:v) (x:tvar) (u:t),
     Sem_t t1 v1 e1 ->
     Sem_t t2 (v_F x u) e2 ->
     Sem_t  (t_sub  u   x   v1 )  v3 e3 ->
     Sem_t (t_App t1 t2) v3 (e_P ((app (cons e1 nil) (app (cons e2 nil) (app (cons e3 nil) nil)))))
 | Sem_t_PatU : forall (t1 t2:t) (v2:v) (e1 e2:e),
     Sem_t t1 v_U e1 ->
     Sem_t t2 v2 e2 ->
     Sem_t (t_PatU t1 t2) v2 (e_P ((app (cons e1 nil) (app (cons e2 nil) nil))))
 | Sem_t_PatL : forall (t5:t) (x1:tvar) (u1:t) (x2:tvar) (u2:t) (v2:v) (e1 e2:e) (v1:v),
     Sem_t t5 (v_L v1) e1 ->
     Sem_t  (t_sub  u1   x1   v1 )  v2 e2 ->
     Sem_t (t_PatS t5 x1 u1 x2 u2) v2 (e_P ((app (cons e1 nil) (app (cons e2 nil) nil))))
 | Sem_t_PatR : forall (t5:t) (x1:tvar) (u1:t) (x2:tvar) (u2:t) (v2:v) (e1 e2:e) (v1:v),
     Sem_t t5 (v_R v1) e1 ->
     Sem_t  (t_sub  u2   x2   v1 )  v2 e2 ->
     Sem_t (t_PatS t5 x1 u1 x2 u2) v2 (e_P ((app (cons e1 nil) (app (cons e2 nil) nil))))
 | Sem_t_PatP : forall (t5:t) (x1 x2:tvar) (u:t) (v2:v) (e1 e2:e) (v1:v),
     Sem_t t5 (v_P v1 v2) e1 ->
     Sem_t  (t_sub   (t_sub  u   x1   v1 )    x2   v2 )  v2 e2 ->
     Sem_t (t_PatP t5 x1 x2 u) v2 (e_P ((app (cons e1 nil) (app (cons e2 nil) nil))))
 | Sem_t_Map : forall (t5:t) (x:tvar) (u:t) (v3:v) (w4:w) (D':NC) (e1 e3:e) (v1:v) (w2:w) (D:NC) (e2:e),
     Sem_t t5 (v_A v1 w2 D) e1 ->
     Sem_t  (t_sub  u   x   v1 )  v3 e2 ->
     Sem_e w2 D e2 w4 D' e3 ->
     Sem_t (t_Map t5 x u) (v_A v3 w4 D') (e_P ((app (cons e1 nil) (app (cons e3 nil) nil))))
 | Sem_t_Alloc : forall (T5:T) (h:hvar),
     C_FH h ->
     Sem_t (t_Alloc T5) (v_A (v_D h) (w_H h)  (NC_from_NA_list  (cons (NA_H h  (Fin 0)  T5) nil) ) ) e_N
 | Sem_t_ToA : forall (t5:t) (v5:v) (e5:e),
     Sem_t t5 v5 e5 ->
     Sem_t (t_ToA t5) (v_A v_U (w_V v5)  (NC_from_NA_list  nil ) ) e5
 | Sem_t_FromA : forall (t5:t) (v5:v) (e5:e),
     Sem_t t5 (v_A v_U (w_V v5)  (NC_from_NA_list  nil ) ) e5 ->
     Sem_t (t_FromA t5) v5 e5
 | Sem_t_FillU : forall (t5:t) (e5:e) (h:hvar),
     Sem_t t5 (v_D h) e5 ->
     Sem_t (t_FillU t5) v_U (e_P ((app (cons e5 nil) (app (cons (e_A h (w_V v_U)) nil) nil))))
 | Sem_t_FillL : forall (t5:t) (h':hvar) (e5:e) (h:hvar),
     Sem_t t5 (v_D h) e5 ->
     C_FH h' ->
     Sem_t (t_FillL t5) (v_D h') (e_P ((app (cons e5 nil) (app (cons (e_A h (w_L (w_H h'))) nil) nil))))
 | Sem_t_FillR : forall (t5:t) (h':hvar) (e5:e) (h:hvar),
     Sem_t t5 (v_D h) e5 ->
     Sem_t (t_FillR t5) (v_D h') (e_P ((app (cons e5 nil) (app (cons (e_A h (w_R (w_H h'))) nil) nil))))
 | Sem_t_FillP : forall (t5:t) (h1 h2:hvar) (e5:e) (h:hvar),
     Sem_t t5 (v_D h) e5 ->
     C_FH h1 ->
     C_FH h2 ->
     Sem_t (t_FillP t5) (v_P (v_D h1) (v_D h2)) (e_P ((app (cons e5 nil) (app (cons (e_A h (w_P (w_H h1) (w_H h2))) nil) nil))))
 | Sem_t_FillC : forall (t5 u:t) (v1:v) (e1 e2:e) (h:hvar) (w2:w) (D:NC),
     Sem_t t5 (v_D h) e1 ->
     Sem_t u (v_A v1 w2 D) e2 ->
     Sem_t (t_FillC t5 u) v1 (e_P ((app (cons e1 nil) (app (cons e2 nil) (app (cons (e_A h w2) nil) nil))))).



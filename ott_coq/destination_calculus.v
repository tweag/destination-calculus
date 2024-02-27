Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.ext_nat.

Notation "⋆" := (nil).
Notation "d '.1'" := (d ++ (cons 1 nil)) (at level 30, right associativity).
Notation "d '.2'" := (d ++ (cons 2 nil)) (at level 30, right associativity).
Notation "d '.3'" := (d ++ (cons 3 nil)) (at level 30, right associativity).

Notation "'dyn' d" := (hdnm_D d) (at level 40, no associativity).
Notation "'static' hdmv" := (hdnm_S hdmv) (at level 40, no associativity).

Notation "'¹ν'" := (Some (pair Lin (Fin 0))).
Notation "'¹↑'" := (Some (pair Lin (Fin 1))).
Notation "'¹∞'" := (Some (pair Lin Inf)).

Notation "'ων'" := (Some (pair Ur (Fin 0))).
Notation "'ω↑'" := (Some (pair Ur (Fin 1))).
Notation "'ω∞'" := (Some (pair Ur Inf)).

Notation "'☠'" := None.

Notation Infix "·" := md_times (at level 60, right associativity).
Notation "𝟏" := (typ_U).
Notation "T ⨁ U" := (typ_S T U) (at level 50, left associativity).
Notation "T ⨂ U" := (typ_P T U) (at level 40, left associativity).
Notation "! m T" := (typ_E m T) (at level 30, no associativity).
Notation "T m → U" := (typ_F T m U) (at level 60, right associativity).
Notation "m ⌊ T ⌋" := (typ_D m T) (at level 35, no associativity).

Notation "x : m T" := (bndr_V x m T) (at level 60, no associativity).
Notation "+ h : m n ⌊ T ⌋" := (bndr_D h m n T) (at level 60, no associativity).
Notation "- h ':' n T" := (bndr_H h n T) (at level 60, no associativity).

Notation "{ b , .. , c }" := (ctx_from_list (cons b .. (cons c nil) ..)) (at level 0, no associativity).
Notation "m 'ᶜ·' G" := (ctx_stimes m G) (at level 41, right associativity).
Notation "G '⨄' H" := (ctx_union G H) (at level 50, left associativity).
Notation "G '⋓' H" := (ctx_interact G H) (at level 50, left associativity).
Notation "ᶜ- G" := (ctx_minus G) (at level 35, no associativity).

Notation "t ≻ u" := (term_App t u) (at level 40, left associativity).
Notation "t ; u" := (term_PatU t u) (at level 45, left associativity).
Notation "t '≻case' { 'Inl' x1 ⟼ u1 , 'Inr' x2 ⟼ u2 }" := (term_PatS t x1 u1 x2 u2) (at level 50, left associativity).
Notation "t '≻case' ( x1 , x2 ) ⟼ u" := (term_PatP t x1 x2 u) (at level 50, left associativity).
Notation "t '≻case' '⦆' m x ⟼ u" := (term_PatE t m x u) (at level 50, left associativity).
Notation "t '≻map' x ⟼ u" := (term_Map t x u) (at level 50, left associativity).
Notation "'to⧕' t" := (term_ToA t) (at level 40, left associativity).
Notation "'from⧕' t" := (term_FromA t) (at level 40, left associativity).
Notation "'alloc' T" := (term_Alloc T) (at level 40, left associativity).
Notation "t ⨞ ()" := (term_FillU t) (at level 45, left associativity).
Notation "t ⨞ 'Inl'" := (term_FillL t) (at level 45, left associativity).
Notation "t ⨞ 'Inr'" := (term_FillR t) (at level 45, left associativity).
Notation "t ⨞ '(,)'" := (term_FillP t) (at level 45, left associativity).
Notation "t ⨞ '⦆' m" := (term_FillE t m) (at level 45, left associativity).
Notation "t '⨞·' u" := (term_FillC t u) (at level 45, left associativity).
Notation "t [ x ≔ v ]" := (term_sub t x v) (at level 31, left associativity).

Notation "'ᵛ-' h" := (val_H h) (at level 30, no associativity).
Notation "'ᵛ+' h" := (val_D h) (at level 30, no associativity).
Notation "'()'" := (val_U).
Notation "'λ' x ⟼ t" := (val_F x t) (at level 30, right associativity).
Notation "'Inl' v" := (val_L v) (at level 30, right associativity).
Notation "'Inr' v" := (val_R v) (at level 30, right associativity).
Notation "'⦆' m v" := (val_E m v) (at level 30, right associativity).
Notation "( v 'ᵛ,' w )" := (val_P v w) (at level 30, no associativity).
Notation "'⟨' v '❟' w '⟩' D" := (val_A v w D) (at level 30, no associativity).
Notation "v 'ᵉ[' e ]" := (val_effapp v e) (at level 29, no associativity).

Notation "'ε'" := nil.
Notation "h '≔' w" := (has_A h w) (at level 30, no associativity).
Infix "»" := app (at level 60, right associativity).

Notation "G '⫦' e" := (TyR_eff G e) (at level 60, no associativity).
Notation "G '⫦' t : T" := (TyR_term G t T) (at level 60, no associativity).
Notation "G '⊢' e" := (Ty_eff G e) (at level 60, no associativity).
Notation "G '⊢' t : T" := (Ty_term G t T) (at level 60, no associativity).
Notation "G '⊢' v ⋄ e : T" := (Ty_cmd G v e T) (at level 60, no associativity).

Notation "v1 D1 | e1 '⤋' v2 D2 | e2" := (Sem_eff v1 D1 e1 v2 D2 e2) (at level 60, no associativity).
Notation "t d '⇓' v ⋄ e" := (Sem_term t d v e) (at level 60, no associativity).

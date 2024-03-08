Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.ext_nat.

(* Var, holes and dests names : 15-19 *)
Notation "⋆" := (nil).
Notation "d '.1'" := (d ++ (cons 1 nil)) (at level 18, right associativity).
Notation "d '.2'" := (d ++ (cons 2 nil)) (at level 18, right associativity).
Notation "d '.3'" := (d ++ (cons 3 nil)) (at level 18, right associativity).

Notation "'dyn' d" := (hdn_D d) (at level 19, no associativity).
Notation "'static' hdn" := (hdn_S hdn) (at level 19, no associativity).

(* Multiplicities : 25-29 *)
Notation "'¹ν'" := (Some (pair Lin (Fin 0))).
Notation "'¹↑'" := (Some (pair Lin (Fin 1))).
Notation "'¹∞'" := (Some (pair Lin Inf)).

Notation "'ων'" := (Some (pair Ur (Fin 0))).
Notation "'ω↑'" := (Some (pair Ur (Fin 1))).
Notation "'ω∞'" := (Some (pair Ur Inf)).

Notation "'☠'" := None.

Infix "·" := mode_times (at level 25, right associativity).

(* Types : 30-59 *)
Notation "𝟏" := (type_U).
Notation "T ⨁ U" := (type_S T U) (at level 50, left associativity, U at next level).
Notation "T ⨂ U" := (type_P T U) (at level 40, left associativity, U at next level).
Notation "! m '⁔' T" := (type_E m T) (at level 30, m at level 29, right associativity, T at level 30).
Notation "T ⧔ U" := (type_A T U) (at level 55, left associativity, U at next level).
Notation "T '⁔' m '→' U" := (type_F T m U) (at level 59, m at level 29, right associativity, U at level 59).
Notation "⌊ T ⌋ m" := (type_D T m) (at level 35, T at level 59, m at level 29, no associativity).

(* Values : 30-59 *)
Notation "'ᵛ-' h" := (val_H h) (at level 31, h at level 19, no associativity).
Notation "'ᵛ+' h" := (val_D h) (at level 31, h at level 19, no associativity).
Notation "'ᵛ()'" := (val_U).
Notation "'λ' x ⟼ t" := (val_F x t) (at level 59, x at level 19, t at level 59, right associativity).
Notation "'Inl' v" := (val_L v) (at level 31, right associativity, v at level 31).
Notation "'Inr' v" := (val_R v) (at level 31, right associativity, v at level 31).
Notation "'ᴇ' m '⁔' v" := (val_E m v) (at level 31, m at level 29, v at level 31, right associativity).
Notation "'ᵛ(' v ',' w ')'" := (val_P v w) (at level 0, v at level 59, w at level 59, no associativity).
Notation "'⟨' v '❟' w '⟩' D" := (val_A v w D) (at level 31, no associativity, v at level 59, w at level 59, D at next level).
Notation "v 'ᵉ[' f ]" := (val_hfill v f) (at level 30, f at level 64, no associativity).

(* Terms : 40-59 *)
Notation "t ≻ u" := (term_App t u) (at level 42, left associativity, u at next level).
Notation "t 'ᵗ;' u" := (term_PatU t u) (at level 45, left associativity, u at next level).
Notation "t '≻case' 'ᵛ{' 'Inl' x1 ⟼ u1 , 'Inr' x2 ⟼ u2 '}'" := (term_PatS t x1 u1 x2 u2) (at level 59, x1 at level 19, x2 at level 19, u1 at level 59, u2 at level 59, right associativity).
Notation "t '≻case' 'ᵛ(' x1 ',' x2 ')' ⟼ u" := (term_PatP t x1 x2 u) (at level 59, x1 at level 19, x2 at level 19, u at level 59, right associativity).
Notation "t '≻case' 'ᴇ' m '⁔' x ⟼ u" := (term_PatE t m x u) (at level 59, m at level 29, x at level 19, u at level 59, right associativity).
Notation "t '≻map' x ⟼ u" := (term_Map t x u) (at level 59, x at level 19, u at level 59, right associativity).
Notation "'to⧔' t" := (term_ToA t) (at level 41, right associativity, t at level 41).
Notation "'from⧔' t" := (term_FromA t) (at level 41, right associativity, t at level 41).
Notation "'alloc' T" := (term_Alloc T) (at level 40, no associativity, T at next level).
Notation "t ⨞ 'ᵛ()'" := (term_FillU t) (at level 43, left associativity).
Notation "t ⨞ 'Inl'" := (term_FillL t) (at level 43, left associativity).
Notation "t ⨞ 'Inr'" := (term_FillR t) (at level 43, left associativity).
Notation "t ⨞ 'ᵛ(,)'" := (term_FillP t) (at level 43, left associativity).
Notation "t ⨞ 'ᴇ' m" := (term_FillE t m) (at level 43, left associativity, m at level 29).
Notation "t '⨞·' u" := (term_FillC t u) (at level 43, left associativity, u at next level).
Notation "t 'ᵗ[' x '≔' v ]" := (term_sub t x v) (at level 40, x at level 19, v at level 59, left associativity).

(* Bindings and contexts : 60 - 64 *)
Notation "'ᵛ' x 'ː' m '‗' T" := (bndr_V x m T) (at level 60, x at level 19, m at level 29, T at level 59, no associativity).
Notation "'⁺' h 'ː' m ⌊ T ⌋ n" := (bndr_D h m T n) (at level 60, h at level 19, m at level 29, T at level 59, n at level 29, no associativity).
Notation "'⁻' h 'ː' n '‗' T" := (bndr_H h n T) (at level 60, h at level 19, n at level 29, T at level 59, no associativity).

Notation "'ᶜ{' b , .. , c '}'" := (ctx_from_list (cons b .. (cons c nil) ..)) (at level 0, no associativity).
Notation "m 'ᶜ·' G" := (ctx_stimes m G) (at level 62, G at level 62, right associativity).
Notation "G '⨄' H" := (ctx_union G H) (at level 63, left associativity, H at next level).
Notation "G '⁻⨄⁺' H" := (ctx_interact G H) (at level 63, no associativity, H at next level).
Notation "ᶜ- G" := (ctx_minus G) (at level 61, no associativity, G at next level).

(* Effects : 60-64 *)
Notation "'ε'" := nil.
Notation "h '≔' v" := (hf_F h v) (at level 60, v at level 59, no associativity).
Infix "»" := app (at level 61, right associativity).

(* Typing and semantics : 70 - 79 *)
Notation "G 'ᵉ⫦' e" := (TyR_eff G e) (at level 70, e at level 64, no associativity).
Notation "G 'ᵉ⊢' e" := (Ty_eff G e) (at level 70, e at level 64, no associativity).
Notation "G 'ᵗ⫦' t 'ː' T" := (TyR_term G t T) (at level 70, t at level 59, T at level 59, no associativity).
Notation "G 'ᵗ⊢' t 'ː' T" := (Ty_term G t T) (at level 70, t at level 59, T at level 59, no associativity).
Notation "G 'ᶜ⊢' v ⋄ e 'ː' T" := (Ty_cmd G v e T) (at level 70, v at level 59, e at level 64, T at level 59, no associativity).

Notation "v1 '‿' D1 | e1 '⤋' v2 '‿' D2 | e2" := (Sem_eff v1 D1 e1 v2 D2 e2) (at level 70, D1 at level 64, e1 at level 64, v2 at level 59, D2 at level 64, e2 at level 64, no associativity).
Notation "t '‿' d '⇓' v ⋄ e" := (Sem_term t d v e) (at level 70, d at level 19, v at level 59, e at level 64, no associativity).

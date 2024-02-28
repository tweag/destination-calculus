Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.ext_nat.

Notation "⋆" := (nil).
Notation "d '.1'" := (d ++ (cons 1 nil)) (at level 18, right associativity).
Notation "d '.2'" := (d ++ (cons 2 nil)) (at level 18, right associativity).
Notation "d '.3'" := (d ++ (cons 3 nil)) (at level 18, right associativity).

Notation "'dyn' d" := (hdnm_D d) (at level 19, no associativity).
Notation "'static' hdmv" := (hdnm_S hdmv) (at level 19, no associativity).

Notation "'¹ν'" := (Some (pair Lin (Fin 0))).
Notation "'¹↑'" := (Some (pair Lin (Fin 1))).
Notation "'¹∞'" := (Some (pair Lin Inf)).

Notation "'ων'" := (Some (pair Ur (Fin 0))).
Notation "'ω↑'" := (Some (pair Ur (Fin 1))).
Notation "'ω∞'" := (Some (pair Ur Inf)).

Notation "'☠'" := None.

Infix "·" := mode_times (at level 21, right associativity).

(* Types : 30-59 *)
Notation "𝟏" := (type_U).
Notation "T ⨁ U" := (type_S T U) (at level 50, left associativity).
Notation "T ⨂ U" := (type_P T U) (at level 40, left associativity).
Notation "! m T" := (type_E m T) (at level 30, m at next level, right associativity).
Notation "T ⧔ U" := (type_A T U) (at level 55, left associativity).
Notation "T m → U" := (type_F T m U) (at level 59, m at next level, right associativity).
Notation "⌊ T ⌋ m" := (type_D T m) (at level 35, m at next level, no associativity).

(* Bindings and contexts : 60 - 64 *)
Notation "'ᵛ' x 'ː' m T" := (bndr_V x m T) (at level 60, m at next level, T at next level, no associativity).
Notation "'⁺' h 'ː' m ⌊ T ⌋ n" := (bndr_D h m T n) (at level 60, h at next level, m at next level, T at next level, n at next level, no associativity).
Notation "'⁻' h 'ː' n T" := (bndr_H h n T) (at level 60, h at next level, n at next level, T at next level, no associativity).

Notation "'ᶜ{' b , .. , c 'ᶜ}'" := (ctx_from_list (cons b .. (cons c nil) ..)) (at level 0, no associativity).
Notation "m 'ᶜ·' G" := (ctx_stimes m G) (at level 62, right associativity).
Notation "G '⨄' H" := (ctx_union G H) (at level 63, left associativity).
Notation "G '⁻⨄⁺' H" := (ctx_interact G H) (at level 63, no associativity).
Notation "ᶜ- G" := (ctx_minus G) (at level 61, no associativity).

(* Terms : 40-49 *)
Notation "t ≻ u" := (term_App t u) (at level 42, left associativity).
Notation "t 'ᵗ;' u" := (term_PatU t u) (at level 45, left associativity).
Notation "t '≻case' 'ᵛ{' 'Inl' x1 ⟼ u1 , 'Inr' x2 ⟼ u2 '}'" := (term_PatS t x1 u1 x2 u2) (at level 59, x1 at next level, x2 at next level, right associativity).
Notation "t '≻case' 'ᵛ(' x1 ',' x2 ')' ⟼ u" := (term_PatP t x1 x2 u) (at level 59, x1 at next level, x2 at next level, right associativity).
Notation "t '≻case' '⦆' m x ⟼ u" := (term_PatE t m x u) (at level 59, m at next level, x at next level, right associativity).
Notation "t '≻map' x ⟼ u" := (term_Map t x u) (at level 59, x at next level, right associativity).
Notation "'to⧔' t" := (term_ToA t) (at level 41, left associativity).
Notation "'from⧔' t" := (term_FromA t) (at level 40, left associativity).
Notation "'alloc' T" := (term_Alloc T) (at level 40, no associativity).
Notation "t ⨞ 'ᵛ()'" := (term_FillU t) (at level 43, left associativity).
Notation "t ⨞ 'Inl'" := (term_FillL t) (at level 43, left associativity).
Notation "t ⨞ 'Inr'" := (term_FillR t) (at level 43, left associativity).
Notation "t ⨞ 'ᵛ(,)'" := (term_FillP t) (at level 43, left associativity).
Notation "t ⨞ '⦆' m" := (term_FillE t m) (at level 43, left associativity).
Notation "t '⨞·' u" := (term_FillC t u) (at level 43, left associativity).
Notation "t 'ᵗ[' x '≔' v ]" := (term_sub t x v) (at level 40, x at next level, left associativity).

(* Values : 30-49 *)
Notation "'ᵛ-' h" := (val_H h) (at level 31, h at next level, no associativity).
Notation "'ᵛ+' h" := (val_D h) (at level 31, h at next level, no associativity).
Notation "'ᵛ()'" := (val_U).
Notation "'λ' x ⟼ t" := (val_F x t) (at level 59, x at next level, right associativity).
Notation "'Inl' v" := (val_L v) (at level 31, right associativity).
Notation "'Inr' v" := (val_R v) (at level 31, right associativity).
Notation "'⦆' m v" := (val_E m v) (at level 31, m at next level, right associativity).
Notation "'ᵛ(' v ',' w ')'" := (val_P v w) (at level 31, no associativity).
Notation "'⟨' v '❟' w '⟩' D" := (val_A v w D) (at level 31, no associativity, D at next level).
Notation "v 'ᵉ[' e ]" := (val_effapp v e) (at level 30, e at next level, no associativity).

Notation "'ε'" := nil.
Notation "h '≔' v" := (hf_A h v) (at level 20, no associativity).
Infix "»" := app (at level 21, right associativity).

Notation "G 'ᵉ⫦' e" := (TyR_eff G e) (at level 70, e at next level, no associativity).
Notation "G 'ᵗ⫦' t 'ː' T" := (TyR_term G t T) (at level 70, t at next level, T at next level, no associativity).
Notation "G 'ᵉ⊢' e" := (Ty_eff G e) (at level 70, e at next level, no associativity).
Notation "G 'ᵗ⊢' t 'ː' T" := (Ty_term G t T) (at level 70, t at next level, T at next level, no associativity).
Notation "G 'ᶜ⊢' v ⋄ e 'ː' T" := (Ty_cmd G v e T) (at level 70, v at next level, e at next level, T at next level, no associativity).

Notation "v1 D1 | e1 '⤋' v2 D2 | e2" := (Sem_eff v1 D1 e1 v2 D2 e2) (at level 70, D1 at next level, e1 at next level,  v2 at next level, D2 at next level, e2 at next level, no associativity).
Notation "t '‿' d '⇓' v ⋄ e" := (Sem_term t d v e) (at level 70, d at next level, v at next level, e at next level, no associativity).

Notation "T 'for_some' a" := (sigT (fun a => T)) (at level 98, a at next level, no associativity).
Notation "T 'for_some' a , b" := (sigT (fun a => (sigT (fun b => T)))) (at level 98, a at next level, b at next level, no associativity).
Notation "T 'for_some' a , b , c" := (sigT (fun a => (sigT (fun b => (sigT (fun c => T)))))) (at level 98, a at next level, b at next level, c at next level, no associativity).
Notation "T 'for_some' a , b , c , d" := (sigT (fun a => (sigT (fun b => (sigT (fun c => (sigT (fun d => T)))))))) (at level 98, a at next level, b at next level, c at next level, d at next level, no associativity).
Notation "T 'for_some' a , b , c , d , e" := (sigT (fun a => (sigT (fun b => (sigT (fun c => (sigT (fun d => (sigT (fun e => T)))))))))) (at level 98, a at next level, b at next level, c at next level, d at next level, e at next level, no associativity).

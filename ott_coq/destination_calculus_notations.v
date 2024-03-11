Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.ext_nat.

(* Var, holes and dests names : 15-19 *)
Notation "'ʰmax(' b , .. , c ')'" := (hdns_from_list (cons b .. (cons c nil) ..)) (at level 0, no associativity).

(* Hole names sets : 20-24 *)
Notation "'ʰ{' b , .. , c '}'" := (hdns_from_list (cons b .. (cons c nil) ..)) (at level 0, no associativity).
Notation "H1 '∪' H2" := (HdnsM.union H1 H2) (at level 24, left associativity, H2 at next level).
Notation "H 'ʰ⩲' h" := (hdns_incr_hnames H h) (at level 20, h at level 19, no associativity).
Notation "'ᶜhnames(' G ')'" := (hdns_from_ctx G) (at level 0, no associativity).
Notation "'ᵉhnames(' C ')'" := (hdns_from_ectx C) (at level 0, no associativity).

(* Var names : 15-19 *)

(* Mode names : 25-29 *)

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
Notation "T '↣' U" := (type_C T U) (at level 59, no associativity, U at level 59).

(* Values : 30-59 *)
Notation "'ᵛ-' h" := (val_H h) (at level 31, h at level 19, no associativity).
Notation "'ᵛ+' h" := (val_D h) (at level 31, h at level 19, no associativity).
Notation "'ᵛ()'" := (val_U).
Notation "'λᵛ' x '⁔' m ⟼ t" := (val_F x m t) (at level 59, m at level 29, x at level 19, t at level 59, right associativity).
Notation "'Inl' v" := (val_L v) (at level 31, right associativity, v at level 31).
Notation "'Inr' v" := (val_R v) (at level 31, right associativity, v at level 31).
Notation "'ᴇ' m '⁔' v" := (val_E m v) (at level 31, m at level 29, v at level 31, right associativity).
Notation "'ᵛ(' v ',' w ')'" := (val_P v w) (at level 0, v at level 59, w at level 59, no associativity).
Notation "H '⟨' v '❟' w '⟩'" := (val_A H v w) (at level 31, no associativity, v at level 59, w at level 59).
Notation "v 'ᵛ⩲' h " := (val_incr_hnames v h) (at level 30, h at level 19, no associativity).

(* Terms : 40-59 *)
Notation "t ≻ u" := (term_App t u) (at level 42, left associativity, u at next level).
Notation "t 'ᵗ;' u" := (term_PatU t u) (at level 45, left associativity, u at next level).
Notation "t '≻case' m '{Inl' x1 ⟼ u1 , 'Inr' x2 ⟼ u2 '}'" := (term_PatS t m x1 u1 x2 u2) (at level 59, m at level 29, x1 at level 19, x2 at level 19, u1 at level 59, u2 at level 59, right associativity).
Notation "t '≻case' m 'ᵛ(' x1 ',' x2 ')' ⟼ u" := (term_PatP t m x1 x2 u) (at level 59, m at level 29, x1 at level 19, x2 at level 19, u at level 59, right associativity).
Notation "t '≻case' m 'ᴇ' n '⁔' x ⟼ u" := (term_PatE t m n x u) (at level 59,  m at level 29, n at level 29, x at level 19, u at level 59, right associativity).
Notation "t '≻map' x ⟼ u" := (term_Map t x u) (at level 59, x at level 19, u at level 59, right associativity).
Notation "'to⧔' t" := (term_ToA t) (at level 41, right associativity, t at level 41).
Notation "'from⧔' t" := (term_FromA t) (at level 41, right associativity, t at level 41).
Notation "'alloc'" := (term_Alloc).
Notation "t '⨞()'" := (term_FillU t) (at level 43, left associativity).
Notation "t '⨞(λ' x '⁔' m '⟼' u ')'" := (term_FillF t x m u) (at level 43, m at level 29, x at level 19, u at level 59, left associativity).
Notation "t '⨞Inl'" := (term_FillL t) (at level 43, left associativity).
Notation "t '⨞Inr'" := (term_FillR t) (at level 43, left associativity).
Notation "t '⨞(,)'" := (term_FillP t) (at level 43, left associativity).
Notation "t '⨞ᴇ' m" := (term_FillE t m) (at level 43, left associativity, m at level 29).
Notation "t '⨞·' u" := (term_FillC t u) (at level 43, left associativity, u at next level).
Notation "t 'ˢ[' x '≔' v ]" := (term_sub t x v) (at level 40, x at level 19, v at level 59, left associativity).

(* Bindings and contexts : 60 - 64 *)
Notation "'ᵛ' x 'ː' m '‗' T" := (bndr_V x m T) (at level 60, x at level 19, m at level 29, T at level 59, no associativity).
Notation "'⁺' h 'ː' m ⌊ T ⌋ n" := (bndr_D h m T n) (at level 60, h at level 19, m at level 29, T at level 59, n at level 29, no associativity).
Notation "'⁻' h 'ː' T '‗' n" := (bndr_H h T n) (at level 60, h at level 19, n at level 29, T at level 59, no associativity).

Notation "'ᶜ{' b , .. , c '}'" := (ctx_from_list (cons b .. (cons c nil) ..)) (at level 0, no associativity).
Notation "m 'ᶜ·' G" := (ctx_stimes m G) (at level 62, G at level 62, right associativity).
Notation "G '⨄' H" := (ctx_union G H) (at level 63, left associativity, H at next level).
Notation "ᶜ- G" := (ctx_minus G) (at level 61, no associativity, G at next level).

(* Evaluation contexts and extended terms : 65-69 *)

Notation "'ᵉ[' ]" := ectx_Id.
Notation "H 'ᵒ⟨' v1 '❟' C" := (ectx_AOpen H v1 C) (at level 66, v1 at level 59, C at level 66, right associativity).
Notation "C '∘' D" := (ectx_Comp C D) (at level 67, D at level 67, right associativity).
Notation "C 'ᶠ[' h '≔' H '‗' v ]" := (ectx_fill C h H v) (at level 65, h at level 19, H at level 24, v at level 59, left associativity).

Notation "'ᵗ' t" := (eterm_ECtxApp ectx_Id t) (at level 65, t at level 59, no associativity).
Notation "C 'ʲ[' t ]" := (eterm_ECtxApp C t) (at level 65, t at level 59, no associativity).

(* Typing and semantics : 70 - 79 *)
Notation "G '⫦ᵛ' v 'ː' T" := (TyR_val G v T) (at level 70, v at level 59, T at level 59, no associativity).
Notation "G '⊢' j 'ː' T" := (Ty_eterm G j T) (at level 70, j at level 69, T at level 59, no associativity).
Notation "G '⫦ᵉ' C 'ː' T" := (TyR_ectx G C T) (at level 70, C at level 69, T at level 59, no associativity).

Notation "j ⟶ k" := (Sem_eterm j k) (at level 70, k at level 69, no associativity).


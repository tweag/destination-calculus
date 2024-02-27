Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.ext_nat.

Notation "'¹ν'" := (Some (pair Lin (Fin 0))).
Notation "'¹↑'" := (Some (pair Lin (Fin 1))).
Notation "'¹∞'" := (Some (pair Lin Inf)).

Notation "'ων'" := (Some (pair Ur (Fin 0))).
Notation "'ω↑'" := (Some (pair Ur (Fin 1))).
Notation "'ω∞'" := (Some (pair Ur Inf)).

Notation "'☠'" := None.

Infix "·" := md_times (at level 60, right associativity).
Notation "'𝟏'" := (typ_U).
Notation "T ⨁ U" := (typ_S T U) (at level 50, left associativity).
Notation "T ⨂ U" := (typ_P T U) (at level 40, left associativity).
Notation "! m T" := (typ_E m T) (at level 30, no associativity).
Notation "T m → U" := (typ_F T m U) (at level 60, right associativity).
Notation "m ⌊ T ⌋" := (typ_D m T) (at level 35, no associativity).

Notation "x '⁺:' m T" := (pas_V x m T) (at level 60, no associativity).
Notation "@ h '⁺:' m n ⌊ T ⌋" := (pas_D h m n T) (at level 60, no associativity).
Notation "h '⁻:' n T" := (nas_H h n T) (at level 60, no associativity).

Notation "'⁺{' p , .. , q '}'" := (pctx_from_list_unsafe (cons p .. (cons q nil) ..)) (at level 50, no associativity).
Notation "m '⁺·' G" := (pctx_stimes m G) (at level 60, right associativity).
Notation "G '⁺⨄' H" := (pctx_union G H) (at level 40, left associativity).

Notation "'⁻{' p , .. , q '}'" := (nctx_from_list_unsafe (cons p .. (cons q nil) ..)) (at level 50, no associativity).
Notation "m '⁻·' D" := (nctx_stimes m D) (at level 60, right associativity).
Notation "D '⁻⨄' E" := (nctx_union D E) (at level 40, left associativity).
Notation "'⁻-' G" := (nctx_minus G) (at level 35, no associativity).

Notation "t ≻ u" := (term_App t u) (at level 40, left associativity).
Notation "t ; u" := (term_PatU t u) (at level 50, left associativity).
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

Notation "'⟨' v '❟' w '⟩' D" := (val_A v w D) (at level 30, no associativity).
Notation "'@' h" := (val_D h) (at level 30, no associativity).
Notation "'()'" := (val_U).
Notation "'Inl' v" := (val_L v) (at level 30, right associativity).
Notation "'Inr' v" := (val_R v) (at level 30, right associativity).
Notation "( v '❟' w )" := (val_P v w) (at level 30, no associativity).
Notation "'⦆' m v" := (val_E m v) (at level 30, right associativity).
Notation "'λ' x ⟼ t" := (val_F x t) (at level 30, right associativity).

Notation "'ˣcast' v" := (xval_V v) (at level 30, no associativity).
Notation "'ˣλ' x ⟼ t" := (xval_V (val_F x t)) (at level 30, right associativity).
Notation "'ˣ@' h" := (xval_V (val_D h)) (at level 30, no associativity).
Notation "'ˣ()'" := (xval_V (val_U)).

Notation "'ˣ' h" := (xval_H h) (at level 30, no associativity).
Notation "'ˣ⟨' v '❟' w '⟩' D" := (xval_V (val_A v w D)) (at level 30, no associativity).
Notation "'ˣInl' w" := (xval_L w) (at level 30, right associativity).
Notation "'ˣInr' w" := (xval_R w) (at level 30, right associativity).
Notation "ˣ( w '❟' x )" := (xval_P w x) (at level 30, no associativity).
Notation "'ˣ⦆' m w" := (xval_E m w) (at level 30, right associativity).

Notation "w 'ˣ[' e ]" := (xval_effapp w e) (at level 29, no associativity).

Notation "'ε'" := nil.
Notation "h '≔' w" := (has_A h w) (at level 30, no associativity).
Infix "»" := app (at level 60, right associativity).

Notation "G '◡' D '⫦' e" := (Ty_eff G D e) (at level 60, no associativity).
Notation "G '⊢' v ⋄ e : T" := (Ty_cmd G v e T) (at level 60, no associativity).
Notation "G '◡' D '⫦' w : T" := (Ty_xval G D w T) (at level 60, no associativity).
Notation "G '⊢' t : T" := (Ty_term G t T) (at level 60, no associativity).

Notation "w1 D1 | e1 '⤋' w2 D2 | e2" := (Sem_eff w1 D1 e1 w2 D2 e2) (at level 60, no associativity).
Notation "t '⇓' v ⋄ e" := (Sem_term t v e) (at level 60, no associativity).

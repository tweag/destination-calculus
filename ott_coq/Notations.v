Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.ExtNat.

(* Var, holes and dests names : 15-19 *)
Notation "'maxᴴ(' H ')'" := (hname_max H) (at level 0, no associativity).
Notation "h 'ʰ[' H '⩲' k ] " := (hname_cshift h H k) (at level 15, H at level 24, k at level 19, no associativity).

(* Hole names sets : 21-24 *)
Notation "'ᴴ{' b , .. , c '}'" := (hnames_ (cons b .. (cons c nil) ..)) (at level 0, no associativity).
Notation "H1 '∪' H2" := (HNames.union H1 H2) (at level 24, left associativity, H2 at next level).
Notation "H 'ᴴ⩲' h" := (hnames_shift H h) (at level 21, h at level 19, no associativity).
Notation "'hnamesᴳ(' G ')'" := (hnames_ctx G) (at level 0, no associativity).
Notation "'hnames©(' C ')'" := (hnames_ectxs C) (at level 0, no associativity).

(* Terms : 40-59 *)
Notation "'ᵥ₎' v" := (term_Val v) (at level 40, no associativity).
Notation "'ₓ₎' x" := (term_Var x) (at level 40, no associativity).
Notation "t $ u" := (term_App t u) (at level 42, left associativity, u at next level).
Notation "t 'ᵗ;' u" := (term_PatU t u) (at level 45, right associativity, u at next level).
Notation "t '►caseˢ' m '{Inl' x1 ⟼ u1 , 'Inr' x2 ⟼ u2 '}'" := (term_PatS t m x1 u1 x2 u2) (at level 59, m at level 29, x1 at level 19, x2 at level 19, u1 at level 59, u2 at level 59, right associativity).
Notation "t '►caseᵖ' m 'ᵗ(' x1 ',' x2 ')' ⟼ u" := (term_PatP t m x1 x2 u) (at level 59, m at level 29, x1 at level 19, x2 at level 19, u at level 59, right associativity).
Notation "t '►caseᵉ' m 'ᴇ' n '⁔' x ⟼ u" := (term_PatE t m n x u) (at level 59,  m at level 29, n at level 29, x at level 19, u at level 59, right associativity).
Notation "t '►map' x ⟼ u" := (term_UpdA t x u) (at level 59, x at level 19, u at level 59, right associativity).
Notation "'to⧔' t" := (term_ToA t) (at level 41, right associativity, t at level 41).
Notation "'from⧔' t" := (term_FromA t) (at level 41, right associativity, t at level 41).
Notation "'alloc'" := (term_NewA).
Notation "t '⨞()'" := (term_FillU t) (at level 43, left associativity).
Notation "t '⨞Inl'" := (term_FillL t) (at level 43, left associativity).
Notation "t '⨞Inr'" := (term_FillR t) (at level 43, left associativity).
Notation "t '⨞(,)'" := (term_FillP t) (at level 43, left associativity).
Notation "t '⨞ᴇ' m" := (term_FillE t m) (at level 43, left associativity, m at level 29).
Notation "t '⨞(λ' x '⁔' m '⟼' u ')'" := (term_FillF t x m u) (at level 43, m at level 29, x at level 19, u at level 59, left associativity).
Notation "t '⨞·' u" := (term_FillComp t u) (at level 43, left associativity, u at next level).
Notation "t '◀' u" := (term_FillLeaf t u) (at level 43, left associativity, u at next level).
Notation "t 'ᵗ[' x '≔' v ]" := (term_sub t x v) (at level 40, x at level 19, v at level 59, left associativity).

Notation "'from⧔'' t" := (sterm_FromA' t) (at level 41, right associativity, t at level 41).
Notation "ˢ()" := (sterm_Unit).
Notation "'ˢλ' x '⁔' m '⟼' u" := (sterm_Fun x m u) (at level 59, m at level 29, x at level 19, u at level 59, right associativity).
Notation "'ˢInl' t" := (sterm_Left t) (at level 31, right associativity, t at level 31).
Notation "'ˢInr' t" := (sterm_Right t) (at level 31, right associativity, t at level 31).
Notation "'ˢᴇ' m '⁔' t" := (sterm_Exp m t) (at level 31, m at level 29, t at level 31, right associativity).
Notation "'ˢ(' t ',' u ')'" := (sterm_Prod t u) (at level 0, t at level 59, u at level 59, no associativity).

(* Values : 30-59 *)
Notation "'ᵛ+' h" := (val_Hole h) (at level 31, h at level 19, no associativity).
Notation "'ᵛ-' h" := (val_Dest h) (at level 31, h at level 19, no associativity).
Notation "'ᵛ()'" := (val_Unit).
Notation "'ᵛλ' x '⁔' m ⟼ t" := (val_Fun x m t) (at level 59, m at level 29, x at level 19, t at level 59, right associativity).
Notation "'Inl' v" := (val_Left v) (at level 31, right associativity, v at level 31).
Notation "'Inr' v" := (val_Right v) (at level 31, right associativity, v at level 31).
Notation "'ᴇ' m '⁔' v" := (val_Exp m v) (at level 31, m at level 29, v at level 31, right associativity).
Notation "'ᵛ(' v ',' w ')'" := (val_Prod v w) (at level 0, v at level 59, w at level 59, no associativity).
Notation "H '⟨' v '❟' w '⟩'" := (val_Ampar H v w) (at level 31, no associativity, v at level 59, w at level 59).
Notation "v 'ᵛ[' H '⩲' k ] " := (val_cshift v H k) (at level 30, H at level 24, k at level 19, no associativity).

(* Evaluation context stack : 60 - 64 *)
Notation "'©️⬜'" := nil.
Notation "C '∘' c" := (cons c C) (at level 63, left associativity, c at next level).
Notation "C '©️[' h '≔' H '‗' v ]" := (ectxs_fill C h H v) (at level 61, h at level 19, H at level 24, v at level 59, left associativity).

(* Evaluation contexts : 40-59 *)
Notation "'⬜►' u" := (ectx_App1 u) (at level 42, no associativity, u at next level).
Notation "v '►⬜'" := (ectx_App2 v) (at level 42, no associativity).
Notation "⬜; u" := (ectx_PatU u) (at level 45, no associativity, u at next level).
Notation "'⬜►caseˢ' m '{Inl' x1 ⟼ u1 , 'Inr' x2 ⟼ u2 '}'" := (ectx_PatS m x1 u1 x2 u2) (at level 59, m at level 29, x1 at level 19, x2 at level 19, u1 at level 59, u2 at level 59, no associativity).
Notation "'⬜►caseᵖ' m 'ᵗ(' x1 ',' x2 ')' ⟼ u" := (ectx_PatP m x1 x2 u) (at level 59, m at level 29, x1 at level 19, x2 at level 19, u at level 59, no associativity).
Notation "'⬜►caseᵉ' m 'ᴇ' n '⁔' x ⟼ u" := (ectx_PatE m n x u) (at level 59,  m at level 29, n at level 29, x at level 19, u at level 59, no associativity).
Notation "'⬜►map' x ⟼ u" := (ectx_UpdA x u) (at level 59, x at level 19, u at level 59, no associativity).
Notation "'to⧔⬜'" := (ectx_ToA) (at level 41, no associativity).
Notation "'from⧔⬜'" := (ectx_FromA) (at level 41, no associativity).
Notation "'⬜⨞()'" := (ectx_FillU) (at level 43, no associativity).
Notation "'⬜⨞Inl'" := (ectx_FillL) (at level 43, no associativity).
Notation "'⬜⨞Inr'" := (ectx_FillR) (at level 43, no associativity).
Notation "'⬜⨞(,)'" := (ectx_FillP) (at level 43, no associativity).
Notation "'⬜⨞ᴇ' m" := (ectx_FillE m) (at level 43, no associativity, m at level 29).
Notation "'⬜⨞(λ' x '⁔' m '⟼' u ')'" := (ectx_FillF x m u) (at level 43, m at level 29, x at level 19, u at level 59, no associativity).
Notation "'⬜⨞·' u" := (ectx_FillComp1 u) (at level 43, no associativity, u at next level).
Notation "v '⨞·⬜'" := (ectx_FillComp2 v) (at level 43, no associativity).
Notation "'⬜◀' u" := (ectx_FillLeaf1 u) (at level 43, no associativity, u at next level).
Notation "v '◀⬜'" := (ectx_FillLeaf2 v) (at level 43, no associativity).
Notation "H 'ᵒᵖ⟨' v1 '❟⬜⟩'" := (ectx_OpenAmpar H v1) (at level 31, v1 at level 59, no associativity).

(* Types : 30-59 *)
Notation "①" := (type_Unit).
Notation "T ⨁ U" := (type_Sum T U) (at level 50, left associativity, U at next level).
Notation "T ⨂ U" := (type_Prod T U) (at level 40, left associativity, U at next level).
Notation "! m '⁔' T" := (type_Exp m T) (at level 30, m at level 29, right associativity, T at level 30).
Notation "T ⧔ U" := (type_Ampar T U) (at level 55, left associativity, U at next level).
Notation "T '⁔' m '→' U" := (type_Fun T m U) (at level 59, m at level 29, right associativity, U at level 59).
Notation "⌊ T ⌋ m" := (type_Dest T m) (at level 35, T at level 59, m at level 29, no associativity).

(* Mode : 25-29 *)
Notation "'¹ν'" := (Some (pair Lin (Fin 0))).
Notation "'¹↑'" := (Some (pair Lin (Fin 1))).
Notation "'¹∞'" := (Some (pair Lin Inf)).

Notation "'ων'" := (Some (pair Ur (Fin 0))).
Notation "'ω↑'" := (Some (pair Ur (Fin 1))).
Notation "'ω∞'" := (Some (pair Ur Inf)).

Notation "'☠'" := None.

Infix "·" := mode_times (at level 25, right associativity).

(* Bindings and contexts : 60 - 64 *)

Notation "'ˣ' x" := (name_Var x) (at level 20, x at level 19, no associativity).
Notation "'ʰ' h" := (name_DH h) (at level 20, h at level 19, no associativity).

Notation "'ₓ' m '‗' T" := (binding_Var m T) (at level 60, m at level 29, T at level 59, no associativity).
Notation "'₋' m '⌊' T '⌋' n" := (binding_Dest m T n) (at level 60, m at level 29, T at level 59, n at level 29, no associativity).
Notation "'₊' T '‗' n" := (binding_Hole T n) (at level 60, T at level 59, n at level 29, no associativity).

Notation "'ᴳ{}'" := (ctx_empty).
Notation "'ᴳ{' x ':' m '‗' T '}'" := (ctx_singleton (name_Var x) (binding_Var m T)) (at level 1, x at level 19, m at level 29, T at level 59, no associativity).
Notation "'ᴳ{-' h ':' m ⌊ T ⌋ n '}'" := (ctx_singleton (name_DH h) (binding_Dest m T n)) (at level 0, h at level 19, m at level 29, T at level 59, n at level 29, no associativity).
Notation "'ᴳ{+' h ':' T '‗' n '}'" := (ctx_singleton (name_DH h) (binding_Hole T n)) (at level 0, h at level 19, T at level 59, n at level 29, no associativity).
Notation "m 'ᴳ·' G" := (stimes m G) (at level 63, G at level 63, right associativity).
Notation "G 'ᴳ+' H" := (union G H) (at level 64, left associativity, H at next level).
Notation "'ᴳ-⁻¹' G" := (hminus_inv G) (at level 62, no associativity, G at next level).
Notation "'ᴳ-' G" := (hminus G) (at level 62, no associativity, G at next level).
Notation "G 'ᴳ[' H '⩲' k ]" := (ctx_cshift G H k) (at level 61, H at level 24, k at level 19, no associativity).

(* Typing and semantics : 70 - 79 *)

Notation "G '⫦' v ':' T" := (Ty_val G v T) (at level 70, v at level 59, T at level 59, no associativity).
Notation "P '⊢' t ':' T" := (Ty_term P t T) (at level 70, t at level 59, T at level 59, no associativity).
Notation "P 'ˢ⊢' t ':' T" := (Ty_sterm P t T) (at level 70, t at level 59, T at level 59, no associativity).
Notation "D '⊣' C ':' T1 '↣' T2" := (Ty_ectxs D C T1 T2) (at level 70, C at level 64, T1 at level 59, T2 at level 59, no associativity).
Notation "'⊢' C 'ʲ[' t ] : T" := (Ty C t T) (at level 70, C at level 64, t at level 59, T at level 59, no associativity).
Notation "C 'ʲ[' t ] '⟶' C2 'ʲ[' t2 ]" := (Sem C t C2 t2) (at level 70, t at level 59, C2 at level 64, t2 at level 59, no associativity).

Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.

Theorem TypeSafety : forall (G : ctx) (t : term) (T : type) (d : hddyn), (G ᵗ⊢ t ː T) -> (exists v e, (t ‿d ⇓ v ⋄ e) /\ (G ᶜ⊢ v ⋄ e ː T)).
Proof.
    intros G t T d TYt. destruct TYt. inversion TYRt.
    - (* TyR_term_H *) give_up.
    - (* TyR_term_D *) give_up.
    - (* TyR_term_U *) give_up.
    - (* TyR_term_L *) give_up.
    - (* TyR_term_R *) give_up.
    - (* TyR_term_P *) give_up.
    - (* TyR_term_E *) give_up.
    - (* TyR_term_A *) give_up.
    - (* TyR_term_F *) give_up.
    - (* TyR_term_Var *) give_up.
    - (* TyR_term_App *) give_up.
    - (* TyR_term_PatU *) give_up.
    - (* TyR_term_PatS *) give_up.
    - (* TyR_term_PatP *) give_up.
    - (* TyR_term_PatE *) give_up.
    - (* TyR_term_Map *) give_up.
    - (* TyR_term_FillC *) give_up.
    - (* TyR_term_FillU *) give_up.
    - (* TyR_term_FillL *) give_up.
    - (* TyR_term_FillR *) give_up.
    - (* TyR_term_FillP *) give_up.
    - (* TyR_term_FillE *) give_up.
    - (* TyR_term_Alloc *) give_up.
    - (* TyR_term_ToA *) give_up.
    - (* TyR_term_FromA *) give_up.
Admitted.

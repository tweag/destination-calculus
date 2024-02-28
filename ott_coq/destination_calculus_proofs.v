Require Import List.
Require Import Ott.ott_list_core.
Require Import Ott.destination_calculus_ott.
Require Import Ott.destination_calculus_notations.
Require Import Ott.ext_nat.

Theorem type_safety : forall (G : ctx) (t : term) (T : type) (d : hddyn), (G ᵗ⊢ t ː T) -> ((t d ⇓ v ⋄ e) /\ (G ᶜ⊢ v ⋄ e ː T) for_some v, e).

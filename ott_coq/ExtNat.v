Require Import Ott.ott_list_core.
Require Import Arith.

Inductive ext_nat : Type :=
    | Fin : nat -> ext_nat
    | Inf : ext_nat.

Definition ext_plus (m n : ext_nat) : ext_nat :=
  match m, n with
  | Inf, _ => Inf
  | _, Inf => Inf
  | Fin m', Fin n' => Fin (m' + n')
  end.

Definition ext_plus' (l : list ext_nat) : ext_nat :=
  List.fold_left ext_plus l (Fin 0).

Theorem ext_eq_dec : forall m n : ext_nat, {m = n} + {m <> n}.
Proof.
  decide equality.
  apply eq_nat_dec.
Defined.

Definition ext_eqb (m n : ext_nat) : bool :=
  match ext_eq_dec m n with
  | left _ => true
  | right _ => false
  end.

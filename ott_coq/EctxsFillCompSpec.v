Require Import List.
Require Import Ott.ott_list_core.
Require Import Dest.destination_calculus_ott.
Require Import Dest.Notations.
Require Import Dest.Lemmas.
Require Import Dest.ExtNat.
Require Import Coq.Program.Equality.
Require Import Dest.Finitely.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
(* ⬇️ for the `impl` relation. *)
Require Coq.Program.Basics.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Compare_dec.
Require Import Arith.
Require Import Lia.

Lemma ectxs_fillComp_spec' : forall (C : ectxs) (h : hname) (v : val) (D2 D3: ctx) (U: type), DestOnly D2 -> DestOnly D3 -> D2 # D3 -> D2 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } -> D3 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  LinOnly D3 ->
  FinAgeOnly D3 ->
  ValidOnly D3 ->
  D2 ᴳ+ (ᴳ-⁻¹ D3) ⫦ v : U ->
  forall (m0 : mode) (T U0 : type) (D1: ctx),
  IsValid m0 ->
  DestOnly D1 ->
  D1 # D2 ->
  D1 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν }) ⊣ C : T ↣ U0 ->
  D1 ᴳ+ m0 ᴳ· D3 ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T ↣ U0.
Proof.
  intros * DestOnlyD2 DestOnlyD3 DisjointD2D3 DisjointD2h DisjointD3h HDisjointCD3 LinOnlyD3 FinAgeOnlyD3 ValidOnlyD3 Tyv. induction C.
  - intros * Validm0 DestOnlyD1 DisjointD1D2 DisjointD1D3 DisjointD1h TyC.
    dependent destruction TyC. (* Prove that union of singleton + other things is not the empty context *) admit.
  - intros * Validm0 DestOnlyD1 DisjointD1D2 DisjointD1D3 DisjointD1h TyC.
    destruct a; simpl; dependent destruction TyC.
    * (* Ty-ectxs-App1 *)
      assert (LinOnly (m ᴳ· (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν})) ᴳ+ D4) /\ FinAgeOnly (m ᴳ· (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν})) ᴳ+ D4)) as (LinOnlyD & FinAgeOnlyD).
        { apply Ty_ectxs_LinOnly_FinAgeOnly with (C := C) (T := U1) (U0 := U0). tauto. }
      assert (HNames.Subset hnamesᴳ(m ᴳ· (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν})) ᴳ+ D4) hnames©(C)) as HDisjointCD4.
        { apply hnames_C_wk_hnames_G with (T := U1) (U0 := U0); trivial. }
      assert ((m ᴳ· (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν})) ᴳ+ D4) # D3).
        { apply HDisjoint_to_Disjoint. supercrush. apply HSubset_preserves_HDisjoint with (H2 := hnames©( C)); trivial. }
      constructor 2 with (D2 := D4) (m := m) (U := U1); trivial.
        { supercrush. } { supercrush. }
        { replace (m ᴳ· (D1 ᴳ+ m0 ᴳ· D3) ᴳ+ D4) with (m ᴳ· D1 ᴳ+ D4 ᴳ+ m · m0 ᴳ· D3). apply IHC with (D1 := m ᴳ· D1 ᴳ+ D4) (m0 := m · m0); swap 1 7.
          replace (m ᴳ· D1 ᴳ+ D4 ᴳ+ m · m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν})) with (m ᴳ· (D1 ᴳ+ m0 ᴳ· (¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν})) ᴳ+ D4). assumption.
          { rewrite 1 stimes_distrib_on_union. rewrite <- 1 union_associative. rewrite union_commutative with (G2 := D4). rewrite 1 union_associative. rewrite <- stimes_is_action. reflexivity. }
          { crush. } { crush. } { supercrush. } { supercrush. } { supercrush. } { assumption. } { rewrite stimes_distrib_on_union. rewrite stimes_is_action. rewrite <- union_associative. rewrite union_commutative with (G1 := D4). rewrite union_associative. reflexivity. }
        }
    * (* Ty-ectxs-App2 *)
      give_up.
Admitted.

Lemma ectxs_fillComp_spec : forall (D1 D2 D3: ctx) (h : hname) (C : ectxs) (T U U0 : type) (v : val),
  DestOnly D1 ->
  DestOnly D2 ->
  DestOnly D3 ->
  D1 # D2 ->
  D1 # D3 ->
  D2 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  D2 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  D3 # ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  LinOnly D3 ->
  FinAgeOnly D3 ->
  ValidOnly D3 ->
  D1 ᴳ+ ¹↑ ᴳ· D2 ᴳ+ ᴳ{- h : ¹ν ⌊ U ⌋ ¹ν } ⊣ C : T ↣ U0 ->
  D2 ᴳ+ (ᴳ-⁻¹ D3) ⫦ v : U ->
  D1 ᴳ+ D3 ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T ↣ U0.
Proof.
  intros * DestOnlyD1 DestOnlyD2 DestOnlyD3 DisjointD1D2 DisjointD1D3 DisjointD2D3 DisjointD1h DisjointD2h DisjointD3h HDisjointCD3 LinOnlyD3 FinAgeOnlyD3 ValidOnlyD3 TyC Tyv. rewrite 1 stimes_linnu_eq with (G := D3). rewrite hnames_stimes_eq. apply ectxs_fillComp_spec' with (U := U) (D2 := D2); trivial. apply IsValid_linnu'. rewrite <- stimes_linnu_eq. rewrite union_associative. assumption.
Qed.

(* ========================================================================= *)

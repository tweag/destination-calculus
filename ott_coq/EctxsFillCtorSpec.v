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

Lemma ectxs_fillCtor_spec : forall (D1 D3: ctx) (h : hname) (C : ectxs) (n : mode) (T T' U0 : type) (v : val),
  IsValid n -> 
  DestOnly D1 ->
  DestOnly D3 ->
  D1 # D3 ->
  D1 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  D3 # ᴳ{- h : ¹ν ⌊ T ⌋ n } ->
  hnames©(C) ## hnamesᴳ( D3) ->
  LinOnly D3 ->
  FinAgeOnly D3 ->
  ValidOnly D3 ->
  D1 ᴳ+ ᴳ{- h : ¹ν ⌊ T ⌋ n } ⊣ C : T' ↣ U0 ->
  (ᴳ-⁻¹ D3) ⫦ v : T ->
  D1 ᴳ+ (ᴳ- (n ᴳ· (ᴳ-⁻¹ D3))) ⊣ C ©️[ h ≔ hnamesᴳ( D3) ‗ v ] : T' ↣ U0.
Proof. Admitted.

(* ========================================================================= *)

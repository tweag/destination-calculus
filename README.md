# Destination Calculus: A Linear λ−Calculus for Purely Functional Memory Writes

By Thomas Bagrel and Arnaud Spiwack.

## Proofs

1. [Introduction](#introduction)
2. [Hardware Dependencies](#hardware-dependencies)
3. [Getting Started Guide](#getting-started-guide)  
  3.1. [Get dependencies and check the proofs in one step with Nix](#get-dependencies-and-check-the-proofs-in-one-step-with-nix)  
  3.2. [Manually installing dependencies](#manually-installing-dependencies)
4. [Step by Step Instructions](#step-by-step-instructions)
5. [Reusability Guide](#reusability-guide)

### Introduction

In addition to the article, this repository contains the formalization of the destination calculus as described in sections 5 and 6 of the paper, using the [Coq proof assistant](https://coq.inria.fr/).

The main reproducible results are the machine-verified proofs of the following type-safety theorems for the destination calculus:

**Type preservation**

_If ⊢ C [t] : T and C[t] ⟶ C'[t'] then ⊢ C' [t'] : T_.

**Progress**

_If ⊢ C [t] : T and ∀ v, C [t] ≠ [][v] then ∃ C', t'. C [t] ⟶ C' [t']_.

### Hardware Dependencies

The proof can be checked on any recent hardware with no specific requirements. On a laptop with Intel i7-1165G7 and Kubuntu 22.04, it takes about 25 minutes to check all the proofs.

### Getting Started Guide

#### Get dependencies and check the proofs in one step with Nix

The easiest way to check the proofs is to use [Nix](https://nix.dev/install-nix#install-nix). If you have [Nix](https://nix.dev/install-nix#install-nix) installed and [Make](https://www.gnu.org/software/make/#download), you can simply run

```bash
make nix
```

It should pull the dependencies listed in `flake.nix`/`flake.lock`(including the right Coq version) and check the proofs.

#### Manually installing dependencies

If you don't want to use Nix, you can still check the proofs manually. You will need to install the following dependencies:

**System dependencies**

+ `make`
+ `opam` (version 2.0.0)
+ `ott` (version 0.33)

**OCaml dependencies (listed in `destination.opam`)**

+ `coq` (version 8.18.0)
+ `coq-hammer`
+ `coq-ott`

### Step by Step Instructions

If using Nix:

```bash
make nix
```

otherwise:

```bash
make -j coq
```

Here's the kind of output you should obtain:

```bash
$ make nix
## ---------------------------------- OUTPUT ---------------------------------- #

[... dependencies installation ...]

nix --extra-experimental-features 'nix-command flakes' develop --command make -j
make[1]: Entering directory '[redacted]'
coq_makefile -f _CoqProject -o Makefile.coq
ott -tex_show_meta true -tex_wrap false -picky_multiple_parses false -tex_suppress_ntr Q -o ott_coq/destination_calculus_ott.v grammar.ott rules.ott
Ott version 0.33   distribution of Mon 16 Jan 15:32:01 GMT 2023
Warning: warning: indexvar "k" is primary so may give a name-clash

Definition rules:        114 good    0 bad
Definition rule clauses: 343 good    0 bad
sed -i 's/: Set/: Type/g' ott_coq/destination_calculus_ott.v
make TIMED=1 -f Makefile.coq
make[2]: Entering directory '[redacted]'
COQDEP VFILES
COQC ott_coq/Finitely.v
COQC ott_coq/Permutation.v
COQC ott_coq/ExtNat.v
ott_coq/ExtNat.vo (real: 0.25, user: 0.18, sys: 0.06, mem: 179352 ko)
ott_coq/Permutation.vo (real: 0.56, user: 0.42, sys: 0.13, mem: 416520 ko)
ott_coq/Finitely.vo (real: 3.69, user: 3.50, sys: 0.15, mem: 482744 ko)
COQC ott_coq/destination_calculus_ott.v
ott_coq/destination_calculus_ott.vo (real: 0.83, user: 0.68, sys: 0.15, mem: 484492 ko)
COQC ott_coq/Notations.v
ott_coq/Notations.vo (real: 0.53, user: 0.41, sys: 0.12, mem: 413528 ko)
COQC ott_coq/Lemmas.v
ott_coq/Lemmas.vo (real: 77.76, user: 77.27, sys: 0.38, mem: 948528 ko)
COQC ott_coq/TySterm.v
COQC ott_coq/Progress.v
COQC ott_coq/TyValFill.v
COQC ott_coq/TermSubSpec1.v
ott_coq/TySterm.vo (real: 16.91, user: 16.24, sys: 0.58, mem: 472232 ko)
ott_coq/Progress.vo (real: 25.53, user: 24.76, sys: 0.67, mem: 517340 ko)
ott_coq/TyValFill.vo (real: 54.69, user: 54.35, sys: 0.29, mem: 647024 ko)
COQC ott_coq/EctxsFillLeafSpec.v
COQC ott_coq/EctxsFillCtorSpec.v
COQC ott_coq/EctxsFillCompSpec.v
ott_coq/TermSubSpec1.vo (real: 352.34, user: 350.55, sys: 1.16, mem: 982812 ko)
COQC ott_coq/TermSubSpec2.v
ott_coq/TermSubSpec2.vo (real: 8.24, user: 7.72, sys: 0.51, mem: 476000 ko)
ott_coq/EctxsFillCtorSpec.vo (real: 620.89, user: 618.53, sys: 1.30, mem: 1123200 ko)
ott_coq/EctxsFillLeafSpec.vo (real: 764.30, user: 761.58, sys: 2.02, mem: 1938532 ko)
ott_coq/EctxsFillCompSpec.vo (real: 909.48, user: 906.90, sys: 1.48, mem: 1637480 ko)
COQC ott_coq/Preservation.v
ott_coq/Preservation.vo (real: 281.83, user: 281.00, sys: 0.80, mem: 1502664 ko)

COQC ott_coq/Check.v
Axioms:
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
Axioms:
ProofIrrelevance.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
ott_coq/Check.vo (real: 3.02, user: 2.86, sys: 0.16, mem: 543136 ko)

make[2]: Leaving directory '[redacted]'
make[1]: Leaving directory '[redacted]'
```

### Reusability Guide

+ `grammar.ott` and `rules.ott` contain the grammar of destination calculus and the typing and semantic rules. It is compiled by [Ott](https://github.com/ott-lang/ott) to autogenerate Coq definitions in `ott_coq/destination_calculus_ott.v` (this file will be created during build)
+ `ott_coq/` contains all the Coq files for the proof:
  + `Finitely.v` contains the definition and lemmas for typing contexts (finite dependent functions used as maps)
  + `Permutation.v` contains a few lemmas for permutations of lists, that are used in the proof when hole names are renamed
  + `ExtNat.v` contains the definition of natural numbers extended with infinity, to implement ages
  + `destination_calculus_ott.v` will be autogenerated at build time by Ott, and will contain the Coq definition of all language constructs and typing / semantic rules of destination calculus
  + `Notations.v` contains some Unicode notations for Coq, close to the one used in the paper (with some extra disambiguation symbols) to make the proofs more readable
  + `Lemmas.v` contains most of the small lemmas that are used in other proofs (a lot of them are used to prove typing contexts properties)
  + `TySterm.v` is the proof of derived typing rules for syntactic sugar constructs
  + `Progress.v` is the proof of progress for destination calculus: _If ⊢ C[t] : T and ∀v, C[t] ≠ [][v] then ∃C′, t′. C[t] → C′[t′]_. It depends only on `Lemmas.v`.
  + `TyValFill.v` contains the fill lemma when a value is written to the hole inside a value with holes
  + `EctxsFillLeafSpec.v`, `EctxsFillCtorSpec.v` and `EctxsFillCompSpec.v` are the proofs of substitution lemmas for hole names inside evaluation contexts; they all depend on `TyValFill.v`
  + `TermSubSpec1.v` and `TermSubSpec2.v` are the proofs of substitution lemmas for variable inside terms
  + `Preservation.v` is the proof of preservation for destination calculus: _If ⊢ C[t] : T and C[t] → C′[t′] then ⊢ C′[t′] : T_. It depends on `Lemmas.v` and all the substitution lemmas.
  + `Check.v` is compiled last in the project, and prints the exhaustive list of assumptions/axioms that are used in progress and preservation proofs (and all the lemmas that they transitively depend on). Next section includes the expected output of this module

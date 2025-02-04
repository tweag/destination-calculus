We tried to generate a latexdiff for the article, but after several hours, we couldn't succeed, probably due to some OTT macros conflicting with the tool. We apologize for that and instead, we provide the plain git diff for our main latex file, as well as a detailed changelog below:

- We clarified the goal of λd as soon as line 70 in introduction, as well as in related work section about Bagrel2024, as required by the meta-review.
- We added a section on tail-recursive map on lists that is made possible by destinations (see new section 2.2), as required by the meta-review.
- Section 3 "Scope escape of destinations" (section 3) introduced a great deal of new notations, so we added some introductory words about them, as pointed out by reviewer B.
- We reworked section 5 "Type system" quite deeply, as required by the meta-review:
  + We added a long introduction on graded modalities/graded modal systems including an example about scope control.
  + We worked towards a more comprehensive and complete description of the modes of λd (section 5.1), including their algebraic rules, ordering, and why we need that structure in our system.
  + About the naming of the structure, after some more research on the subject, we've elected to keep the “semiring” terminology. It turns out that it's the most common terminology for our algebraic structure (see for instance https://ncatlab.org/nlab/show/semiring). The terminology clash with the structure with a zero (which can be unambiguously referred to as “rig”) is unfortunate, but “ringoid” is such an obscure, much rarer terminology, that we felt it would be more confusing to adopt it. We added a footnote on bottom of page 11 to justify that choice.
  + We also reworked the figure about scopes to be more concrete and less ambiguous.
- We precised how our approach of explicit evaluation contexts relates to existing work, as pointed out by reviewer B.
- We also tried to concentrate all the formalism on fewer figures, as pointed out by reviewer B:
  + We consolidated all the grammar of λd and meta-operations on syntax on one figure, and all the type system in another.
  + We consolidated all the figures related to runtime values and the new typing context forms for operational semantics in one figure.
  + We consolidated grammar and typing rules of evaluation contexts in one figure.
  + We consolidated semantic rules and meta operations relative to semantics in one figure.
  We also made sure that all operators and meta operations are now shown in figures next to their use site when that is possible, instead of being lost in the middle of the text. In the end we went from 12(14) figures down to 9(11) figures.
- We added a paragraph about linked data structures in section 8 "Implementation of λd using in-place memory mutations", as required by the meta-review.
- The section "Design motivation behind the ampar and destination types" (previous section 5.2) was a bit rough especially this early in the paper, as pointed out by several reviewers. We removed it from section 5, and merged most of its content with discussion about Minamide's system in related works (section 9.3).
- We added a section comparing our system of ages with Rust lifetimes (new section 9.6), as required by the meta-review.
- We also added a section about Oxidizing Ocaml and how their notion of locality compares to our ages (new section 9.7), as required by the meta-review.

**Renamings and visual changes:**

- operator `alloc` has been changed to `new⧔` as this operator is not really the place where allocation happens in a linked data structure setting;
- operator `alloc'` (in section 3) has been changed to `alloc` as this name is now free;
- modality constructor `ᴇ m` has been changed to `Mod m` so it's easier to read;
- operator `map` has been changed to `upd⧔` as reviewer C pointed out that `map` is not really specific enough for our use-case;
- function arrow `→` has been changed to `⊸` to better emphasize that functions are linear by default in λd;
- notations for evaluation contexts `C`, `c` has been changed to `E`, `e` for more familiarity;
- we added type hints on some use sites of `new⧔` as suggested by reviewer B;
- ordering on modes `<:` has been changed to `⥶` to indicate the direction in which coercion can happen.

Also, we had left some of reviewer C's question unanswered in our earlier response, we would like to apologize and offer answers here:

> line 317: "Destinations as first-class values are very much required" In what sense is this known to be true? Do you really mean that the existing systems cannot express this code but yours can? Or is there some stronger claim that no language without first-class destinations could express this?

Yes, we state that we need a system in which destinations can be reordered and stored in a data structure like a queue, with the structure with holes having an unbounded number of holes, to make this example possible. Alternatively, imperative mutable references would suffice. In systems like Minamide's one or Lorenzen & al. _The Functional Essence of Imperative Binary Search Trees_ we don't have enough flexibility.

> line 384: Is the arrow notation just a convenience?

Yes, mostly. It doesn't add any extra expressivity to the system; it just let us take an argument with mode other than `¹ν` without needing explicit boxing in modality `Mod m`. As in λd, every variable must be assigned a mode in the typing context (unlike some older systems where contexts held two kinds of bindings: those with modes, and the plain linear bindings with no modes), it's rather natural to let that mode be any `m` when building a lambda abstraction instead of forcing it to be `¹ν`.

> "where [.] is analogous to dualisation" it's not clear to me that it formally IS a dualisation?

We've made it more explicit in the text, now part of section 9.3, that `S ⋉ ⌊T⌋` is a classical reinterpretation of `(T,S) hfun`, in the same way that `S par T^⟂` is a classical reinterpretation of `T ⊸ S`. Following this idea, `⌊·⌋` plays a role very analogous to `·^⟂`, which is the dualisation operator of linear logic that we were referring to in the original sentence. For instance, one way of eliminating `⌊T⌋` is by filling it with a `T`.

> Regarding related work, in the untyped setting, Racket placeholders play a quite similar role to destinations, though they are not intended for efficient construction, but rather for the construction of structures with DAG-like joins and graph-like cycles. I wonder if some extension of this language could support such constructions as well, but with static type guarantees?

It's really not clear how we would achieve that. A key ingredient that make our system sound is that while we modify a structure with holes through its destinations, we are temporarily no longer allowed to refer to the structure itself. It's very reminiscent of Rust, where a structure cannot be used or moved while a mutable borrow on it is live. And that mutual exclusion is very much required for the safety of the system. Unfortunately, that forbids self-referential structs. But they would be problematic in λd anyway: they don't behave well with respects to linearity, and deciding whether all destinations have been filled or not on a self-referential struct would be hard to do (as usually, when composing structure with holes, we join the remaining destinations of the two structures... here we would have to prevent destination duplication when composing a structure with itself).
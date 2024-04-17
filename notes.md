## Some outliny things for the article

1. Mini-examples (artificial examples, include difference-list
   contactenation, maybe culminating in tail-recursive map). Briefly
   discuss the relation of `Incomplete` and $\parr$.
2. What can go very wrong: examples of programs that we _want_ to
   reject but are not obvious to reject
3. One big example: bf-traversal with difference-list based queues.
4. Type system
5. Dynamic semantics
6. Summary of typing evaluation contexts. Type safety (theorem
   statements, but no proof. Proofs are in Coq anyway, so… note: if we
   need manual proof in appendix, we can try using
   https://github.com/PierreSenellart/apxproof I've never used it.)

A parler à Paris le 18:

- Elimination du concept de Valid/Invalid dans le OTT/.tex

ctx_ValidOnly (*)
ctx_DestOnly (D*)
mode_IsValid (*)
ctx_Disjoint A B -> éliminer et remplacer A ⨄ B par A,B

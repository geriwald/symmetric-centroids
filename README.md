# symmetric-centroids

A Lean 4 and Mathlib proof that the surface centroid `S` and the volume centroid `B` of a solid both lie in the set of points fixed by its symmetries. When that set is a single point, `S = B`.

The proof is elementary and needs no machine check. It is formalised here for fun, and to try Lean and Mathlib on a small, real statement.

- `SymmetricCentroids.lean`: the definitions, the key lemma (an affine isometry that preserves a finite measure fixes its centroid), the theorem, its mirror corollary, and the trivial criterion for `S = B`.

## Build

```bash
lake exe cache get   # fetch Mathlib's prebuilt cache
lake build
```

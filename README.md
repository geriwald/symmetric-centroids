# symmetric-centroids

A Lean 4 and Mathlib proof that the surface centroid `S` and the volume centroid `B` of a solid both lie in the set of points fixed by its symmetries. When that set is a single point, `S = B`.

The proof is elementary and needs no machine check. It is formalised here for fun, and to try Lean and Mathlib on a small, real statement.

- `SymmetricCentroids.lean`: the definitions, the key lemma (an affine isometry that preserves a finite measure fixes its centroid), the theorem, its mirror corollary, and the trivial criterion for `S = B`.
- `SymmetricCentroids/SnubSolids.lean`: the two chiral snub solids, from their vertex coordinates. The snub cube turns onto itself by quarter turns about the `z` and `x` axes, the snub dodecahedron by half turns about the same axes; in each case the two rotations fix only the origin, so `S = B = 0`.
- `SymmetricCentroids/Tetrahedron.lean`: on a tetrahedron, the area-weighted mean of the face centroids equals the vertex centroid exactly when the four faces have the same area. The proof holds for any positive weights; affine independence of the vertices does the work.

## What is not proved, and what could follow

The statements below are worked out by hand or expected, not checked in Lean.

- **No symmetry condition is necessary.** The closed cone whose slant height is three times its base radius has `S = B`, yet its symmetries fix a whole axis: `S` sits at `(h/3)·s/(s + r)` and `B` at `h/4`. So does the square pyramid of base side `a` and height `√2·a`, whose lateral faces put `S` at `(2ℓh/3)/(2ℓ + a)`, `ℓ` being the slant height of a face. Checking either in Lean needs the area of a surface in space; this version of Mathlib normalises the Hausdorff measure, but has no area formula for a triangle or a cone in ℝ³ that we found.
- **The theorem is sharp, presumably.** For every group of isometries whose fixed set is more than a point, there should be a solid with exactly those symmetries and `S ≠ B`. The cone, the pyramid, the frustum and the hemisphere are examples for some of those groups, not a proof for all.
- **The meshes.** Every centre built from a mesh without favouring a direction (the mean of the vertices, of the triangles, `S`, `B`) is fixed by the symmetries that the mesh keeps, so all of them coincide when those symmetries fix a single point. The proof is the same; it is not written in Lean.
- **Any dimension.** Nothing in the proof uses dimension 3. In ℝⁿ, `S` is weighted by the `(n−1)`-dimensional measure of the boundary, and the statement should carry over as is.

### Tetrahedra: the converse holds

For a tetrahedron the converse is true. `B` is the mean of the four vertices, and the centroid of a face is `(4B − v)/3`, `v` being the opposite vertex. Hence `S = B` exactly when `B = Σ A_f v_f / Σ A_f`, the weights being the areas of the opposite faces. Barycentric coordinates are unique, so `S = B` exactly when the four faces have the same area. A tetrahedron with four faces of equal area is a disphenoid: its opposite edges are equal in pairs, and its three half turns about perpendicular axes fix only its centre. So on tetrahedra, `S = B` if and only if the symmetries fix a single point.

In Lean so far: the first step, `S = B` exactly when the four faces have the same area, for `S` written as the area-weighted mean of the face centroids (`Tetrahedron.lean`). Not yet in Lean: that this mean is the `surfCentroid` of the solid, and that equal face areas make a disphenoid.

### A conjecture, and a question

The same computation in ℝⁿ gives: for a simplex, `S = B` if and only if all its facets have the same `(n−1)`-dimensional volume.

- **Conjecture.** `S = B` does not require any symmetry. Among convex polyhedra with a given number of vertices, five or more, those with `S = B` form a set of codimension 3 (three real equations), and it contains polyhedra with no symmetry at all. Tetrahedra are the exception, since for them equal face areas force a symmetry.
- **Question.** In ℝ⁴ and beyond, does a simplex whose facets all have the same volume always have a symmetry group fixing a single point, as in ℝ³? If not, such a simplex has `S = B` without the symmetry, and the tetrahedron is a low-dimensional accident. We have not searched the literature on simplices with facets of equal volume.

## Build

```bash
lake exe cache get   # fetch Mathlib's prebuilt cache
lake build
```

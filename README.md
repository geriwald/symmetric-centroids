# symmetric-centroids

A Lean 4 and Mathlib proof that the surface centroid `S` and the volume centroid `B` of a solid in ℝⁿ both lie in the set of points fixed by its symmetries. When that set is a single point, `S = B`.

The proof is elementary and needs no machine check. It is formalised here for fun, and to try Lean and Mathlib on a small, real statement.

The note [*Symmetric centroids*](https://barycentre.scatteredstack.com/symmetric-centroids.pdf) states and proves everything below, including what is not in Lean. The explorer [Barycentre](https://barycentre.scatteredstack.com) computes `S`, `B` and the symmetries of many solids.

- `SymmetricCentroids.lean`: in ℝⁿ, `S` weighted by the `(n−1)`-dimensional Hausdorff measure of the boundary; the definitions, the key lemma (an affine isometry that preserves a finite measure fixes its centroid), the theorem, its mirror corollary, and the trivial criterion for `S = B`.
- `SymmetricCentroids/SnubSolids.lean`: the two chiral snub solids, from their vertex coordinates. The snub cube turns onto itself by quarter turns about the `z` and `x` axes, the snub dodecahedron by half turns about the same axes; in each case the two rotations fix only the origin, so `S = B = 0`.
- `SymmetricCentroids/Tetrahedron.lean`: on a tetrahedron, the area-weighted mean of the face centroids equals the vertex centroid exactly when the four faces have the same area, and a tetrahedron of nonzero volume with four faces of equal area has its opposite edges equal in pairs (a disphenoid), and conversely. Together: `S = B` exactly when the tetrahedron is a disphenoid.
- `SymmetricCentroids/SimplexCentroid.lean`, `TriangleCentroid.lean`: an affine map carries a centroid to a centroid; the centroid of a triangle in space under the area measure `μHE[2]` is the mean of its vertices, and its area is the norm of a cross product times a constant.
- `SymmetricCentroids/TetrahedronFrontier.lean`, `TetrahedronVolCentroid.lean`, `TetrahedronHausdorff.lean`, `TetrahedronTrueCentroids.lean`: the skin of a solid tetrahedron is the union of its four faces, which meet in sets of zero area; its volume centroid `B` is the mean of its vertices; its surface centroid `S` is the area-weighted mean of its face centroids; hence, with the true `S` and `B` of the solid, `S = B` exactly when the tetrahedron is a disphenoid (`surfCentroid_eq_volCentroid_iff_disphenoid`).
- `SymmetricCentroids/TetrahedronSymmetry.lean`: the converse of the main theorem for tetrahedra. A tetrahedron that is not flat has `S = B` exactly when its symmetries fix a single point (`surfCentroid_eq_volCentroid_iff_unique_fixed_point`): a disphenoid turns onto itself by the half turn about each bimedian, and two bimedians meet only at the centre.
- `SymmetricCentroids/MeshCentres.lean`: in any dimension, a symmetry of a triangle mesh fixes every weighted mean of its vertices or triangles whose weights it keeps, in particular the vertex mean `V`, the triangle mean `T` and the area-weighted mean `S`; so when the symmetries of the mesh fix a single point, `V = T = S` there.
- `SymmetricCentroids/Pyramid.lean`, `PyramidVolume.lean`, `PyramidSurface.lean`, `PyramidCentroid.lean`: **the converse of the main theorem fails** (`pyramid_counterexample`). The square pyramid with base vertices `(±1, 0, 0)`, `(0, ±1, 0)` and apex `(0, 0, 2)` has `S = B = (0, 0, 1/2)`, yet its symmetries fix both `B` and the apex, the only point of the pyramid at distance `3/2` from `B`.

## What is not proved in Lean

The note proves the statements below by hand.

- **The cone.** The closed cone whose slant height is three times its base radius has `S = B`, yet its symmetries fix a whole axis. So does the square pyramid of base side `a` and height `√2·a`, which `PyramidCentroid.lean` proves in Lean with base side `√2` and height `2`. The cone stays outside Lean, because we found no area formula for curved surfaces in this version of Mathlib.
- **Solids circumscribing a sphere** (Proposition 7, Corollary 8). If every tangent plane of the skin touches a sphere of centre `I`, then `B − I = ¾(S − I)`, so `S = B` exactly when `I = B`. A right cone, or a right pyramid on a regular base, has `S = B` exactly when its lateral area is three times its base area.
- **Section 6, Propositions 11 to 15.** For every `N ≥ 5` there is a convex polyhedron with `N` vertices, `S = B` and no symmetry other than the identity, a pyramid (11). Turning a piece with a rotation axis keeps `S` and `B` (12), so the gyrate rhombicosidodecahedra J72 to J75 have `S = B` (13). `S − B` is a multiple of the covariance, over the skin, between the position and the distance from `B` to the tangent plane (14). The theorem is sharp: for each group of isometries that fixes more than one point, except the rotations about an axis alone, which are the group of no solid, a convex solid has exactly that group and `S ≠ B` (15).
- **The meshes, for `B`.** `MeshCentres.lean` covers the vertex mean, the triangle mean and the area-weighted mean of a mesh. The volume centroid of a mesh, from signed tetrahedra, is a weighted mean too, but its weights depend on the orientation and on a reference point, and it is not written in Lean.

### Tetrahedra: the converse holds

`B` is the mean of the four vertices, and the centroid of a face is `(4B − v)/3`, `v` being the opposite vertex. Hence `S = B` exactly when `B = Σ A_f v_f / Σ A_f`, the weights being the areas of the opposite faces, and since barycentric coordinates are unique, exactly when the four faces have the same area. In Lean (`Tetrahedron.lean`), equal face areas make a disphenoid through the face normals: they have the same length and sum to zero, so `nₐ·n_b = n_c·n_d`, the cross product of two normals is their common edge times the triple product, and Lagrange's identity then makes opposite edges equal. Conversely, a disphenoid has four congruent faces. The weighted mean is the true `surfCentroid` of the solid and the vertex mean its true `volCentroid` (`TetrahedronTrueCentroids.lean`), and a disphenoid turns onto itself by the half turn about each bimedian, two of which fix only its centre. So a tetrahedron has `S = B` exactly when it is a disphenoid (`centroid_eq_iff_disphenoid`), that is, when its symmetries fix a single point (`TetrahedronSymmetry.lean`).

### A conjecture, and a question, with numerical evidence

- **Conjecture.** Among convex polyhedra with a given number of vertices, those with `S = B` form a set of codimension 3, one for each of the three real equations `S = B`. The note proves it among pyramids with a plane base near the regular ones (Proposition 11), and for four vertices the set is that of the disphenoids. It is a statement about dimension only: the derivative of `S − B` may drop rank on the set, since the bipyramid over a regular `n`-gon whose apices stand at the height of its inradius has `S = B` and a derivative of rank 2.
  *Evidence:* `numerics/s_equals_b_without_symmetry.py` starts from the square pyramid of height `√2·a`, moves the four base vertices at random in space, and solves `S = B` for the apex. With its default arguments it keeps 8 of 20 trials, each a convex polyhedron with five vertices, no symmetry (the only distance-preserving permutation of the vertices is the identity) and `|S − B|` below `1e-16`. At each of these eight points the derivative of `S − B` in the apex has rank 3, its smallest singular value being above `0.02`, so near each of them the set where `S = B` is a submanifold of codimension 3. This is numerical evidence, not a proof.
- **Question, answered numerically.** In ℝⁿ, a simplex has `S = B` exactly when all its facets have the same `(n−1)`-dimensional volume (Krantz, McCarthy and Parks, J. Math. Anal. Appl. 316, 2006, Theorem 34; Edmonds, Hajja and Martini, arXiv:math/0411093, Theorem 3.2 (iii)). In ℝ⁴, does such a simplex always have a symmetry fixing a single point, as in ℝ³? No, numerically: `numerics/equiareal_simplex_without_symmetry.py` moves one vertex of a random 4-simplex to make the five facet volumes equal, and in 8 of 20 trials the result has no symmetry, with facet volumes equal to `1e-15` and `|S − B|` below `1e-15`. So the tetrahedron is a low-dimensional accident. We found no paper that exhibits an equiareal simplex shown to have no symmetry at all.

## Numerics

The two scripts in `numerics/` need Python 3 with NumPy and SciPy: `python3 numerics/s_equals_b_without_symmetry.py [trials] [seed]`. The defaults (20 trials, seed 2026) give the counts above.

## Build

```bash
lake exe cache get   # fetch Mathlib's prebuilt cache
lake build
```

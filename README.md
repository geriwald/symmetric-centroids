# symmetric-centroids

A Lean 4 and Mathlib proof that the surface centroid `S` and the volume centroid `B` of a solid in ℝⁿ both lie in the set of points fixed by its symmetries. When that set is a single point, `S = B`.

The proof is elementary and needs no machine check. It is formalised here for fun, and to try Lean and Mathlib on a small, real statement.

- `SymmetricCentroids.lean`: in ℝⁿ, `S` weighted by the `(n−1)`-dimensional Hausdorff measure of the boundary; the definitions, the key lemma (an affine isometry that preserves a finite measure fixes its centroid), the theorem, its mirror corollary, and the trivial criterion for `S = B`.
- `SymmetricCentroids/SnubSolids.lean`: the two chiral snub solids, from their vertex coordinates. The snub cube turns onto itself by quarter turns about the `z` and `x` axes, the snub dodecahedron by half turns about the same axes; in each case the two rotations fix only the origin, so `S = B = 0`.
- `SymmetricCentroids/Tetrahedron.lean`: on a tetrahedron, the area-weighted mean of the face centroids equals the vertex centroid exactly when the four faces have the same area, and a tetrahedron of nonzero volume with four faces of equal area has its opposite edges equal in pairs (a disphenoid), and conversely. Together: `S = B` exactly when the tetrahedron is a disphenoid.
- `SymmetricCentroids/SimplexCentroid.lean`, `TriangleCentroid.lean`: an affine map carries a centroid to a centroid; the centroid of a triangle in space under the area measure `μHE[2]` is the mean of its vertices, and its area is the norm of a cross product times a constant.
- `SymmetricCentroids/TetrahedronFrontier.lean`, `TetrahedronVolCentroid.lean`, `TetrahedronHausdorff.lean`, `TetrahedronTrueCentroids.lean`: the skin of a solid tetrahedron is the union of its four faces, which meet in sets of zero area; its volume centroid `B` is the mean of its vertices; its surface centroid `S` is the area-weighted mean of its face centroids; hence, with the true `S` and `B` of the solid, `S = B` exactly when the tetrahedron is a disphenoid (`surfCentroid_eq_volCentroid_iff_disphenoid`).
- `SymmetricCentroids/TetrahedronSymmetry.lean`: the converse of the main theorem for tetrahedra. A tetrahedron that is not flat has `S = B` exactly when its symmetries fix a single point (`surfCentroid_eq_volCentroid_iff_unique_fixed_point`): a disphenoid turns onto itself by the half turn about each bimedian, and two bimedians meet only at the centre.
- `SymmetricCentroids/MeshCentres.lean`: in any dimension, a symmetry of a triangle mesh fixes every weighted mean of its vertices or triangles whose weights it keeps, in particular the vertex mean `V`, the triangle mean `T` and the area-weighted mean `S`; so when the symmetries of the mesh fix a single point, `V = T = S` there.
- `SymmetricCentroids/Pyramid.lean`, `PyramidVolume.lean`, `PyramidSurface.lean`, `PyramidCentroid.lean`: **the converse of the main theorem fails** (`pyramid_counterexample`). The square pyramid with base vertices `(±1, 0, 0)`, `(0, ±1, 0)` and apex `(0, 0, 2)` has `S = B = (0, 0, 1/2)`, yet its symmetries fix both `B` and the apex, the only point of the pyramid at distance `3/2` from `B`.

## What is not proved, and what could follow

The statements below are worked out by hand or expected, not checked in Lean.

- **No symmetry condition is necessary, now in Lean for the pyramid.** The closed cone whose slant height is three times its base radius has `S = B`, yet its symmetries fix a whole axis. So does the square pyramid of base side `a` and height `√2·a`, which `PyramidCentroid.lean` proves in Lean with base side `√2` and height `2`. The cone itself stays outside Lean: its lateral surface is curved, and this version of Mathlib has no area formula for curved surfaces that we found.
- **The theorem is sharp, presumably.** For every group of isometries whose fixed set is more than a point, there should be a solid with exactly those symmetries and `S ≠ B`. The cone, the pyramid, the frustum and the hemisphere are examples for some of those groups, not a proof for all.
- **The meshes, for `B`.** `MeshCentres.lean` covers the vertex mean, the triangle mean and the area-weighted mean of a mesh. The volume centroid of a mesh, from signed tetrahedra, is a weighted mean too, but its weights depend on the orientation and on a reference point; it is not written in Lean.

### Tetrahedra: the converse holds

For a tetrahedron the converse is true. `B` is the mean of the four vertices, and the centroid of a face is `(4B − v)/3`, `v` being the opposite vertex. Hence `S = B` exactly when `B = Σ A_f v_f / Σ A_f`, the weights being the areas of the opposite faces. Barycentric coordinates are unique, so `S = B` exactly when the four faces have the same area. A tetrahedron with four faces of equal area is a disphenoid: its opposite edges are equal in pairs, and its three half turns about perpendicular axes fix only its centre. So on tetrahedra, `S = B` if and only if the symmetries fix a single point.

In Lean (`Tetrahedron.lean`), for `S` written as the area-weighted mean of the face centroids: `S = B` exactly when the four faces have the same area, and equal face areas make a disphenoid. The second step uses the face normals: they have the same length and sum to zero, so `nₐ·n_b = n_c·n_d`; the cross product of two normals is their common edge times the triple product, and Lagrange's identity then makes opposite edges equal. Conversely, a disphenoid has four faces of equal area: each face has the same three side lengths, and Heron's formula follows from Lagrange's identity. So `S = B` exactly when the tetrahedron is a disphenoid (`centroid_eq_iff_disphenoid`). The weighted mean is the true `surfCentroid` of the solid, and the vertex mean its true `volCentroid` (`TetrahedronTrueCentroids.lean`), so the equivalence holds for the solid itself. A disphenoid turns onto itself by the half turn about each bimedian, and two of them fix only its centre, so on tetrahedra `S = B` exactly when the symmetries fix a single point (`TetrahedronSymmetry.lean`).

### A conjecture, and a question, with numerical evidence

The same computation in ℝⁿ gives: for a simplex, `S = B` if and only if all its facets have the same `(n−1)`-dimensional volume. This is known: the incenter and the centroid of a simplex coincide exactly when it is equiareal (Edmonds, Hajja and Martini, *Coincidences of simplex centers and related facial structures*, arXiv:math/0411093, 2004, Theorem 3.2 (iii)). The tetrahedron case is classical; McMullen studied simplices with facets of equal volume (*Simplices with equiareal faces*, Discrete Comput. Geom. 24, 2000).

- **Conjecture.** `S = B` does not require any symmetry. Among convex polyhedra with a given number of vertices, five or more, those with `S = B` form a set of codimension 3 (three real equations), and it contains polyhedra with no symmetry at all. Tetrahedra are the exception, since for them equal face areas force a symmetry.
  *Evidence:* `numerics/s_equals_b_without_symmetry.py` starts from the square pyramid of height `√2·a`, moves the four base vertices at random and solves `S = B` for the apex. In 8 of 20 trials it finds a convex polyhedron with five vertices, no symmetry (the only distance-preserving permutation of the vertices is the identity) and `|S − B|` below `1e-16`. The Jacobian of `S − B` in the apex has rank 3 at those points, so by the implicit function theorem the set where `S = B` is, near each of them, a submanifold of codimension 3. This is numerical evidence, not a proof.
- **Question, answered numerically.** In ℝ⁴, does a simplex whose facets all have the same volume always have a symmetry fixing a single point, as in ℝ³? No, numerically: `numerics/equiareal_simplex_without_symmetry.py` moves one vertex of a random 4-simplex to make the five facet volumes equal, and in 8 of 20 trials the result has no symmetry, with facet volumes equal to `1e-15` and `|S − B|` below `1e-15`. So a 4-simplex can have `S = B` without any symmetry, and the tetrahedron is a low-dimensional accident. Edmonds, Hajja and Martini already give an equiareal 4-simplex whose centroid, circumcenter and Fermat–Torricelli point are pairwise distinct (Theorem 4.3), so that its facets are not all congruent; we did not find in the literature an equiareal simplex shown to have no symmetry at all.

## Numerics

The two scripts in `numerics/` need Python 3 with NumPy and SciPy: `python3 numerics/s_equals_b_without_symmetry.py [trials] [seed]`.

## Build

```bash
lake exe cache get   # fetch Mathlib's prebuilt cache
lake build
```

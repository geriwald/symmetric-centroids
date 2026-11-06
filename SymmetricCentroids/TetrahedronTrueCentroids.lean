/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.TetrahedronHausdorff

/-!
# Tetrahedra, with the true `S` and `B`

`Tetrahedron.lean` proves that a tetrahedron is a disphenoid exactly when the area-weighted mean
of its face centroids equals the mean of its vertices. Here the two sides are the true centroids
of the solid: `surfCentroid`, under the area measure `μHE[2]` on its frontier, and `volCentroid`,
under the volume.

The area `μHE[2]` of each face is its `faceArea` times a constant common to the four faces, and a
weighted mean does not move when every weight is scaled by the same constant.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace SymmetricCentroids.Tetrahedron

variable {v : Fin 4 → E}

/-- Scaling every weight by the same nonzero constant does not move the weighted centroid. -/
lemma weightedCentroid_const_mul (v : Fin 4 → E) (A : Fin 4 → ℝ) {k : ℝ} (hk : k ≠ 0) :
    weightedCentroid v (fun i => k * A i) = weightedCentroid v A := by
  simp only [weightedCentroid, ← Finset.mul_sum, mul_inv, mul_smul, ← Finset.smul_sum]
  rw [smul_comm _ k, inv_smul_smul₀ hk]

/-- The area `μHE[2]` of a face is `faceArea` times twice the area of the standard triangle. -/
lemma hausdorff_face (hv : AffineIndependent ℝ v) (i : Fin 4) :
    ((μHE[2] : Measure E) (face v i)).toReal =
      (2 * (volume stdTriangle).toReal) * faceArea v i := by
  rw [face_eq_triangle, hausdorff_triangle_cross (face_edges_linearIndependent hv i),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), faceArea]
  ring

/-- **On a tetrahedron, `S = B` exactly when it is a disphenoid**, `S` and `B` being the true
centroids of the solid: of its frontier under the area measure `μHE[2]`, and of its volume. -/
theorem surfCentroid_eq_volCentroid_iff_disphenoid (hv : AffineIndependent ℝ v)
    (hA : ∀ i, 0 < faceArea v i) (hvol : tripleProduct v ≠ 0) :
    surfCentroid (solid v) = volCentroid (solid v) ↔
      dist (v 0) (v 1) = dist (v 2) (v 3) ∧ dist (v 0) (v 2) = dist (v 1) (v 3) ∧
        dist (v 0) (v 3) = dist (v 1) (v 2) := by
  have hK : 0 < (volume stdTriangle).toReal :=
    ENNReal.toReal_pos volume_stdTriangle_ne_zero isCompact_stdTriangle.measure_lt_top.ne
  have hS : surfCentroid (solid v) = weightedCentroid v (faceArea v) := by
    rw [surfCentroid_solid hv]
    change weightedCentroid v (fun i => ((μHE[2] : Measure E) (face v i)).toReal) = _
    simp only [hausdorff_face hv]
    exact weightedCentroid_const_mul v (faceArea v) (by positivity)
  have hB : volCentroid (solid v) = vertexCentroid v := by
    rw [volCentroid_solid hv, vertexCentroid]; norm_num
  rw [hS, hB]
  exact centroid_eq_iff_disphenoid v hv hA hvol

end SymmetricCentroids.Tetrahedron

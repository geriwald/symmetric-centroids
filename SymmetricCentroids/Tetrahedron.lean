/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids

/-!
# Tetrahedra: `S = B` exactly when the four faces have the same area

On a tetrahedron, the surface centroid is the mean of the four face centroids weighted by the
face areas, and the vertex centroid is the mean of the four vertices. They coincide exactly when
the four faces have the same area. The face opposite the vertex `vᵢ` has its centroid at
`(4B - vᵢ)/3`, so `S = B` exactly when `B` is the mean of the vertices weighted by the areas of
the opposite faces. The vertices are affinely independent, so the weights must all be equal.

The proof uses nothing about areas: it holds for any positive weights.

Not proved here: that this weighted mean is the `surfCentroid` of the solid tetrahedron, its
centroid under the area measure `μHE[2]`, and that the vertex centroid is its `volCentroid`.
Both are true, but they need the area and the centroid of a triangle under `μHE[2]`.
-/

open Finset Matrix

@[expose] public noncomputable section

namespace SymmetricCentroids.Tetrahedron

variable (v : Fin 4 → E)

/-- The vertex centroid, the mean of the four vertices. -/
def vertexCentroid : E := (4 : ℝ)⁻¹ • ∑ i, v i

/-- The centroid of the face opposite the vertex `i`, the mean of the other three. -/
def faceCentroid (i : Fin 4) : E := (3 : ℝ)⁻¹ • (∑ j, v j - v i)

/-- The mean of the face centroids, weighted by `A`. -/
def weightedCentroid (A : Fin 4 → ℝ) : E := (∑ i, A i)⁻¹ • ∑ i, A i • faceCentroid v i

/-- The area of the face opposite the vertex `i`: half the norm of a cross product of two of
its edges. -/
def faceArea (i : Fin 4) : ℝ :=
  let p := fun k : Fin 3 => v (i.succAbove k)
  ‖(WithLp.toLp 2 ((p 1 - p 0).ofLp ⨯₃ (p 2 - p 0).ofLp) : E)‖ / 2

/-- With positive weights on affinely independent vertices, the weighted mean of the face
centroids is the vertex centroid exactly when the weights are all equal. -/
theorem weightedCentroid_eq_iff (hv : AffineIndependent ℝ v) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) :
    weightedCentroid v A = vertexCentroid v ↔ ∀ i j, A i = A j := by
  set T := ∑ i, A i with hT
  have hT0 : T ≠ 0 := (Finset.sum_pos (fun i _ => hA i) Finset.univ_nonempty).ne'
  set P := ∑ i, v i with hP
  set Q := ∑ i, A i • v i with hQ
  -- The face opposite `vᵢ` has its centroid at `(P - vᵢ)/3`.
  have hsum : ∑ i, A i • faceCentroid v i = (3 : ℝ)⁻¹ • (T • P - Q) := by
    have h1 : ∀ i, A i • faceCentroid v i = (3 : ℝ)⁻¹ • (A i • P) - (3 : ℝ)⁻¹ • (A i • v i) := by
      intro i; simp only [faceCentroid, ← hP]; module
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, ← Finset.smul_sum,
      ← Finset.smul_sum, ← Finset.sum_smul, ← hT, ← hQ, smul_sub]
  have hS : weightedCentroid v A = T⁻¹ • (3 : ℝ)⁻¹ • (T • P - Q) := by
    simp only [weightedCentroid, ← hT, hsum]
  have hB : vertexCentroid v = (4 : ℝ)⁻¹ • P := rfl
  rw [hS, hB]
  constructor
  · intro h
    -- `S = B` turns into `∑ (Aᵢ - T/4) vᵢ = 0`, with weights summing to zero.
    rw [inv_smul_eq_iff₀ hT0, inv_smul_eq_iff₀ (by norm_num : (3 : ℝ) ≠ 0)] at h
    have hQP : Q = (T / 4) • P := by linear_combination (norm := module) -h
    have key : ∑ i, (A i - T / 4) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ← hQ, ← hP, hQP, sub_self]
    have hw : ∑ i, (A i - T / 4) = 0 := by
      rw [Finset.sum_sub_distrib, ← hT]; simp; ring
    have hzero := (affineIndependent_iff_of_fintype ℝ v).1 hv (fun i => A i - T / 4) hw (by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
        Finset.weightedVSubOfPoint_apply]
      simpa using key)
    intro i j
    have hi : A i - T / 4 = 0 := hzero i
    have hj : A j - T / 4 = 0 := hzero j
    linarith
  · intro h
    have hA0 : ∀ i, A i = A 0 := fun i => h i 0
    have hT4 : T = 4 * A 0 := by
      rw [hT, Fin.sum_univ_four, hA0 1, hA0 2, hA0 3]; ring
    have hQ0 : Q = A 0 • P := by
      rw [hQ, hP, Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hA0 i]
    have hA00 : A 0 ≠ 0 := (hA 0).ne'
    rw [hQ0, hT4, ← sub_smul, smul_smul, smul_smul]
    congr 1
    field_simp
    ring

/-- On a tetrahedron whose four faces have positive area, the area-weighted mean of the face
centroids is the vertex centroid exactly when the four faces have the same area. -/
theorem surfaceCentroid_eq_iff (hv : AffineIndependent ℝ v) (hA : ∀ i, 0 < faceArea v i) :
    weightedCentroid v (faceArea v) = vertexCentroid v ↔
      ∀ i j, faceArea v i = faceArea v j :=
  weightedCentroid_eq_iff v hv _ hA

end SymmetricCentroids.Tetrahedron

/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.Tetrahedron
public import SymmetricCentroids.TetrahedronFrontier
public import SymmetricCentroids.TetrahedronVolCentroid
public import SymmetricCentroids.TriangleCentroid

/-!
# The true `S` of a tetrahedron

* `face_eq_triangle`, `face_edges_linearIndependent`: the face opposite `vᵢ` is the triangle on
  the vertices `v (i.succAbove k)`, `k = 0, 1, 2`, in the order of `faceArea`, and its two edges
  from the first vertex are linearly independent.
* `surfCentroid_solid`: the surface centroid of the solid tetrahedron, its centroid under `μHE[2]`
  on the frontier, is the mean of the four face centroids weighted by the face areas. The
  frontier is the union of the faces, which meet in sets of zero area, so the measure splits into
  the four faces, and each face has its centroid at the mean of its vertices.
-/

open MeasureTheory Set

@[expose] public noncomputable section

namespace SymmetricCentroids.Tetrahedron

variable {v : Fin 4 → E}

/-- The face opposite `vᵢ` is the triangle on the three other vertices, in the order of
`faceArea`. -/
lemma face_eq_triangle (i : Fin 4) :
    face v i = convexHull ℝ {v (i.succAbove 0), v (i.succAbove 1), v (i.succAbove 2)} := by
  rw [face, show {j | j ≠ i} = range i.succAbove from (Fin.range_succAbove i).symm,
    ← range_comp]
  congr 1
  ext x
  simp only [mem_range, Function.comp_apply, mem_insert_iff, mem_singleton_iff,
    Fin.exists_fin_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.exists_iff,
    or_false]
  simp only [eq_comm]

/-- The two edges of a face from its first vertex are linearly independent. -/
lemma face_edges_linearIndependent (hv : AffineIndependent ℝ v) (i : Fin 4) :
    LinearIndependent ℝ ![v (i.succAbove 1) - v (i.succAbove 0),
      v (i.succAbove 2) - v (i.succAbove 0)] := by
  set b := affineBasis hv
  have e : ∀ a c : Fin 3,
      b.coord (i.succAbove a) (v (i.succAbove c)) = if a = c then 1 else 0 := by
    intro a c
    split_ifs with h
    · subst h; exact b.coord_apply_eq _
    · exact b.coord_apply_ne (Fin.succAbove_right_injective.ne h)
  have key : ∀ (k : Fin 4) (s t : ℝ),
      (b.coord k).linear (s • (v (i.succAbove 1) - v (i.succAbove 0)) +
        t • (v (i.succAbove 2) - v (i.succAbove 0))) =
      s * (b.coord k (v (i.succAbove 1)) - b.coord k (v (i.succAbove 0))) +
        t * (b.coord k (v (i.succAbove 2)) - b.coord k (v (i.succAbove 0))) := by
    intro k s t
    simp only [map_add, map_smul, smul_eq_mul, ← vsub_eq_sub, AffineMap.linear_apply_vsub]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have k1 := key (i.succAbove 1) s t
  have k2 := key (i.succAbove 2) s t
  rw [hst, map_zero] at k1 k2
  simp only [e] at k1 k2
  norm_num at k1 k2
  exact ⟨k1.symm, k2.symm⟩

lemma isCompact_face (i : Fin 4) : IsCompact (face v i) :=
  (toFinite _).isCompact_convexHull (𝕜 := ℝ)

/-- Each face has finite area. -/
lemma hausdorff_face_ne_top (hv : AffineIndependent ℝ v) (i : Fin 4) :
    (μHE[2] : Measure E) (face v i) ≠ ⊤ := by
  rw [face_eq_triangle, hausdorff_triangle (face_edges_linearIndependent hv i)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top isCompact_stdTriangle.measure_lt_top.ne

/-- The first moment of a finite measure is its mass times its centroid. -/
lemma integral_eq_smul_centroid (ν : Measure E) [IsFiniteMeasure ν] :
    ∫ x, x ∂ν = (ν univ).toReal • centroid ν := by
  by_cases hν : ν = 0
  · simp [hν]
  · have hM : (ν univ).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨Measure.measure_univ_ne_zero.2 hν, measure_ne_top ν _⟩
    rw [centroid, smul_smul, mul_inv_cancel₀ hM, one_smul]

/-- The first moment of a face is its area times its centroid, the mean of its vertices. -/
lemma integral_face (hv : AffineIndependent ℝ v) (i : Fin 4) :
    ∫ x in face v i, x ∂(μHE[2] : Measure E) =
      ((μHE[2] : Measure E) (face v i)).toReal • faceCentroid v i := by
  have : IsFiniteMeasure ((μHE[2] : Measure E).restrict (face v i)) :=
    isFiniteMeasure_restrict.2 (hausdorff_face_ne_top hv i)
  rw [integral_eq_smul_centroid, Measure.restrict_apply_univ]
  congr 1
  rw [face_eq_triangle, centroid_triangle (face_edges_linearIndependent hv i), faceCentroid,
    Fin.sum_univ_succAbove _ i, Fin.sum_univ_three]
  congr 1
  abel

/-- **The surface centroid of a tetrahedron** is the mean of the face centroids weighted by the
face areas, the areas being taken under `μHE[2]`. -/
theorem surfCentroid_solid (hv : AffineIndependent ℝ v) :
    surfCentroid (solid v) =
      (∑ i, ((μHE[2] : Measure E) (face v i)).toReal)⁻¹ •
        ∑ i, ((μHE[2] : Measure E) (face v i)).toReal • faceCentroid v i := by
  have hsplit : (μHE[2] : Measure E).restrict (frontier (solid v)) =
      ∑ i, (μHE[2] : Measure E).restrict (face v i) := by
    rw [frontier_eq_iUnion_face hv, Measure.restrict_iUnion_ae
      (fun i j hij => hausdorff_face_inter_face hv hij)
      (fun i => (isCompact_face i).isClosed.measurableSet.nullMeasurableSet),
      Measure.sum_fintype]
  change centroid ((μHE[2] : Measure E).restrict (frontier (solid v))) = _
  rw [centroid, hsplit, integral_finsetSum_measure fun i _ =>
      integrable_id_restrict (isCompact_face i) (hausdorff_face_ne_top hv i),
    Measure.finsetSum_apply, ENNReal.toReal_sum fun i _ => by
      rw [Measure.restrict_apply_univ]; exact hausdorff_face_ne_top hv i]
  simp only [Measure.restrict_apply_univ, integral_face hv]

end SymmetricCentroids.Tetrahedron

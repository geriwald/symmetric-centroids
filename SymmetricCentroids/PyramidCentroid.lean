/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.PyramidSurface

/-!
# The surface centroid of the square pyramid, and the counterexample

Each lateral face has cross product of norm 3 and centroid at height `2/3`; each half of the base
has cross product of norm 2 and centroid in the plane `z = 0`, the two halves mirror images. With
the area measure split over the six faces, `S = (0, 0, 1/2) = B`, while the symmetries of the
pyramid fix both `B` and the apex: `S = B` does not need the symmetries to fix a single point.
-/

open MeasureTheory Matrix

@[expose] public noncomputable section

namespace SymmetricCentroids.Pyramid

open Tetrahedron

lemma norm_toLp_eq {w : Fin 3 → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : w ⬝ᵥ w = r ^ 2) :
    ‖(WithLp.toLp 2 w : E)‖ = r := by
  rw [← sq_eq_sq₀ (norm_nonneg _) hr, norm_sq_toLp, h]

/-- The area of the standard triangle, the unit of the face weights. -/
abbrev K : ℝ := (volume stdTriangle).toReal


lemma li_lat0 : LinearIndependent ℝ ![b1 - b0, apex - b0] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e0 := congrArg (· 0) h
  have e1 := congrArg (· 1) h
  have e2 := congrArg (· 2) h
  simp [apex, b0, b1] at e0 e1 e2
  constructor <;> linarith

lemma cross_lat0 :
    ‖(WithLp.toLp 2 ((b1 - b0).ofLp ⨯₃ (apex - b0).ofLp) : E)‖ = 3 := by
  refine norm_toLp_eq (by norm_num) ?_
  simp [apex, b0, b1, cross_apply, dotProduct, Fin.sum_univ_three]
  norm_num

lemma area_lat0 : ((μHE[2] : Measure E) lat0).toReal = K * 3 := by
  rw [lat0, hausdorff_triangle_cross li_lat0, cross_lat0, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma centroid_lat0 :
    centroid ((μHE[2] : Measure E).restrict lat0) = pt3 (1 / 3) (1 / 3) (2 / 3) := by
  rw [lat0, centroid_triangle li_lat0]
  ext i; fin_cases i <;> simp [apex, b0, b1]; norm_num

lemma li_lat1 : LinearIndependent ℝ ![b2 - b1, apex - b1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e0 := congrArg (· 0) h
  have e1 := congrArg (· 1) h
  have e2 := congrArg (· 2) h
  simp [apex, b1, b2] at e0 e1 e2
  constructor <;> linarith

lemma cross_lat1 :
    ‖(WithLp.toLp 2 ((b2 - b1).ofLp ⨯₃ (apex - b1).ofLp) : E)‖ = 3 := by
  refine norm_toLp_eq (by norm_num) ?_
  simp [apex, b1, b2, cross_apply, dotProduct, Fin.sum_univ_three]
  norm_num

lemma area_lat1 : ((μHE[2] : Measure E) lat1).toReal = K * 3 := by
  rw [lat1, hausdorff_triangle_cross li_lat1, cross_lat1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma centroid_lat1 :
    centroid ((μHE[2] : Measure E).restrict lat1) = pt3 (-1 / 3) (1 / 3) (2 / 3) := by
  rw [lat1, centroid_triangle li_lat1]
  ext i; fin_cases i <;> simp [apex, b1, b2] <;> norm_num

lemma li_lat2 : LinearIndependent ℝ ![b3 - b2, apex - b2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e0 := congrArg (· 0) h
  have e1 := congrArg (· 1) h
  have e2 := congrArg (· 2) h
  simp [apex, b2, b3] at e0 e1 e2
  constructor <;> linarith

lemma cross_lat2 :
    ‖(WithLp.toLp 2 ((b3 - b2).ofLp ⨯₃ (apex - b2).ofLp) : E)‖ = 3 := by
  refine norm_toLp_eq (by norm_num) ?_
  simp [apex, b2, b3, cross_apply, dotProduct, Fin.sum_univ_three]
  norm_num

lemma area_lat2 : ((μHE[2] : Measure E) lat2).toReal = K * 3 := by
  rw [lat2, hausdorff_triangle_cross li_lat2, cross_lat2, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma centroid_lat2 :
    centroid ((μHE[2] : Measure E).restrict lat2) = pt3 (-1 / 3) (-1 / 3) (2 / 3) := by
  rw [lat2, centroid_triangle li_lat2]
  ext i; fin_cases i <;> simp [apex, b2, b3] <;> norm_num

lemma li_lat3 : LinearIndependent ℝ ![b0 - b3, apex - b3] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e0 := congrArg (· 0) h
  have e1 := congrArg (· 1) h
  have e2 := congrArg (· 2) h
  simp [apex, b0, b3] at e0 e1 e2
  constructor <;> linarith

lemma cross_lat3 :
    ‖(WithLp.toLp 2 ((b0 - b3).ofLp ⨯₃ (apex - b3).ofLp) : E)‖ = 3 := by
  refine norm_toLp_eq (by norm_num) ?_
  simp [apex, b0, b3, cross_apply, dotProduct, Fin.sum_univ_three]
  norm_num

lemma area_lat3 : ((μHE[2] : Measure E) lat3).toReal = K * 3 := by
  rw [lat3, hausdorff_triangle_cross li_lat3, cross_lat3, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma centroid_lat3 :
    centroid ((μHE[2] : Measure E).restrict lat3) = pt3 (1 / 3) (-1 / 3) (2 / 3) := by
  rw [lat3, centroid_triangle li_lat3]
  ext i; fin_cases i <;> simp [apex, b0, b3] <;> norm_num

lemma li_baseA : LinearIndependent ℝ ![b1 - b0, b2 - b0] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e0 := congrArg (· 0) h
  have e1 := congrArg (· 1) h
  have e2 := congrArg (· 2) h
  simp [b0, b1, b2] at e0 e1 e2
  constructor <;> linarith

lemma cross_baseA :
    ‖(WithLp.toLp 2 ((b1 - b0).ofLp ⨯₃ (b2 - b0).ofLp) : E)‖ = 2 := by
  refine norm_toLp_eq (by norm_num) ?_
  simp [b0, b1, b2, cross_apply, dotProduct, Fin.sum_univ_three]
  norm_num

lemma area_baseA : ((μHE[2] : Measure E) baseA).toReal = K * 2 := by
  rw [baseA, hausdorff_triangle_cross li_baseA, cross_baseA, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma centroid_baseA : centroid ((μHE[2] : Measure E).restrict baseA) = pt3 0 (1 / 3) 0 := by
  rw [baseA, centroid_triangle li_baseA]
  ext i; fin_cases i <;> simp [b0, b1, b2]

lemma li_baseB : LinearIndependent ℝ ![b2 - b0, b3 - b0] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e0 := congrArg (· 0) h
  have e1 := congrArg (· 1) h
  have e2 := congrArg (· 2) h
  simp [b0, b2, b3] at e0 e1 e2
  constructor <;> linarith

lemma cross_baseB :
    ‖(WithLp.toLp 2 ((b2 - b0).ofLp ⨯₃ (b3 - b0).ofLp) : E)‖ = 2 := by
  refine norm_toLp_eq (by norm_num) ?_
  simp [b0, b2, b3, cross_apply, dotProduct, Fin.sum_univ_three]
  norm_num

lemma area_baseB : ((μHE[2] : Measure E) baseB).toReal = K * 2 := by
  rw [baseB, hausdorff_triangle_cross li_baseB, cross_baseB, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]
  ring

lemma centroid_baseB : centroid ((μHE[2] : Measure E).restrict baseB) = pt3 0 (-1 / 3) 0 := by
  rw [baseB, centroid_triangle li_baseB]
  ext i; fin_cases i <;> simp [b0, b2, b3]; norm_num

/-! ### `S` of the pyramid -/

lemma K_pos : 0 < K :=
  ENNReal.toReal_pos volume_stdTriangle_ne_zero isCompact_stdTriangle.measure_lt_top.ne

lemma isCompact_face6 (i : Fin 6) : IsCompact (face6 i) := by
  fin_cases i <;> exact (Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)

lemma face6_ne_top (i : Fin 6) : (μHE[2] : Measure E) (face6 i) ≠ ⊤ := by
  have hK := (isCompact_stdTriangle.measure_lt_top (μ := volume)).ne
  fin_cases i
  · change (μHE[2] : Measure E) lat0 ≠ ⊤
    rw [lat0, hausdorff_triangle_cross li_lat0]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  · change (μHE[2] : Measure E) lat1 ≠ ⊤
    rw [lat1, hausdorff_triangle_cross li_lat1]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  · change (μHE[2] : Measure E) lat2 ≠ ⊤
    rw [lat2, hausdorff_triangle_cross li_lat2]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  · change (μHE[2] : Measure E) lat3 ≠ ⊤
    rw [lat3, hausdorff_triangle_cross li_lat3]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  · change (μHE[2] : Measure E) baseA ≠ ⊤
    rw [baseA, hausdorff_triangle_cross li_baseA]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  · change (μHE[2] : Measure E) baseB ≠ ⊤
    rw [baseB, hausdorff_triangle_cross li_baseB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK

lemma area_face6 (i : Fin 6) :
    ((μHE[2] : Measure E) (face6 i)).toReal = K * ![3, 3, 3, 3, 2, 2] i := by
  fin_cases i
  exacts [area_lat0, area_lat1, area_lat2, area_lat3, area_baseA, area_baseB]

lemma centroid_face6 (i : Fin 6) :
    centroid ((μHE[2] : Measure E).restrict (face6 i)) =
      ![pt3 (1 / 3) (1 / 3) (2 / 3), pt3 (-1 / 3) (1 / 3) (2 / 3), pt3 (-1 / 3) (-1 / 3) (2 / 3),
        pt3 (1 / 3) (-1 / 3) (2 / 3), pt3 0 (1 / 3) 0, pt3 0 (-1 / 3) 0] i := by
  fin_cases i
  exacts [centroid_lat0, centroid_lat1, centroid_lat2, centroid_lat3, centroid_baseA,
    centroid_baseB]

lemma restrict_frontier_pyr : (μHE[2] : Measure E).restrict (frontier pyr) =
    ∑ i, (μHE[2] : Measure E).restrict (face6 i) := by
  rw [frontier_pyr, Measure.restrict_iUnion_ae (fun i j hij => hausdorff_face6_inter hij)
    (fun i => (isCompact_face6 i).isClosed.measurableSet.nullMeasurableSet),
    Measure.sum_fintype]

/-- **`S` of the pyramid** is `(0, 0, 1/2)`. -/
theorem surfCentroid_pyr : surfCentroid pyr = pt3 0 0 (1 / 2) := by
  change centroid ((μHE[2] : Measure E).restrict (frontier pyr)) = _
  have hint : ∀ i, ∫ x, x ∂((μHE[2] : Measure E).restrict (face6 i)) =
      ((μHE[2] : Measure E) (face6 i)).toReal •
        centroid ((μHE[2] : Measure E).restrict (face6 i)) := fun i => by
    have : IsFiniteMeasure ((μHE[2] : Measure E).restrict (face6 i)) :=
      isFiniteMeasure_restrict.2 (face6_ne_top i)
    rw [integral_eq_smul_centroid, Measure.restrict_apply_univ]
  rw [centroid, restrict_frontier_pyr, integral_finsetSum_measure fun i _ =>
      integrable_id_restrict (isCompact_face6 i) (face6_ne_top i),
    Measure.finsetSum_apply, ENNReal.toReal_sum fun i _ => by
      rw [Measure.restrict_apply_univ]; exact face6_ne_top i]
  simp only [Measure.restrict_apply_univ, hint, area_face6, centroid_face6, Fin.sum_univ_six]
  have hK := K_pos.ne'
  ext j; fin_cases j <;> simp <;> field_simp <;> ring

/-! ### The counterexample -/

lemma hausdorff_frontier_pyr_ne_top : (μHE[2] : Measure E) (frontier pyr) ≠ ⊤ := by
  rw [frontier_pyr]
  exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => face6_ne_top i)
    (measure_iUnion_fintype_le _ _)

lemma hausdorff_frontier_pyr_ne_zero : (μHE[2] : Measure E) (frontier pyr) ≠ 0 := by
  have h0 : 0 < ((μHE[2] : Measure E) (face6 0)).toReal := by
    have := mul_pos K_pos (show (0 : ℝ) < 3 by norm_num)
    simpa [area_face6] using this
  refine fun hz => (ENNReal.toReal_pos_iff.1 h0).1.ne' (measure_mono_null ?_ hz)
  rw [frontier_pyr]
  exact Set.subset_iUnion face6 0

/-- **The converse of the main theorem fails.** The square pyramid is a solid to which the main
theorem applies, it has `S = B`, and yet its symmetries fix more than one point. -/
theorem pyramid_counterexample :
    IsCompact pyr ∧ volume pyr ≠ 0 ∧ (μHE[2] : Measure E) (frontier pyr) ≠ 0 ∧
      (μHE[2] : Measure E) (frontier pyr) ≠ ⊤ ∧ surfCentroid pyr = volCentroid pyr ∧
        ¬ ∃ c, ∀ x ∈ fixedSet pyr, x = c :=
  ⟨isCompact_pyr, volume_pyr_ne_zero, hausdorff_frontier_pyr_ne_zero,
    hausdorff_frontier_pyr_ne_top, surfCentroid_pyr.trans volCentroid_pyr.symm,
    not_unique_fixed_point_pyr⟩

end SymmetricCentroids.Pyramid

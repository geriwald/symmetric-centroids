/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.Pyramid
public import SymmetricCentroids.SnubSolids

/-!
# The square pyramid: its volume centroid, and two points its symmetries fix

The plane `y = 0` cuts the pyramid into the tetrahedra `tetA` (`y ≥ 0`) and `tetB` (`y ≤ 0`),
mirror images of each other, whose common part lies in a plane. So `B` is the mean of their
centroids, `(0, 1/4, 1/2)` and `(0, -1/4, 1/2)`, that is `(0, 0, 1/2)`. Every symmetry fixes `B`,
and fixes the apex, the only point of the pyramid at distance `3/2` from `B`.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace SymmetricCentroids.Pyramid

open Tetrahedron

lemma mem_pyr {x : E} : x ∈ pyr ↔ 0 ≤ x 2 ∧ x 0 + x 1 + x 2 / 2 ≤ 1 ∧ -x 0 + x 1 + x 2 / 2 ≤ 1 ∧
    -x 0 - x 1 + x 2 / 2 ≤ 1 ∧ x 0 - x 1 + x 2 / 2 ≤ 1 := Iff.rfl

lemma convex_pyr : Convex ℝ pyr := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3, x4, x5⟩ := hx
  obtain ⟨y1, y2, y3, y4, y5⟩ := hy
  simp only [mem_pyr, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb,
      mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hb,
      mul_le_mul_of_nonneg_left x4 ha, mul_le_mul_of_nonneg_left y4 hb,
      mul_le_mul_of_nonneg_left x5 ha, mul_le_mul_of_nonneg_left y5 hb]

lemma isClosed_pyr : IsClosed pyr := by
  have c : ∀ i : Fin 3, Continuous fun x : E => x i := fun i => (EuclideanSpace.proj i).continuous
  have z := (c 2).div_const 2
  exact (isClosed_le continuous_const (c 2)).inter
    ((isClosed_le (((c 0).add (c 1)).add z) continuous_const).inter
    ((isClosed_le (((c 0).neg.add (c 1)).add z) continuous_const).inter
    ((isClosed_le (((c 0).neg.sub (c 1)).add z) continuous_const).inter
    (isClosed_le (((c 0).sub (c 1)).add z) continuous_const))))

lemma isCompact_pyr : IsCompact pyr := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_pyr ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨3, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right, ← sq_le_sq₀ (norm_nonneg _) (by norm_num),
    EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith

/-! ### The two tetrahedra -/

lemma vertex_mem_pyr_A (i : Fin 4) : tetA i ∈ pyr := by
  fin_cases i <;> simp [tetA, b0, b1, b2, apex, mem_pyr]

lemma vertex_mem_pyr_B (i : Fin 4) : tetB i ∈ pyr := by
  fin_cases i <;> simp [tetB, b0, b2, b3, apex, mem_pyr]

lemma solid_tetA_subset : solid tetA ⊆ pyr :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact vertex_mem_pyr_A i) convex_pyr

lemma solid_tetB_subset : solid tetB ⊆ pyr :=
  convexHull_min (by rintro _ ⟨i, rfl⟩; exact vertex_mem_pyr_B i) convex_pyr

lemma mem_solid_of_weights (v : Fin 4 → E) (w : Fin 4 → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : ∑ i, w i • v i ∈ solid v :=
  (convex_convexHull ℝ _).sum_mem (fun i _ => hw0 i) hw1
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

/-- The pyramid is the union of the two tetrahedra. -/
lemma pyr_eq_union : pyr = solid tetA ∪ solid tetB := by
  refine subset_antisymm (fun x hx => ?_) (Set.union_subset solid_tetA_subset solid_tetB_subset)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  rcases le_total 0 (x 1) with hy | hy
  · left
    have hx : x = ∑ i, ![(1 - x 1 - x 2 / 2 + x 0) / 2, x 1, (1 - x 1 - x 2 / 2 - x 0) / 2,
        x 2 / 2] i • tetA i := by
      ext j; fin_cases j <;> simp [Fin.sum_univ_four, tetA, b0, b1, b2, apex]; ring
    rw [hx]
    refine mem_solid_of_weights _ _ (fun i => ?_) (by simp [Fin.sum_univ_four]; ring)
    fin_cases i <;> simp <;> linarith
  · right
    have hx : x = ∑ i, ![(1 + x 1 - x 2 / 2 + x 0) / 2, (1 + x 1 - x 2 / 2 - x 0) / 2, -x 1,
        x 2 / 2] i • tetB i := by
      ext j; fin_cases j <;> simp [Fin.sum_univ_four, tetB, b0, b2, b3, apex]; ring
    rw [hx]
    refine mem_solid_of_weights _ _ (fun i => ?_) (by simp [Fin.sum_univ_four]; ring)
    fin_cases i <;> simp <;> linarith

lemma affineIndependent_tetA : AffineIndependent ℝ tetA := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs i
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
    Finset.weightedVSubOfPoint_apply] at hs
  have e0 := congrArg (· 0) hs
  have e1 := congrArg (· 1) hs
  have e2 := congrArg (· 2) hs
  simp [Fin.sum_univ_four, tetA, b0, b1, b2, apex] at e0 e1 e2 hw
  fin_cases i <;> simp <;> linarith

lemma affineIndependent_tetB : AffineIndependent ℝ tetB := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs i
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
    Finset.weightedVSubOfPoint_apply] at hs
  have e0 := congrArg (· 0) hs
  have e1 := congrArg (· 1) hs
  have e2 := congrArg (· 2) hs
  simp [Fin.sum_univ_four, tetB, b0, b2, b3, apex] at e0 e1 e2 hw
  fin_cases i <;> simp <;> linarith

/-- The two tetrahedra meet in a set of zero volume: it lies in the plane `y = 0`. -/
lemma volume_inter_tet : volume (solid tetA ∩ solid tetB) = 0 := by
  have hA : solid tetA ⊆ {x : E | 0 ≤ x 1} := convexHull_min
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> simp [tetA, b0, b1, b2, apex])
    (convex_halfSpace_ge (EuclideanSpace.proj (1 : Fin 3)).isLinear 0)
  have hB : solid tetB ⊆ {x : E | x 1 ≤ 0} := convexHull_min
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> simp [tetB, b0, b2, b3, apex])
    (convex_halfSpace_le (EuclideanSpace.proj (1 : Fin 3)).isLinear 0)
  set H : Submodule ℝ E := LinearMap.ker (EuclideanSpace.proj (1 : Fin 3) : E →L[ℝ] ℝ).toLinearMap
  have hH : H ≠ ⊤ := by
    intro h
    have : pt3 0 1 0 ∈ H := h ▸ Submodule.mem_top
    simp [H] at this
  refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_submodule volume H hH)
  have h1 := hA hx.1
  have h2 := hB hx.2
  simp only [Set.mem_ofPred_eq] at h1 h2
  simp [H]
  linarith

/-- The mirror `y ↦ -y` sends `tetA` onto `tetB`, so the two have the same volume. -/
lemma volume_tetA_eq_tetB : volume (solid tetA) = volume (solid tetB) := by
  set g : E ≃ᵃⁱ[ℝ] E := (Snub.signedPerm 1 ![false, true, false]).toAffineIsometryEquiv
  have hg : ∀ x : E, g x = pt3 (x 0) (-x 1) (x 2) := fun x => by
    ext i; fin_cases i <;> simp [g, Snub.signedPerm_apply, Snub.sgn]
  have himg : g '' solid tetA = solid tetB := by
    rw [solid, solid, show (⇑g : E → E) = ⇑(g.toAffineEquiv.toAffineMap) from rfl,
      AffineMap.image_convexHull]
    congr 1
    ext x; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · exact ⟨0, by simp [hg, tetA, tetB, b0]⟩
      · exact ⟨2, by simp [hg, tetA, tetB, b1, b3]⟩
      · exact ⟨1, by simp [hg, tetA, tetB, b2]⟩
      · exact ⟨3, by simp [hg, tetA, tetB, apex]⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨tetA 0, ⟨0, rfl⟩, by simp [hg, tetA, tetB, b0]⟩
      · exact ⟨tetA 2, ⟨2, rfl⟩, by simp [hg, tetA, tetB, b2]⟩
      · exact ⟨tetA 1, ⟨1, rfl⟩, by simp [hg, tetA, tetB, b1, b3]⟩
      · exact ⟨tetA 3, ⟨3, rfl⟩, by simp [hg, tetA, tetB, apex]⟩
  rw [← himg, ← (measurePreserving_volume g).measure_preimage
    (isCompact_solid.image g.continuous).isClosed.measurableSet.nullMeasurableSet,
    Set.preimage_image_eq _ g.injective]

/-! ### `B` of the pyramid -/

lemma volume_pyr_ne_zero : volume pyr ≠ 0 := fun h =>
  volume_solid_ne_zero affineIndependent_tetA (measure_mono_null solid_tetA_subset h)

/-- **`B` of the pyramid** is `(0, 0, 1/2)`. -/
theorem volCentroid_pyr : volCentroid pyr = pt3 0 0 (1 / 2) := by
  have hAc : IsCompact (solid tetA) := isCompact_solid
  have hBc : IsCompact (solid tetB) := isCompact_solid
  have : IsFiniteMeasure (volume.restrict (solid tetA)) :=
    isFiniteMeasure_restrict.2 hAc.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (solid tetB)) :=
    isFiniteMeasure_restrict.2 hBc.measure_lt_top.ne
  have hsplit :
      volume.restrict pyr = volume.restrict (solid tetA) + volume.restrict (solid tetB) := by
    rw [pyr_eq_union, ← Measure.restrict_union_add_inter _ hBc.isClosed.measurableSet,
      Measure.restrict_eq_zero.2 volume_inter_tet, add_zero]
  set m := (volume (solid tetA)).toReal
  have hm : m ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨volume_solid_ne_zero affineIndependent_tetA, hAc.measure_lt_top.ne⟩
  have hmB : (volume (solid tetB)).toReal = m := by rw [← volume_tetA_eq_tetB]
  have iA := integral_eq_smul_centroid (volume.restrict (solid tetA))
  have iB := integral_eq_smul_centroid (volume.restrict (solid tetB))
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at iA iB
  rw [hmB] at iB
  have cA : centroid (volume.restrict (solid tetA)) = pt3 0 (1 / 4) (1 / 2) := by
    change volCentroid (solid tetA) = _
    rw [volCentroid_solid affineIndependent_tetA]
    ext i; fin_cases i <;> simp [Fin.sum_univ_four, tetA, b0, b1, b2, apex]; norm_num
  have cB : centroid (volume.restrict (solid tetB)) = pt3 0 (-1 / 4) (1 / 2) := by
    change volCentroid (solid tetB) = _
    rw [volCentroid_solid affineIndependent_tetB]
    ext i; fin_cases i <;> simp [Fin.sum_univ_four, tetB, b0, b2, b3, apex] <;> norm_num
  unfold volCentroid centroid
  rw [hsplit, integral_add_measure (integrable_id_restrict hAc hAc.measure_lt_top.ne)
    (integrable_id_restrict hBc hBc.measure_lt_top.ne), Measure.add_apply,
    Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Set.univ_inter, ENNReal.toReal_add hAc.measure_lt_top.ne
      hBc.measure_lt_top.ne, hmB]
  rw [iA, iB, cA, cB, show (volume (solid tetA)).toReal = m from rfl]
  ext i; fin_cases i <;> simp <;> field_simp; ring

/-! ### Two points fixed by every symmetry -/

/-- The apex is the only point of the pyramid at distance `3/2` from `(0, 0, 1/2)`; every other
point is closer. -/
lemma eq_apex_of_dist (x : E) (hx : x ∈ pyr) (h : dist x (pt3 0 0 (1 / 2)) = 3 / 2) :
    x = apex := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  have hd := congrArg (· ^ 2) h
  simp only [Tetrahedron.dist_sq, dotProduct, Fin.sum_univ_three, WithLp.ofLp_sub,
    Pi.sub_apply] at hd
  simp only [pt3, PiLp.toLp_apply] at hd
  norm_num at hd
  have hz : x 2 ≤ 2 := by linarith
  have hs : (x 0 + x 1) ^ 2 ≤ (1 - x 2 / 2) ^ 2 := by nlinarith
  have hd' : (x 0 - x 1) ^ 2 ≤ (1 - x 2 / 2) ^ 2 := by nlinarith
  have hz2 : x 2 = 2 := by nlinarith
  have e1 : x 0 + x 1 = 0 := by nlinarith
  have e2 : x 0 - x 1 = 0 := by nlinarith
  ext i; fin_cases i <;> simp [apex] <;> linarith

lemma volCentroid_mem_fixedSet : pt3 0 0 (1 / 2) ∈ fixedSet pyr := fun _ hg =>
  volCentroid_pyr ▸ volCentroid_fixed isCompact_pyr volume_pyr_ne_zero hg

lemma apex_mem_pyr : apex ∈ pyr := by simp [apex, mem_pyr]

lemma apex_mem_fixedSet : apex ∈ fixedSet pyr := by
  intro g hg
  have hB := volCentroid_mem_fixedSet g hg
  refine eq_apex_of_dist _ ?_ ?_
  · rw [← hg]; exact ⟨apex, apex_mem_pyr, rfl⟩
  · rw [← hB, g.dist_map]
    rw [dist_comm, ← sq_eq_sq₀ dist_nonneg (by norm_num), Tetrahedron.dist_sq]
    simp [apex, pt3, dotProduct, Fin.sum_univ_three]; norm_num

/-- **The symmetries of the pyramid fix more than one point**: `B` and the apex. -/
theorem not_unique_fixed_point_pyr : ¬ ∃ c, ∀ x ∈ fixedSet pyr, x = c := by
  rintro ⟨c, hc⟩
  have h := (hc _ apex_mem_fixedSet).trans (hc _ volCentroid_mem_fixedSet).symm
  have := congrArg (· 2) h
  simp [apex] at this
  norm_num at this

end SymmetricCentroids.Pyramid

/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.SimplexCentroid

/-!
# The centroid of a triangle in space, under the area measure

A triangle `abc` of ℝ³ lies in the plane through `a` spanned by `b - a` and `c - a`. An
orthonormal basis of that plane gives an isometric affine embedding `ι` of ℝ² onto it, and
`Isometry.map_euclideanHausdorffMeasure` carries the area of ℝ² to the area measure `μHE[2]` on the
plane. So `μHE[2]` restricted to the triangle is the image under `ι` of the area restricted to a
planar triangle, and the centroids follow (`centroid_map`).
-/

open MeasureTheory Module

@[expose] public noncomputable section

namespace SymmetricCentroids

variable {n : ℕ} {a b c : E} (h : LinearIndependent ℝ ![b - a, c - a])

/-- The plane through the origin spanned by `b - a` and `c - a`. -/
def planeSpan (a b c : E) : Submodule ℝ E := Submodule.span ℝ (Set.range ![b - a, c - a])

include h in
lemma finrank_planeSpan : finrank ℝ (planeSpan a b c) = 2 := by
  rw [planeSpan, finrank_span_eq_card h]; simp

/-- An orthonormal basis of the plane, indexed by `Fin 2`. -/
def planeBasis : OrthonormalBasis (Fin 2) ℝ (planeSpan a b c) :=
  (stdOrthonormalBasis ℝ (planeSpan a b c)).reindex (finCongr (finrank_planeSpan h))

/-- The linear isometry from ℝ² onto the plane. -/
def planeLin : Space 2 →ₗᵢ[ℝ] E :=
  (planeSpan a b c).subtypeₗᵢ.comp (planeBasis h).repr.symm.toLinearIsometry

/-- The isometric affine embedding of ℝ² onto the plane of the triangle, `0 ↦ a`. -/
def planeEmbedding : Space 2 →ᵃ[ℝ] E :=
  (planeLin h).toLinearMap.toAffineMap + AffineMap.const ℝ (Space 2) a

lemma planeEmbedding_apply (x : Space 2) : planeEmbedding h x = planeLin h x + a := rfl

lemma isometry_planeEmbedding : Isometry (planeEmbedding h) :=
  Isometry.of_dist_eq fun x y => by
    simp only [planeEmbedding_apply, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub,
      LinearIsometry.norm_map]

/-- The preimage of `b - a` in ℝ². -/
def preB : Space 2 := (planeBasis h).repr ⟨b - a, Submodule.subset_span ⟨0, rfl⟩⟩

/-- The preimage of `c - a` in ℝ². -/
def preC : Space 2 := (planeBasis h).repr ⟨c - a, Submodule.subset_span ⟨1, rfl⟩⟩

lemma planeEmbedding_zero : planeEmbedding h 0 = a := by simp [planeEmbedding_apply]

lemma planeEmbedding_preB : planeEmbedding h (preB h) = b := by
  simp [planeEmbedding_apply, planeLin, preB]

lemma planeEmbedding_preC : planeEmbedding h (preC h) = c := by
  simp [planeEmbedding_apply, planeLin, preC]

lemma image_planarTriangle :
    planeEmbedding h '' convexHull ℝ {0, preB h, preC h} = convexHull ℝ {a, b, c} := by
  rw [AffineMap.image_convexHull, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    planeEmbedding_zero, planeEmbedding_preB, planeEmbedding_preC]

/-- The area measure of ℝ², carried onto the plane, is `μHE[2]` on the plane. -/
lemma map_planeEmbedding_volume :
    (volume : Measure (Space 2)).map (planeEmbedding h) =
      (μHE[2] : Measure E).restrict (Set.range (planeEmbedding h)) := by
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2]
  exact (isometry_planeEmbedding h).map_euclideanHausdorffMeasure

/-- `μHE[2]` restricted to the triangle is the image of the area restricted to the planar
triangle. -/
lemma map_planarTriangle :
    (volume.restrict (convexHull ℝ {0, preB h, preC h})).map (planeEmbedding h) =
      (μHE[2] : Measure E).restrict (convexHull ℝ {a, b, c}) := by
  have hT : IsClosed (convexHull ℝ ({a, b, c} : Set E)) :=
    ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hpre : planeEmbedding h ⁻¹' convexHull ℝ {a, b, c} = convexHull ℝ {0, preB h, preC h} := by
    rw [← image_planarTriangle h, Set.preimage_image_eq _ (isometry_planeEmbedding h).injective]
  have hsub : convexHull ℝ ({a, b, c} : Set E) ⊆ Set.range (planeEmbedding h) := by
    rw [← image_planarTriangle h]; exact Set.image_subset_range _ _
  rw [← hpre, ← Measure.restrict_map (isometry_planeEmbedding h).continuous.measurable
    hT.measurableSet, map_planeEmbedding_volume, Measure.restrict_restrict hT.measurableSet,
    Set.inter_eq_left.2 hsub]

/-! ### A planar triangle -/

/-- A measure restricted to a compact set of finite measure has a first moment. -/
lemma integrable_id_restrict {μ : Measure (Space n)} {s : Set (Space n)} (hs : IsCompact s)
    (hfin : μ s ≠ ⊤) : Integrable (fun x : Space n => x) (μ.restrict s) := by
  obtain ⟨C, hC⟩ := hs.isBounded.exists_norm_le
  exact Measure.integrableOn_of_bounded hfin continuous_id.aestronglyMeasurable
    ((ae_restrict_iff' hs.isClosed.measurableSet).2 (Filter.Eventually.of_forall hC))

variable {q₁ q₂ : Space 2}

/-- The linear map `x ↦ x₀ q₁ + x₁ q₂`, which sends the standard triangle onto `0 q₁ q₂`. -/
def planarLin (q₁ q₂ : Space 2) : Space 2 →ₗ[ℝ] Space 2 where
  toFun x := x 0 • q₁ + x 1 • q₂
  map_add' x y := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' r x := by simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, smul_add]; rfl

lemma planarLin_injective (hq : LinearIndependent ℝ ![q₁, q₂]) :
    Function.Injective (planarLin q₁ q₂) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 hq _ _ hx
  ext i; fin_cases i <;> simp [h0, h1]

lemma image_stdTriangle_planarLin :
    planarLin q₁ q₂ '' stdTriangle = convexHull ℝ {0, q₁, q₂} := by
  rw [stdTriangle, LinearMap.image_convexHull, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton]
  simp [planarLin]

/-- The area restricted to the triangle `0 q₁ q₂` is a positive multiple of the image of the area
restricted to the standard triangle. -/
lemma map_stdTriangle_planarLin (hq : LinearIndependent ℝ ![q₁, q₂]) :
    (volume.restrict stdTriangle).map (planarLin q₁ q₂) =
      ENNReal.ofReal |(LinearMap.det (planarLin q₁ q₂))⁻¹| •
        volume.restrict (convexHull ℝ {0, q₁, q₂}) := by
  have hinj := planarLin_injective hq
  have hdet : LinearMap.det (planarLin q₁ q₂) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]; exact hinj
  have hS : IsClosed (convexHull ℝ ({0, q₁, q₂} : Set (Space 2))) :=
    ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)).isClosed
  rw [← Measure.restrict_smul, ← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
    Measure.restrict_map (planarLin q₁ q₂).continuous_of_finiteDimensional.measurable
      hS.measurableSet, ← image_stdTriangle_planarLin, Set.preimage_image_eq _ hinj]

lemma smul_factor_ne_zero (hq : LinearIndependent ℝ ![q₁, q₂]) :
    ENNReal.ofReal |(LinearMap.det (planarLin q₁ q₂))⁻¹| ≠ 0 := by
  have hdet : LinearMap.det (planarLin q₁ q₂) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact planarLin_injective hq
  simpa using hdet

/-- **A planar triangle.** The centroid of the area restricted to the triangle `0 q₁ q₂` is
`(q₁ + q₂)/3`, and that area is not zero. -/
theorem centroid_planarTriangle (hq : LinearIndependent ℝ ![q₁, q₂]) :
    centroid (volume.restrict (convexHull ℝ {0, q₁, q₂})) = (3 : ℝ)⁻¹ • (q₁ + q₂) ∧
      volume (convexHull ℝ ({0, q₁, q₂} : Set (Space 2))) ≠ 0 := by
  have hT := isCompact_stdTriangle
  have : IsFiniteMeasure (volume.restrict stdTriangle) :=
    isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
  have hμ : volume.restrict stdTriangle ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact volume_stdTriangle_ne_zero
  have hmap := map_stdTriangle_planarLin hq
  have hk0 := smul_factor_ne_zero hq
  have hk : ENNReal.ofReal |(LinearMap.det (planarLin q₁ q₂))⁻¹| ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨?_, ?_⟩
  · have hm := centroid_map _ hμ (integrable_id_restrict hT hT.measure_lt_top.ne)
      (planarLin q₁ q₂).toAffineMap
    simp only [LinearMap.coe_toAffineMap] at hm
    rw [← centroid_smul _ hk0 hk, ← hmap, hm, centroid_stdTriangle]
    ext i; fin_cases i <;> simp [planarLin]
  · intro h0
    have := congrArg (fun μ : Measure (Space 2) => μ Set.univ) hmap
    simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, h0,
      smul_zero, Measure.map_apply (planarLin q₁ q₂).continuous_of_finiteDimensional.measurable
        MeasurableSet.univ, Set.preimage_univ] at this
    exact volume_stdTriangle_ne_zero this

/-! ### A triangle in space -/

include h in
lemma linearIndependent_pre : LinearIndependent ℝ ![preB h, preC h] := by
  have h' : LinearIndependent ℝ ![(⟨b - a, Submodule.subset_span ⟨0, rfl⟩⟩ : planeSpan a b c),
      ⟨c - a, Submodule.subset_span ⟨1, rfl⟩⟩] :=
    LinearIndependent.of_comp (planeSpan a b c).subtype (by
      convert h using 1; ext i; fin_cases i <;> rfl)
  have := h'.map' (planeBasis h).repr.toLinearEquiv.toLinearMap
    (planeBasis h).repr.toLinearEquiv.ker
  convert this using 1; ext i; fin_cases i <;> rfl

include h in
/-- **The centroid of a triangle in space**, under the area measure `μHE[2]`, is the mean of its
vertices. -/
theorem centroid_triangle :
    centroid ((μHE[2] : Measure E).restrict (convexHull ℝ {a, b, c})) =
      (3 : ℝ)⁻¹ • (a + b + c) := by
  obtain ⟨hc, hne⟩ := centroid_planarTriangle (linearIndependent_pre h)
  have hK : IsCompact (convexHull ℝ ({0, preB h, preC h} : Set (Space 2))) :=
    (Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)
  have : IsFiniteMeasure (volume.restrict (convexHull ℝ ({0, preB h, preC h} : Set (Space 2)))) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hμ : volume.restrict (convexHull ℝ ({0, preB h, preC h} : Set (Space 2))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hne
  rw [← map_planarTriangle h,
    centroid_map _ hμ (integrable_id_restrict hK hK.measure_lt_top.ne) (planeEmbedding h), hc]
  have hb : planeLin h (preB h) = b - a :=
    eq_sub_of_add_eq (by have := planeEmbedding_preB h; rwa [planeEmbedding_apply] at this)
  have hc' : planeLin h (preC h) = c - a :=
    eq_sub_of_add_eq (by have := planeEmbedding_preC h; rwa [planeEmbedding_apply] at this)
  rw [planeEmbedding_apply, map_smul, map_add, hb, hc']
  module

end SymmetricCentroids

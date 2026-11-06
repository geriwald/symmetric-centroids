/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids

/-!
# The centroid of a triangle is the mean of its vertices

An affine map carries the centroid of a measure to the centroid of its image (`centroid_map`).
The standard triangle turns onto itself by an affine map of determinant one that permutes its
vertices, and the only point that map fixes is `(1/3, 1/3)`: that is the centroid of the standard
triangle (`centroid_stdTriangle`).
-/

open MeasureTheory

@[expose] public noncomputable section

namespace SymmetricCentroids

variable {m n : ℕ}

/-- **Affine equivariance.** An affine map carries the centroid of a finite, nonzero measure with
a first moment to the centroid of the image measure. -/
theorem centroid_map (μ : Measure (Space m)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hint : Integrable (fun x : Space m => x) μ) (f : Space m →ᵃ[ℝ] Space n) :
    centroid (μ.map f) = f (centroid μ) := by
  have hf : Continuous f := f.continuous_of_finiteDimensional
  have hL : Continuous f.linear := f.linear.continuous_of_finiteDimensional
  set L : Space m →L[ℝ] Space n := ⟨f.linear, hL⟩
  set M := (μ Set.univ).toReal with hM
  have hM0 : M ≠ 0 := by
    rw [hM, ENNReal.toReal_ne_zero]
    exact ⟨Measure.measure_univ_ne_zero.2 hμ, measure_ne_top μ _⟩
  have huniv : (μ.map f) Set.univ = μ Set.univ := by
    rw [Measure.map_apply hf.measurable MeasurableSet.univ, Set.preimage_univ]
  have hI : ∫ x, x ∂(μ.map f) = L (∫ x, x ∂μ) + M • f 0 := by
    calc ∫ x, x ∂(μ.map f) = ∫ x, f x ∂μ :=
          integral_map hf.aemeasurable continuous_id.aestronglyMeasurable
      _ = ∫ x, (L x + f 0) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun f.decomp x)
      _ = ∫ x, L x ∂μ + ∫ _, f 0 ∂μ := integral_add (L.integrable_comp hint) (integrable_const _)
      _ = L (∫ x, x ∂μ) + M • f 0 := by
          rw [L.integral_comp_comm hint, integral_const]; rfl
  unfold centroid
  rw [huniv, hI, ← hM]
  conv_rhs => rw [f.decomp]
  simp only [Pi.add_apply, map_smul]
  rw [smul_add, smul_smul, inv_mul_cancel₀ hM0, one_smul]
  rfl

/-! ### The standard triangle -/

/-- The point `(a, b)` of the plane. -/
def pt2 (a b : ℝ) : Space 2 := WithLp.toLp 2 ![a, b]

@[simp] lemma pt2_zero (a b : ℝ) : pt2 a b 0 = a := rfl
@[simp] lemma pt2_one (a b : ℝ) : pt2 a b 1 = b := rfl

/-- The standard triangle, with vertices `(0, 0)`, `(1, 0)` and `(0, 1)`. -/
def stdTriangle : Set (Space 2) := convexHull ℝ {pt2 0 0, pt2 1 0, pt2 0 1}

/-- The linear part of `rot`: `(x, y) ↦ (y, -x - y)`, of determinant one. -/
def rotLin : Space 2 →ₗ[ℝ] Space 2 where
  toFun x := pt2 (x 1) (-x 0 - x 1)
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp; ring

/-- `(x, y) ↦ (y, 1 - x - y)`, which permutes the vertices of the standard triangle. -/
def rot : Space 2 →ᵃ[ℝ] Space 2 := rotLin.toAffineMap + AffineMap.const ℝ (Space 2) (pt2 0 1)

lemma rot_apply (x : Space 2) : rot x = pt2 (x 1) (1 - x 0 - x 1) := by
  ext i; fin_cases i <;> simp [rot, rotLin]; ring

lemma rot_rot_rot (x : Space 2) : rot (rot (rot x)) = x := by
  ext i; fin_cases i <;> simp [rot_apply]; ring

lemma rot_image_subset : rot '' stdTriangle ⊆ stdTriangle := by
  rw [stdTriangle, AffineMap.image_convexHull]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro _ ⟨p, hp, rfl⟩
  apply subset_convexHull
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl <;> simp [rot_apply]

lemma rot_preimage : rot ⁻¹' stdTriangle = stdTriangle := by
  ext x
  refine ⟨fun hx => ?_, fun hx => rot_image_subset ⟨x, hx, rfl⟩⟩
  rw [← rot_rot_rot x]
  exact rot_image_subset ⟨_, rot_image_subset ⟨_, hx, rfl⟩, rfl⟩

lemma det_rotLin : LinearMap.det rotLin = 1 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, rotLin]

lemma map_rot_volume : Measure.map rot (volume : Measure (Space 2)) = volume := by
  have hlin : Measure.map rotLin (volume : Measure (Space 2)) = volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_rotLin]; norm_num),
      det_rotLin]
    simp
  have hrot : (rot : Space 2 → Space 2) = (· + pt2 0 1) ∘ rotLin := by
    funext x; simp [rot]
  rw [hrot, ← Measure.map_map (measurable_add_const _)
    rotLin.continuous_of_finiteDimensional.measurable, hlin]
  exact (measurePreserving_add_right volume (pt2 0 1)).map_eq

lemma isCompact_stdTriangle : IsCompact stdTriangle :=
  (Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)

lemma volume_stdTriangle_ne_zero : volume stdTriangle ≠ 0 := by
  set U : Set (Space 2) := {x | 0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < 1}
  have hU : IsOpen U := by
    have c0 : Continuous fun x : Space 2 => x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have c1 : Continuous fun x : Space 2 => x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const c0).inter
      ((isOpen_lt continuous_const c1).inter (isOpen_lt (c0.add c1) continuous_const))
  have hne : U.Nonempty := ⟨pt2 (1 / 4) (1 / 4), by simp [U]; norm_num⟩
  have hsub : U ⊆ stdTriangle := by
    rintro x ⟨h0, h1, h01⟩
    have hx : x = ∑ i, ![1 - x 0 - x 1, x 0, x 1] i • ![pt2 0 0, pt2 1 0, pt2 0 1] i := by
      ext j; fin_cases j <;> simp [Fin.sum_univ_three]
    rw [hx]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => subset_convexHull ℝ _ ?_)
    · fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_three]; ring
    · fin_cases i <;> simp
  exact (hU.measure_pos volume hne).ne' ∘ fun h => measure_mono_null hsub h

/-- **The centroid of the standard triangle is `(1/3, 1/3)`.** -/
theorem centroid_stdTriangle : centroid (volume.restrict stdTriangle) = pt2 (1 / 3) (1 / 3) := by
  have hT := isCompact_stdTriangle
  have : IsFiniteMeasure (volume.restrict stdTriangle) :=
    isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
  have hint : Integrable (fun x : Space 2 => x) (volume.restrict stdTriangle) :=
    Measure.integrableOn_of_bounded hT.measure_lt_top.ne continuous_id.aestronglyMeasurable
      ((ae_restrict_iff' hT.isClosed.measurableSet).2 (Filter.Eventually.of_forall hC))
  have hμ : volume.restrict stdTriangle ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact volume_stdTriangle_ne_zero
  have hmap : (volume.restrict stdTriangle).map rot = volume.restrict stdTriangle := by
    conv_lhs => rw [← rot_preimage]
    rw [← Measure.restrict_map rot.continuous_of_finiteDimensional.measurable
      hT.isClosed.measurableSet, map_rot_volume]
  have hfix := centroid_map _ hμ hint rot
  rw [hmap] at hfix
  set c := centroid (volume.restrict stdTriangle)
  have e0 := congrArg (· 0) hfix
  have e1 := congrArg (· 1) hfix
  simp only [rot_apply, pt2_zero, pt2_one] at e0 e1
  ext i; fin_cases i <;> simp <;> linarith

end SymmetricCentroids

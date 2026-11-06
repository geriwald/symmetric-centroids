/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.SimplexCentroid
public import SymmetricCentroids.TetrahedronFrontier

/-!
# `B` of a tetrahedron is the mean of its vertices

* `centroid_stdTetra`: the standard tetrahedron, with vertices `0`, `e₀`, `e₁` and `e₂`, has its
  volume centroid at `(1/4, 1/4, 1/4)`. The affine map `(x, y, z) ↦ (y, z, 1 - x - y - z)` cycles
  its four vertices and has determinant `-1`, so it preserves the volume of the standard
  tetrahedron; its only fixed point is `(1/4, 1/4, 1/4)`.
* `volCentroid_solid`: for four affinely independent points `v`, the volume centroid of the
  solid tetrahedron is `(v₀ + v₁ + v₂ + v₃)/4`. The affine map
  `u ↦ v₀ + u₀ (v₁ - v₀) + u₁ (v₂ - v₀) + u₂ (v₃ - v₀)` carries the standard tetrahedron onto the
  solid, and carries volume to a constant multiple of volume; a centroid ignores the constant.
-/

open MeasureTheory Set

@[expose] public noncomputable section

namespace SymmetricCentroids

/-! ### The standard tetrahedron -/

/-- The point `(a, b, c)` of space. -/
def pt3 (a b c : ℝ) : Space 3 := WithLp.toLp 2 ![a, b, c]

@[simp] lemma pt3_zero (a b c : ℝ) : pt3 a b c 0 = a := rfl
@[simp] lemma pt3_one (a b c : ℝ) : pt3 a b c 1 = b := rfl
@[simp] lemma pt3_two (a b c : ℝ) : pt3 a b c 2 = c := rfl

/-- The standard tetrahedron, with vertices `0`, `e₀`, `e₁` and `e₂`. -/
def stdTetra : Set (Space 3) := convexHull ℝ {pt3 0 0 0, pt3 1 0 0, pt3 0 1 0, pt3 0 0 1}

/-- The linear part of `rot3`: `(x, y, z) ↦ (y, z, -x - y - z)`, of determinant `-1`. -/
def rot3Lin : Space 3 →ₗ[ℝ] Space 3 where
  toFun x := pt3 (x 1) (x 2) (-x 0 - x 1 - x 2)
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp; ring

/-- `(x, y, z) ↦ (y, z, 1 - x - y - z)`, which cycles the vertices of the standard tetrahedron. -/
def rot3 : Space 3 →ᵃ[ℝ] Space 3 :=
  rot3Lin.toAffineMap + AffineMap.const ℝ (Space 3) (pt3 0 0 1)

lemma rot3_apply (x : Space 3) : rot3 x = pt3 (x 1) (x 2) (1 - x 0 - x 1 - x 2) := by
  ext i; fin_cases i <;> simp [rot3, rot3Lin]; ring

lemma rot3_four (x : Space 3) : rot3 (rot3 (rot3 (rot3 x))) = x := by
  ext i; fin_cases i <;> simp [rot3_apply]; ring

lemma rot3_image_subset : rot3 '' stdTetra ⊆ stdTetra := by
  rw [stdTetra, AffineMap.image_convexHull]
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro _ ⟨p, hp, rfl⟩
  apply subset_convexHull
  simp only [mem_insert_iff, mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl <;> simp [rot3_apply]

lemma rot3_preimage : rot3 ⁻¹' stdTetra = stdTetra := by
  ext x
  refine ⟨fun hx => ?_, fun hx => rot3_image_subset ⟨x, hx, rfl⟩⟩
  rw [← rot3_four x]
  exact rot3_image_subset ⟨_, rot3_image_subset ⟨_, rot3_image_subset ⟨_, hx, rfl⟩, rfl⟩, rfl⟩

lemma det_rot3Lin : LinearMap.det rot3Lin = -1 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, rot3Lin]

lemma map_rot3_volume : Measure.map rot3 (volume : Measure (Space 3)) = volume := by
  have hlin : Measure.map rot3Lin (volume : Measure (Space 3)) = volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_rot3Lin]; norm_num),
      det_rot3Lin]
    simp
  have hrot : (rot3 : Space 3 → Space 3) = (· + pt3 0 0 1) ∘ rot3Lin := by
    funext x; simp [rot3]
  rw [hrot, ← Measure.map_map (measurable_add_const _)
    rot3Lin.continuous_of_finiteDimensional.measurable, hlin]
  exact (measurePreserving_add_right volume (pt3 0 0 1)).map_eq

lemma isCompact_stdTetra : IsCompact stdTetra :=
  (toFinite _).isCompact_convexHull (𝕜 := ℝ)

lemma volume_stdTetra_ne_zero : volume stdTetra ≠ 0 := by
  set U : Set (Space 3) := {x | 0 < x 0 ∧ 0 < x 1 ∧ 0 < x 2 ∧ x 0 + x 1 + x 2 < 1}
  have hU : IsOpen U := by
    have c0 : Continuous fun x : Space 3 => x 0 := (EuclideanSpace.proj (0 : Fin 3)).continuous
    have c1 : Continuous fun x : Space 3 => x 1 := (EuclideanSpace.proj (1 : Fin 3)).continuous
    have c2 : Continuous fun x : Space 3 => x 2 := (EuclideanSpace.proj (2 : Fin 3)).continuous
    exact (isOpen_lt continuous_const c0).inter ((isOpen_lt continuous_const c1).inter
      ((isOpen_lt continuous_const c2).inter (isOpen_lt ((c0.add c1).add c2) continuous_const)))
  have hne : U.Nonempty := ⟨pt3 (1 / 8) (1 / 8) (1 / 8), by simp [U]; norm_num⟩
  have hsub : U ⊆ stdTetra := by
    rintro x ⟨h0, h1, h2, h012⟩
    have hx : x = ∑ i, ![1 - x 0 - x 1 - x 2, x 0, x 1, x 2] i •
        ![pt3 0 0 0, pt3 1 0 0, pt3 0 1 0, pt3 0 0 1] i := by
      ext j; fin_cases j <;> simp [Fin.sum_univ_four]
    rw [hx]
    refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => subset_convexHull ℝ _ ?_)
    · fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_four]; ring
    · fin_cases i <;> simp
  exact (hU.measure_pos volume hne).ne' ∘ fun h => measure_mono_null hsub h

/-- The restriction of volume to the standard tetrahedron is finite, nonzero, and has a first
moment. -/
lemma stdTetra_measure :
    IsFiniteMeasure (volume.restrict stdTetra) ∧ volume.restrict stdTetra ≠ 0 ∧
      Integrable (fun x : Space 3 => x) (volume.restrict stdTetra) := by
  have hT := isCompact_stdTetra
  obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
  refine ⟨isFiniteMeasure_restrict.2 hT.measure_lt_top.ne, ?_, ?_⟩
  · rw [Ne, Measure.restrict_eq_zero]; exact volume_stdTetra_ne_zero
  · exact Measure.integrableOn_of_bounded hT.measure_lt_top.ne
      continuous_id.aestronglyMeasurable
      ((ae_restrict_iff' hT.isClosed.measurableSet).2 (Filter.Eventually.of_forall hC))

/-- **The centroid of the standard tetrahedron is `(1/4, 1/4, 1/4)`.** -/
theorem centroid_stdTetra :
    centroid (volume.restrict stdTetra) = pt3 (1 / 4) (1 / 4) (1 / 4) := by
  obtain ⟨_, hμ, hint⟩ := stdTetra_measure
  have hT := isCompact_stdTetra
  have hmap : (volume.restrict stdTetra).map rot3 = volume.restrict stdTetra := by
    conv_lhs => rw [← rot3_preimage]
    rw [← Measure.restrict_map rot3.continuous_of_finiteDimensional.measurable
      hT.isClosed.measurableSet, map_rot3_volume]
  have hfix := centroid_map _ hμ hint rot3
  rw [hmap] at hfix
  set c := centroid (volume.restrict stdTetra)
  have e0 := congrArg (· 0) hfix
  have e1 := congrArg (· 1) hfix
  have e2 := congrArg (· 2) hfix
  simp only [rot3_apply, pt3_zero, pt3_one, pt3_two] at e0 e1 e2
  ext i; fin_cases i <;> simp <;> linarith

/-! ### Transport to any tetrahedron -/

namespace Tetrahedron

variable (v : Fin 4 → E)

/-- `u ↦ u₀ (v₁ - v₀) + u₁ (v₂ - v₀) + u₂ (v₃ - v₀)`. -/
def edgeLin : Space 3 →ₗ[ℝ] E where
  toFun u := u 0 • (v 1 - v 0) + u 1 • (v 2 - v 0) + u 2 • (v 3 - v 0)
  map_add' x y := by simp only [PiLp.add_apply]; module
  map_smul' c x := by simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; module

/-- The affine map that carries the standard tetrahedron onto the solid tetrahedron of `v`. -/
def edgeMap : Space 3 →ᵃ[ℝ] E := (edgeLin v).toAffineMap + AffineMap.const ℝ (Space 3) (v 0)

lemma edgeMap_apply (u : Space 3) :
    edgeMap v u = v 0 + u 0 • (v 1 - v 0) + u 1 • (v 2 - v 0) + u 2 • (v 3 - v 0) := by
  simp [edgeMap, edgeLin]; abel

variable {v}

/-- The barycentric coordinates of `edgeMap v u` are `(1 - u₀ - u₁ - u₂, u₀, u₁, u₂)`. -/
lemma coord_edgeMap (hv : AffineIndependent ℝ v) (u : Space 3) :
    (affineBasis hv).coord 1 (edgeMap v u) = u 0 ∧ (affineBasis hv).coord 2 (edgeMap v u) = u 1 ∧
      (affineBasis hv).coord 3 (edgeMap v u) = u 2 := by
  set b := affineBasis hv
  set w : Fin 4 → ℝ := ![1 - u 0 - u 1 - u 2, u 0, u 1, u 2]
  have hw : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_four]; ring
  have hcomb : edgeMap v u = Finset.univ.affineCombination ℝ b w := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hw, Fin.sum_univ_four,
      edgeMap_apply]
    change _ = w 0 • v 0 + w 1 • v 1 + w 2 • v 2 + w 3 • v 3
    simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    module
  rw [hcomb]
  exact ⟨b.coord_apply_combination_of_mem (Finset.mem_univ _) hw,
    b.coord_apply_combination_of_mem (Finset.mem_univ _) hw,
    b.coord_apply_combination_of_mem (Finset.mem_univ _) hw⟩

lemma edgeMap_injective (hv : AffineIndependent ℝ v) : Function.Injective (edgeMap v) := by
  intro u u' h
  obtain ⟨a0, a1, a2⟩ := coord_edgeMap hv u
  obtain ⟨b0, b1, b2⟩ := coord_edgeMap hv u'
  rw [h] at a0 a1 a2
  ext i; fin_cases i
  · exact a0.symm.trans b0
  · exact a1.symm.trans b1
  · exact a2.symm.trans b2

lemma det_edgeLin_ne_zero (hv : AffineIndependent ℝ v) :
    LinearMap.det (edgeLin v : Space 3 →ₗ[ℝ] Space 3) ≠ 0 := by
  have hinj : Function.Injective (edgeLin v) := by
    intro x y h
    apply edgeMap_injective hv
    simp [edgeMap, h]
  exact (LinearMap.isUnit_det _
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.2 hinj))).ne_zero

lemma edgeMap_image : edgeMap v '' stdTetra = solid v := by
  have hr : range v = {v 0, v 1, v 2, v 3} := by
    ext x; simp only [mem_range, mem_insert_iff, mem_singleton_iff, Fin.exists_fin_succ]
    simp [eq_comm]
  rw [stdTetra, AffineMap.image_convexHull, solid, hr]
  congr 1
  simp only [image_insert_eq, image_singleton, edgeMap_apply]
  simp

lemma map_edgeMap_volume (hv : AffineIndependent ℝ v) :
    Measure.map (edgeMap v) (volume : Measure (Space 3)) =
      ENNReal.ofReal |(LinearMap.det (edgeLin v : Space 3 →ₗ[ℝ] Space 3))⁻¹| • volume := by
  have hf : (edgeMap v : Space 3 → E) = (· + v 0) ∘ edgeLin v := by
    funext x; simp [edgeMap]
  rw [hf, ← Measure.map_map (measurable_add_const _)
    (edgeLin v).continuous_of_finiteDimensional.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume (det_edgeLin_ne_zero hv),
    Measure.map_smul, (measurePreserving_add_right volume (v 0)).map_eq]
  exact (measurable_add_const _).aemeasurable

/-- **`B` of a tetrahedron is the mean of its four vertices.** -/
theorem volCentroid_solid (hv : AffineIndependent ℝ v) :
    volCentroid (solid v) = (1 / 4 : ℝ) • ∑ i, v i := by
  obtain ⟨_, hμ, hint⟩ := stdTetra_measure
  have hA := (edgeMap v).continuous_of_finiteDimensional
  have hK : IsClosed (solid v) := ((finite_range v).isCompact_convexHull (𝕜 := ℝ)).isClosed
  set c := ENNReal.ofReal |(LinearMap.det (edgeLin v : Space 3 →ₗ[ℝ] Space 3))⁻¹|
  have hc0 : c ≠ 0 :=
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (det_edgeLin_ne_zero hv)))).ne'
  have hmap : (volume.restrict stdTetra).map (edgeMap v) = c • volume.restrict (solid v) := by
    rw [← Measure.restrict_smul, ← map_edgeMap_volume hv,
      Measure.restrict_map hA.measurable hK.measurableSet, ← edgeMap_image,
      preimage_image_eq _ (edgeMap_injective hv)]
  have h := centroid_map _ hμ hint (edgeMap v)
  rw [hmap, centroid_smul _ hc0 ENNReal.ofReal_ne_top, centroid_stdTetra, edgeMap_apply] at h
  rw [volCentroid, h, Fin.sum_univ_four]
  simp only [pt3_zero, pt3_one, pt3_two]
  module

end Tetrahedron

end SymmetricCentroids

/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import Mathlib

/-!
# Symmetric centroids

If the symmetries of a solid `K ⊆ ℝ³` leave a single point fixed, the centroid `S`
of its surface and the centroid `B` of its volume coincide at that point.

Every symmetry maps the solid onto itself, so it maps `S` to `S` and `B` to `B`; `S` and `B`
are therefore fixed by every symmetry, and only one point is. All the analysis lives in
`centroid_fixed`: an affine isometry that preserves a finite measure fixes its centroid.

The same proof gives more (`centroids_mem_fixedSet`): `S` and `B` always lie in the set of
points fixed by every symmetry, so they can only part within it, along the axis of a solid of
revolution, or within the plane of a mirror (`centroids_mem_of_reflection`). No condition on the
symmetries alone is necessary: the closed cone whose slant height is three times its radius has
`S = B`. The only exact criterion is the trivial one, `surfCentroid_eq_volCentroid_iff`.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace SymmetricCentroids

/-- Euclidean space ℝ³. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The centroid of a measure: `(∫ x dμ) / μ(E)`. -/
def centroid (μ : Measure E) : E := (μ Set.univ).toReal⁻¹ • ∫ x, x ∂μ

/-- `B`, the centroid of the volume of `K`. -/
def volCentroid (K : Set E) : E := centroid (volume.restrict K)

/-- `S`, the centroid of the skin `∂K`, weighted by area
(the 2-dimensional Hausdorff measure, normalised to agree with area). -/
def surfCentroid (K : Set E) : E := centroid ((μHE[2] : Measure E).restrict (frontier K))

/-- A symmetry of `K`: an isometry of space that maps `K` onto itself. -/
def IsSymmetry (K : Set E) (g : E ≃ᵃⁱ[ℝ] E) : Prop := g '' K = K

/-- An affine isometry is its linear part plus a translation. -/
lemma apply_eq (g : E ≃ᵃⁱ[ℝ] E) (x : E) : g x = g.linearIsometryEquiv x + g 0 := by
  have h := g.map_vadd 0 x
  simp only [vadd_eq_add, add_zero] at h
  exact h

/-- Key lemma: an affine isometry that preserves a finite, nonzero measure with a first
moment fixes the centroid of that measure. -/
theorem centroid_fixed (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hint : Integrable (fun x : E => x) μ) (g : E ≃ᵃⁱ[ℝ] E) (hg : μ.map g = μ) :
    g (centroid μ) = centroid μ := by
  set m := (μ Set.univ).toReal with hm_def
  have hm : m ≠ 0 := by
    rw [hm_def, ENNReal.toReal_ne_zero]
    exact ⟨Measure.measure_univ_ne_zero.2 hμ, measure_ne_top μ _⟩
  set L := g.linearIsometryEquiv
  -- The first moment `I = ∫ x dμ` satisfies `I = L I + m • g 0`.
  have hI : ∫ x, x ∂μ = L (∫ x, x ∂μ) + m • g 0 := by
    calc ∫ x, x ∂μ = ∫ x, x ∂(μ.map g) := by rw [hg]
      _ = ∫ x, g x ∂μ :=
          integral_map g.continuous.aemeasurable continuous_id.aestronglyMeasurable
      _ = ∫ x, (L x + g 0) ∂μ := integral_congr_ae (Filter.Eventually.of_forall (apply_eq g))
      _ = ∫ x, L x ∂μ + ∫ _, g 0 ∂μ :=
          integral_add (L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hint)
            (integrable_const _)
      _ = L (∫ x, x ∂μ) + m • g 0 := by
          rw [show ∫ x, L x ∂μ = L (∫ x, x ∂μ) from
            L.toLinearIsometry.integral_comp_comm (fun x => x), integral_const]; rfl
  unfold centroid
  rw [apply_eq g, map_smul]
  conv_rhs => rw [hI]
  rw [smul_add, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- An affine isometry of ℝ³ preserves volume. -/
lemma measurePreserving_volume (g : E ≃ᵃⁱ[ℝ] E) : MeasurePreserving g volume volume := by
  have h : (g : E → E) = (· + g 0) ∘ g.linearIsometryEquiv := funext (apply_eq g)
  rw [h]
  exact (measurePreserving_add_right volume (g 0)).comp
    g.linearIsometryEquiv.measurePreserving

/-- A measure-preserving isometry that maps `s` onto itself preserves `μ` restricted to `s`. -/
lemma map_restrict (μ : Measure E) (g : E ≃ᵃⁱ[ℝ] E) (hp : MeasurePreserving g μ μ)
    {s : Set E} (hs : g '' s = s) : (μ.restrict s).map g = μ.restrict s := by
  have := hp.restrict_image_emb g.toHomeomorph.measurableEmbedding s
  rw [hs] at this
  exact this.map_eq

/-- The centroid of `μ` restricted to a compact set of finite, nonzero measure is fixed by
every measure-preserving isometry that maps the set onto itself. -/
lemma centroid_restrict_fixed (μ : Measure E) {s : Set E} (hs : IsCompact s)
    (h₀ : μ s ≠ 0) (hfin : μ s ≠ ⊤) (g : E ≃ᵃⁱ[ℝ] E) (hp : MeasurePreserving g μ μ)
    (hgs : g '' s = s) : g (centroid (μ.restrict s)) = centroid (μ.restrict s) := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨C, hC⟩ := hs.isBounded.exists_norm_le
  refine centroid_fixed _ ?_ ?_ g (map_restrict μ g hp hgs)
  · rwa [Ne, Measure.restrict_eq_zero]
  · exact Measure.integrableOn_of_bounded hfin continuous_id.aestronglyMeasurable
      ((ae_restrict_iff' hs.isClosed.measurableSet).2 (Filter.Eventually.of_forall hC))

/-- Every symmetry of a compact solid of nonzero volume fixes `B`. -/
lemma volCentroid_fixed {K : Set E} (hK : IsCompact K) (hV : volume K ≠ 0)
    {g : E ≃ᵃⁱ[ℝ] E} (hg : IsSymmetry K g) : g (volCentroid K) = volCentroid K :=
  centroid_restrict_fixed volume hK hV hK.measure_lt_top.ne g (measurePreserving_volume g) hg

/-- Every symmetry of a compact solid whose skin has finite, nonzero area fixes `S`. -/
lemma surfCentroid_fixed {K : Set E} (hK : IsCompact K)
    (hA₀ : μHE[2] (frontier K) ≠ 0) (hA : μHE[2] (frontier K) ≠ ⊤)
    {g : E ≃ᵃⁱ[ℝ] E} (hg : IsSymmetry K g) : g (surfCentroid K) = surfCentroid K := by
  have hfr : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans hK.isClosed.closure_subset)
  have hgK : g '' frontier K = frontier K := by
    rw [show (g : E → E) = g.toHomeomorph from rfl, g.toHomeomorph.image_frontier]
    exact congrArg frontier hg
  exact centroid_restrict_fixed μHE[2] hfr hA₀ hA g
    (g.coe_toIsometryEquiv ▸ g.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure 2) hgK

/-- The points fixed by every symmetry of `K`. -/
def fixedSet (K : Set E) : Set E := {x | ∀ g, IsSymmetry K g → g x = x}

/-- **Generalisation.** `S` and `B` both lie in the set of points fixed by every symmetry
of `K`. On a solid of revolution that set is the axis; on a hull with one plane of symmetry it
is that plane; on a solid with no symmetry it is the whole space. -/
theorem centroids_mem_fixedSet (K : Set E) (hK : IsCompact K) (hV : volume K ≠ 0)
    (hA₀ : μHE[2] (frontier K) ≠ 0) (hA : μHE[2] (frontier K) ≠ ⊤) :
    surfCentroid K ∈ fixedSet K ∧ volCentroid K ∈ fixedSet K :=
  ⟨fun _ hg => surfCentroid_fixed hK hA₀ hA hg, fun _ hg => volCentroid_fixed hK hV hg⟩

/-- **Symmetric centroids.** If the symmetries of a solid `K` fix at most one point `c`,
then its surface centroid `S` and its volume centroid `B` are both `c`. -/
theorem centroids_eq_of_unique_fixed_point (K : Set E) (hK : IsCompact K) (hV : volume K ≠ 0)
    (hA₀ : μHE[2] (frontier K) ≠ 0) (hA : μHE[2] (frontier K) ≠ ⊤)
    (c : E) (huniq : ∀ x ∈ fixedSet K, x = c) :
    surfCentroid K = c ∧ volCentroid K = c :=
  have h := centroids_mem_fixedSet K hK hV hA₀ hA
  ⟨huniq _ h.1, huniq _ h.2⟩

/-- **Mirror.** If the reflection in an affine subspace `P` (a plane, a line, a point) maps `K`
onto itself, `S` and `B` both lie in `P`. A hull symmetric port and starboard has `S` and `B` in
its plane of symmetry, so `S - B` has no athwartships component. -/
theorem centroids_mem_of_reflection (K : Set E) (hK : IsCompact K) (hV : volume K ≠ 0)
    (hA₀ : μHE[2] (frontier K) ≠ 0) (hA : μHE[2] (frontier K) ≠ ⊤)
    (P : AffineSubspace ℝ E) [Nonempty P] (hP : IsSymmetry K (EuclideanGeometry.reflection P)) :
    surfCentroid K ∈ P ∧ volCentroid K ∈ P := by
  have h := centroids_mem_fixedSet K hK hV hA₀ hA
  exact ⟨(EuclideanGeometry.reflection_eq_self_iff _).1 (h.1 _ hP),
    (EuclideanGeometry.reflection_eq_self_iff _).1 (h.2 _ hP)⟩

/-- A finite, nonzero measure has its centroid at `c` exactly when its first moment about `c`
is zero. -/
lemma centroid_eq_iff (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hint : Integrable (fun x : E => x) μ) (c : E) :
    centroid μ = c ↔ ∫ x, (x - c) ∂μ = 0 := by
  have hm : (μ Set.univ).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨Measure.measure_univ_ne_zero.2 hμ, measure_ne_top μ _⟩
  rw [integral_sub hint (integrable_const c), integral_const, sub_eq_zero, centroid,
    inv_smul_eq_iff₀ hm]
  rfl

/-- **The trivial criterion.** `S = B` exactly when the first moment of the skin about `B` is
zero: `∫_∂K (x - B) dA = 0`. True, and no more than the definition of `S`. -/
theorem surfCentroid_eq_volCentroid_iff (K : Set E) (hK : IsCompact K)
    (hA₀ : μHE[2] (frontier K) ≠ 0) (hA : μHE[2] (frontier K) ≠ ⊤) :
    surfCentroid K = volCentroid K ↔
      ∫ x in frontier K, (x - volCentroid K) ∂(μHE[2] : Measure E) = 0 := by
  have hfr : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans hK.isClosed.closure_subset)
  have : IsFiniteMeasure ((μHE[2] : Measure E).restrict (frontier K)) :=
    isFiniteMeasure_restrict.2 hA
  obtain ⟨C, hC⟩ := hfr.isBounded.exists_norm_le
  refine centroid_eq_iff _ ?_ ?_ _
  · rwa [Ne, Measure.restrict_eq_zero]
  · exact Measure.integrableOn_of_bounded hA continuous_id.aestronglyMeasurable
      ((ae_restrict_iff' hfr.isClosed.measurableSet).2 (Filter.Eventually.of_forall hC))

end SymmetricCentroids

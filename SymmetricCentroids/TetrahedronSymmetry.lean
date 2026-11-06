/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.TetrahedronTrueCentroids

/-!
# Tetrahedra: `S = B` exactly when the symmetries fix a single point

On a tetrahedron, the converse of the main theorem holds. If `S = B`, the tetrahedron is a
disphenoid, and the half turn about each bimedian, the line through the midpoints of two opposite
edges, swaps the ends of both edges: in a disphenoid the bimedian is perpendicular to the two edges
it joins. Two of these half turns already fix nothing but the centre of the tetrahedron. The
other way is the main theorem.
-/

open MeasureTheory EuclideanGeometry

@[expose] public noncomputable section

namespace SymmetricCentroids.Tetrahedron

variable {v : Fin 4 → E}

/-! ### The solid satisfies the hypotheses of the main theorem -/

lemma isCompact_solid : IsCompact (solid v) :=
  (Set.toFinite _).isCompact_convexHull (𝕜 := ℝ)

lemma volume_solid_ne_zero (hv : AffineIndependent ℝ v) : volume (solid v) ≠ 0 := by
  intro h0
  have hm := congrArg (fun μ : Measure E => μ (solid v)) (map_edgeMap_volume hv)
  simp only [Measure.smul_apply, smul_eq_mul, h0, mul_zero] at hm
  rw [Measure.map_apply (edgeMap v).continuous_of_finiteDimensional.measurable
    isCompact_solid.isClosed.measurableSet, ← edgeMap_image,
    Set.preimage_image_eq _ (edgeMap_injective hv)] at hm
  exact volume_stdTetra_ne_zero hm

lemma hausdorff_frontier_ne_top (hv : AffineIndependent ℝ v) :
    (μHE[2] : Measure E) (frontier (solid v)) ≠ ⊤ := by
  rw [frontier_eq_iUnion_face hv]
  exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => hausdorff_face_ne_top hv i)
    (measure_iUnion_fintype_le _ _)

lemma hausdorff_frontier_ne_zero (hv : AffineIndependent ℝ v) :
    (μHE[2] : Measure E) (frontier (solid v)) ≠ 0 := by
  have hK : 0 < (volume stdTriangle).toReal :=
    ENNReal.toReal_pos volume_stdTriangle_ne_zero isCompact_stdTriangle.measure_lt_top.ne
  have h0 : 0 < ((μHE[2] : Measure E) (face v 0)).toReal := by
    rw [hausdorff_face hv]; exact mul_pos (by positivity) (faceArea_pos hv 0)
  refine fun hz => (ENNReal.toReal_pos_iff.1 h0).1.ne' (measure_mono_null ?_ hz)
  rw [frontier_eq_iUnion_face hv]
  exact Set.subset_iUnion (face v) 0

/-! ### The half turns of a disphenoid -/

/-- The half turn about the line through `m` and `m'`: Mathlib's reflection in that line. -/
def lineTurn (m m' : E) : E ≃ᵃⁱ[ℝ] E :=
  haveI : Nonempty (line[ℝ, m, m']) := ⟨⟨m, left_mem_affineSpan_pair ℝ m m'⟩⟩
  EuclideanGeometry.reflection line[ℝ, m, m']

lemma lineTurn_eq_self_iff (m m' x : E) : lineTurn m m' x = x ↔ x ∈ line[ℝ, m, m'] := by
  have : Nonempty (line[ℝ, m, m']) := ⟨⟨m, left_mem_affineSpan_pair ℝ m m'⟩⟩
  exact EuclideanGeometry.reflection_eq_self_iff x

lemma lineTurn_lineTurn (m m' x : E) : lineTurn m m' (lineTurn m m' x) = x := by
  have : Nonempty (line[ℝ, m, m']) := ⟨⟨m, left_mem_affineSpan_pair ℝ m m'⟩⟩
  exact EuclideanGeometry.reflection_reflection _ x

/-- If `a - b` is perpendicular to the line through `m = (a + b)/2` and `m'`, the half turn about
that line maps `a` to `b`. -/
lemma lineTurn_midpoint (a b m' : E) (h : inner ℝ (midpoint ℝ a b - m') (a - b) = 0) :
    lineTurn (midpoint ℝ a b) m' a = b := by
  set m := midpoint ℝ a b
  have : Nonempty (line[ℝ, m, m']) := ⟨⟨m, left_mem_affineSpan_pair ℝ m m'⟩⟩
  have hperp : a - m ∈ (line[ℝ, m, m']).directionᗮ := by
    rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have : a - m = (2 : ℝ)⁻¹ • (a - b) := by
      simp only [m, midpoint_eq_smul_add, invOf_eq_inv]; module
    rw [this, inner_smul_right, vsub_eq_sub, h, mul_zero]
  unfold lineTurn
  rw [EuclideanGeometry.reflection_apply_of_mem _ _ (left_mem_affineSpan_pair ℝ m m'),
    vsub_eq_sub, Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hperp, vadd_eq_add]
  simp only [m, midpoint_eq_smul_add, invOf_eq_inv]; module

/-- The same, with the midpoint as the second point of the line. -/
lemma lineTurn_midpoint' (c d m : E) (h : inner ℝ (midpoint ℝ c d - m) (c - d) = 0) :
    lineTurn m (midpoint ℝ c d) c = d := by
  set m' := midpoint ℝ c d
  have : Nonempty (line[ℝ, m, m']) := ⟨⟨m, left_mem_affineSpan_pair ℝ m m'⟩⟩
  have hperp : c - m' ∈ (line[ℝ, m, m']).directionᗮ := by
    rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have : c - m' = (2 : ℝ)⁻¹ • (c - d) := by
      simp only [m', midpoint_eq_smul_add, invOf_eq_inv]; module
    rw [this, inner_smul_right, vsub_eq_sub, show m - m' = -(m' - m) by abel, inner_neg_left, h,
      neg_zero, mul_zero]
  unfold lineTurn
  rw [EuclideanGeometry.reflection_apply_of_mem _ _ (right_mem_affineSpan_pair ℝ m m'),
    vsub_eq_sub, Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hperp, vadd_eq_add]
  simp only [m', midpoint_eq_smul_add, invOf_eq_inv]; module

/-- In a tetrahedron whose opposite edges `ac, bd` and `ad, bc` are equal, the bimedian through the
midpoints of `ab` and `cd` is perpendicular to `ab`. -/
lemma bimedian_perp (a b c d : E) (h₁ : dist a c = dist b d) (h₂ : dist a d = dist b c) :
    inner ℝ (midpoint ℝ a b - midpoint ℝ c d) (a - b) = 0 := by
  have e₁ := congrArg (· ^ 2) h₁
  have e₂ := congrArg (· ^ 2) h₂
  simp only [dist_sq] at e₁ e₂
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [midpoint_eq_smul_add, invOf_eq_inv, dotProduct, Fin.sum_univ_three, star_trivial,
    WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at e₁ e₂ ⊢
  linear_combination (e₁ + e₂) / 4

/-- A permutation of the vertices by an isometry is a symmetry of the solid. -/
lemma isSymmetry_of_perm (g : E ≃ᵃⁱ[ℝ] E) (σ : Equiv.Perm (Fin 4)) (h : ∀ i, g (v i) = v (σ i)) :
    IsSymmetry (solid v) g := by
  have himg : g '' Set.range v = Set.range v := by
    ext x; constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨σ i, (h i).symm⟩
    · rintro ⟨j, rfl⟩; exact ⟨v (σ.symm j), ⟨σ.symm j, rfl⟩, by rw [h, Equiv.apply_symm_apply]⟩
  unfold IsSymmetry solid
  have := (g.toAffineEquiv.toAffineMap).image_convexHull (Set.range v)
  simpa [himg] using this

/-- Two bimedians of a tetrahedron meet only at its centre. -/
lemma eq_centre_of_mem_bimedians (hv : AffineIndependent ℝ v) {x : E}
    (h₁ : x ∈ line[ℝ, midpoint ℝ (v 0) (v 1), midpoint ℝ (v 2) (v 3)])
    (h₂ : x ∈ line[ℝ, midpoint ℝ (v 0) (v 2), midpoint ℝ (v 1) (v 3)]) :
    x = (4 : ℝ)⁻¹ • ∑ i, v i := by
  obtain ⟨s, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h₁
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 h₂
  simp only [AffineMap.lineMap_apply_module, midpoint_eq_smul_add, invOf_eq_inv] at ht ⊢
  set w : Fin 4 → ℝ := ![(t - s) / 2, (1 - s - t) / 2, (s - 1 + t) / 2, (s - t) / 2]
  have hw : ∑ i, w i = 0 := by
    rw [Fin.sum_univ_four]
    change (t - s) / 2 + (1 - s - t) / 2 + (s - 1 + t) / 2 + (s - t) / 2 = 0
    ring
  have hsum : ∑ i, w i • v i = 0 := by
    rw [Fin.sum_univ_four]
    change ((t - s) / 2) • v 0 + ((1 - s - t) / 2) • v 1 + ((s - 1 + t) / 2) • v 2 +
      ((s - t) / 2) • v 3 = 0
    linear_combination (norm := module) -ht
  have hzero := (affineIndependent_iff_of_fintype ℝ v).1 hv w hw (by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
      Finset.weightedVSubOfPoint_apply]
    simpa using hsum)
  have h0 : (t - s) / 2 = 0 := hzero 0
  have h1 : (1 - s - t) / 2 = 0 := hzero 1
  have hs : s = 1 / 2 := by linarith
  rw [hs, Fin.sum_univ_four]
  norm_num
  module

/-- **On a tetrahedron, `S = B` exactly when the symmetries fix a single point**: the converse
of the main theorem holds for tetrahedra. -/
theorem surfCentroid_eq_volCentroid_iff_unique_fixed_point (hv : AffineIndependent ℝ v) :
    surfCentroid (solid v) = volCentroid (solid v) ↔ ∃ c, ∀ x ∈ fixedSet (solid v), x = c := by
  constructor
  · intro h
    obtain ⟨d₁, d₂, d₃⟩ := (surfCentroid_eq_volCentroid_iff_disphenoid hv).1 h
    refine ⟨(4 : ℝ)⁻¹ • ∑ i, v i, fun x hx => eq_centre_of_mem_bimedians hv ?_ ?_⟩
    · -- The half turn about the bimedian of `v0 v1` and `v2 v3` swaps `v0, v1` and `v2, v3`.
      have g0 : lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)) (v 0) = v 1 :=
        lineTurn_midpoint _ _ _ (bimedian_perp _ _ _ _ d₂ d₃)
      have g2 : lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)) (v 2) = v 3 :=
        lineTurn_midpoint' _ _ _ (bimedian_perp _ _ _ _
          (by rw [dist_comm (v 2), dist_comm (v 3)]; exact d₂)
          (by rw [dist_comm (v 2), dist_comm (v 3)]; exact d₃.symm))
      have g1 : lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)) (v 1) = v 0 := by
        have := lineTurn_lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)) (v 0)
        rwa [g0] at this
      have g3 : lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)) (v 3) = v 2 := by
        have := lineTurn_lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)) (v 2)
        rwa [g2] at this
      have hg := isSymmetry_of_perm (v := v)
        (lineTurn (midpoint ℝ (v 0) (v 1)) (midpoint ℝ (v 2) (v 3)))
        (Equiv.swap 0 1 * Equiv.swap 2 3) fun i => by
        fin_cases i <;> simp [Equiv.swap_apply_def, g0, g1, g2, g3]
      exact (lineTurn_eq_self_iff _ _ x).1 (hx _ hg)
    · -- The half turn about the bimedian of `v0 v2` and `v1 v3` swaps `v0, v2` and `v1, v3`.
      have g0 : lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)) (v 0) = v 2 :=
        lineTurn_midpoint _ _ _ (bimedian_perp _ _ _ _ d₁ (d₃.trans (dist_comm _ _)))
      have g1 : lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)) (v 1) = v 3 :=
        lineTurn_midpoint' _ _ _ (bimedian_perp _ _ _ _
          (by rw [dist_comm (v 1), dist_comm (v 3)]; exact d₁)
          (by rw [dist_comm (v 3)]; exact d₃.symm))
      have g2 : lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)) (v 2) = v 0 := by
        have := lineTurn_lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)) (v 0)
        rwa [g0] at this
      have g3 : lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)) (v 3) = v 1 := by
        have := lineTurn_lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)) (v 1)
        rwa [g1] at this
      have hg := isSymmetry_of_perm (v := v)
        (lineTurn (midpoint ℝ (v 0) (v 2)) (midpoint ℝ (v 1) (v 3)))
        (Equiv.swap 0 2 * Equiv.swap 1 3) fun i => by
        fin_cases i <;> simp [Equiv.swap_apply_def, g0, g1, g2, g3]
      exact (lineTurn_eq_self_iff _ _ x).1 (hx _ hg)
  · rintro ⟨c, hc⟩
    have := centroids_eq_of_unique_fixed_point (solid v) isCompact_solid
      (volume_solid_ne_zero hv) (hausdorff_frontier_ne_zero hv) (hausdorff_frontier_ne_top hv) c hc
    rw [this.1, this.2]

end SymmetricCentroids.Tetrahedron

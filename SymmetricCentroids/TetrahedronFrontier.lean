/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids

/-!
# The skin of a solid tetrahedron

For four affinely independent points `v` of `E = ℝ³`, the solid tetrahedron is the convex hull
`K` of the points, and the face opposite the vertex `vᵢ` is the convex hull `F i` of the three
other vertices.

* `frontier_eq_iUnion_face`: the frontier of `K` is the union of its four closed faces.
* `hausdorff_face_inter_face`: two different faces meet in a set of zero area, `μHE[2]`, since
  their intersection lies on the line through the two vertices they share.

The proof of the first goes through Mathlib's simplices. A point of `K` lies in the topological
interior of `K` exactly when its four barycentric coordinates are positive
(`AffineBasis.interior_convexHull`), which is the interior of the simplex in Mathlib's sense
(`Affine.Simplex.interior`). Mathlib then shows that the closed simplex minus its interior is the
union of the closed faces (`Affine.Simplex.closedInterior_sdiff_interior`).
-/

open Set MeasureTheory Module

@[expose] public noncomputable section

namespace SymmetricCentroids.Tetrahedron

variable (v : Fin 4 → E)

/-- The solid tetrahedron: the convex hull of the four vertices. -/
def solid : Set E := convexHull ℝ (range v)

/-- The closed face opposite the vertex `vᵢ`: the convex hull of the three other vertices. -/
def face (i : Fin 4) : Set E := convexHull ℝ (v '' {j | j ≠ i})

variable {v}

/-- Four affinely independent points of `ℝ³` form an affine basis. -/
def affineBasis (hv : AffineIndependent ℝ v) : AffineBasis (Fin 4) ℝ E :=
  ⟨v, hv, hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by simp)⟩

/-- The same four points as a Mathlib simplex. -/
def simplex (hv : AffineIndependent ℝ v) : Affine.Simplex ℝ E 3 := ⟨v, hv⟩

lemma solid_eq_closedInterior (hv : AffineIndependent ℝ v) :
    solid v = (simplex hv).closedInterior :=
  Affine.Simplex.convexHull_eq_closedInterior (simplex hv)

lemma face_eq_closedInterior (hv : AffineIndependent ℝ v) (i : Fin 4) :
    face v i = ((simplex hv).faceOpposite i).closedInterior := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior, Affine.Simplex.range_faceOpposite_points]
  rfl

/-- The topological interior of the solid tetrahedron is the interior of the simplex: the points
whose four barycentric coordinates lie strictly between 0 and 1. -/
lemma interior_solid (hv : AffineIndependent ℝ v) :
    interior (solid v) = (simplex hv).interior := by
  set b := affineBasis hv
  have hb : interior (solid v) = {x | ∀ i, 0 < b.coord i x} := b.interior_convexHull
  ext x
  have hx : x = Finset.univ.affineCombination ℝ (simplex hv).points fun i ↦ b.coord i x :=
    (b.affineCombination_coord_eq_self x).symm
  rw [hb]
  change (∀ i, 0 < b.coord i x) ↔ x ∈ (simplex hv).interior
  conv_rhs => rw [hx]
  rw [Affine.Simplex.affineCombination_mem_interior_iff (b.sum_coord_apply_eq_one x)]
  have hsum := b.sum_coord_apply_eq_one x
  rw [Fin.sum_univ_four] at hsum
  refine ⟨fun h i ↦ ⟨h i, ?_⟩, fun h i ↦ (h i).1⟩
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith

/-- **The skin of a solid tetrahedron is the union of its four closed faces.** -/
theorem frontier_eq_iUnion_face (hv : AffineIndependent ℝ v) :
    frontier (solid v) = ⋃ i, face v i := by
  have hclosed : IsClosed (solid v) :=
    solid_eq_closedInterior hv ▸ (simplex hv).isClosed_closedInterior
  rw [frontier, hclosed.closure_eq, interior_solid hv, solid_eq_closedInterior hv,
    Affine.Simplex.closedInterior_sdiff_interior]
  simp_rw [face_eq_closedInterior hv]

/-- A face lies in the plane where the barycentric coordinate of the opposite vertex vanishes. -/
lemma face_subset_coord_eq_zero (hv : AffineIndependent ℝ v) (i : Fin 4) :
    face v i ⊆ {x | (affineBasis hv).coord i x = 0} := by
  set b := affineBasis hv
  refine convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage (b.coord i))
  rintro _ ⟨j, hj, rfl⟩
  exact b.coord_apply_ne (Ne.symm hj)

/-- A point whose barycentric coordinates vanish except at `a` and `c` lies on the line through
`v a` and `v c`. -/
lemma mem_range_line (hv : AffineIndependent ℝ v) {a c : Fin 4} (hac : a ≠ c) {x : E}
    (hx : ∀ k, k ≠ a ∧ k ≠ c → (affineBasis hv).coord k x = 0) :
    x ∈ range fun t : ℝ ↦ v a + t • (v c - v a) := by
  set b := affineBasis hv
  have hsum : b.coord a x + b.coord c x = 1 := by
    rw [← b.sum_coord_apply_eq_one x, Fintype.sum_eq_add a c hac hx]
  have hcomb : b.coord a x • v a + b.coord c x • v c = x := by
    have h := b.linear_combination_coord_eq_self x
    rwa [Fintype.sum_eq_add a c hac fun k hk ↦ by simp [hx k hk]] at h
  refine ⟨b.coord c x, ?_⟩
  set t := b.coord c x
  rw [show b.coord a x = 1 - t by linarith] at hcomb
  rw [← hcomb]
  module

/-- Two different faces share an edge, and an edge has zero area. -/
theorem hausdorff_face_inter_face (hv : AffineIndependent ℝ v) {i j : Fin 4} (hij : i ≠ j) :
    μHE[2] (face v i ∩ face v j) = 0 := by
  obtain ⟨a, c, hac, hcover⟩ : ∃ a c : Fin 4, a ≠ c ∧ ∀ k, k ≠ a ∧ k ≠ c → k = i ∨ k = j := by
    revert i j; decide
  set f : ℝ → E := fun t ↦ v a + t • (v c - v a)
  have hsub : face v i ∩ face v j ⊆ range f := by
    rintro x ⟨hxi, hxj⟩
    refine mem_range_line hv hac fun k hk ↦ ?_
    rcases hcover k hk with rfl | rfl
    · exact face_subset_coord_eq_zero hv k hxi
    · exact face_subset_coord_eq_zero hv k hxj
  have hdim : dimH (range f) < ((2 : NNReal) : ENNReal) := by
    have hd : Differentiable ℝ f := by fun_prop
    calc dimH (range f) ≤ (finrank ℝ ℝ : ENNReal) := hd.dimH_range_le
      _ < ((2 : NNReal) : ENNReal) := by simp
  have hzero : μH[(2 : NNReal)] (range f) = 0 := hausdorffMeasure_of_dimH_lt hdim
  have h2 : μH[((2 : ℕ) : ℝ)] (range f) = 0 := by simpa using hzero
  refine measure_mono_null hsub ?_
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h2, smul_zero]

end SymmetricCentroids.Tetrahedron

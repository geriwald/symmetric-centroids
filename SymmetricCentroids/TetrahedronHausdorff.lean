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

end SymmetricCentroids.Tetrahedron

/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.PyramidVolume

/-!
# The skin of the square pyramid

The interior of the pyramid is the set of points where its five inequalities are strict: at a
point where one is an equality, a small step outwards along its normal leaves the pyramid. So the
frontier is the set of points of the pyramid where one inequality is an equality, and each of these
five pieces is a triangle, or for the base two triangles, by explicit barycentric weights.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace SymmetricCentroids.Pyramid

open Tetrahedron

/-- The points where the five inequalities are strict. -/
def pyrInt : Set E :=
  {x | 0 < x 2 ∧ x 0 + x 1 + x 2 / 2 < 1 ∧ -x 0 + x 1 + x 2 / 2 < 1 ∧
    -x 0 - x 1 + x 2 / 2 < 1 ∧ x 0 - x 1 + x 2 / 2 < 1}

lemma isOpen_pyrInt : IsOpen pyrInt := by
  have c : ∀ i : Fin 3, Continuous fun x : E => x i := fun i => (EuclideanSpace.proj i).continuous
  have z := (c 2).div_const 2
  exact (isOpen_lt continuous_const (c 2)).inter
    ((isOpen_lt (((c 0).add (c 1)).add z) continuous_const).inter
    ((isOpen_lt (((c 0).neg.add (c 1)).add z) continuous_const).inter
    ((isOpen_lt (((c 0).neg.sub (c 1)).add z) continuous_const).inter
    (isOpen_lt (((c 0).sub (c 1)).add z) continuous_const))))

lemma norm_pt3_lt {a b c ε : ℝ} (hε : 0 < ε) (h : a ^ 2 + b ^ 2 + c ^ 2 < ε ^ 2) :
    ‖pt3 a b c‖ < ε := by
  refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
  rw [show pt3 a b c = WithLp.toLp 2 ![a, b, c] from rfl, norm_sq_toLp]
  simpa [dotProduct, Fin.sum_univ_three, sq] using h

lemma interior_pyr : interior pyr = pyrInt := by
  refine subset_antisymm (fun x hx => ?_)
    (interior_maximal (fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.1.le,
      hx.2.2.2.2.le⟩) isOpen_pyrInt)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hb : ∀ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 < ε ^ 2 → x + pt3 a b c ∈ pyr := fun a b c h =>
    interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact norm_pt3_lt hε h))
  set t := ε / 4
  have ht : 0 < t := by positivity
  have h1 : 2 * t ^ 2 < ε ^ 2 := by simp only [t]; nlinarith
  have k0 := (hb 0 0 (-t) (by nlinarith)).1
  have k1 := (hb t t 0 (by nlinarith)).2.1
  have k2 := (hb (-t) t 0 (by nlinarith)).2.2.1
  have k3 := (hb (-t) (-t) 0 (by nlinarith)).2.2.2.1
  have k4 := (hb t (-t) 0 (by nlinarith)).2.2.2.2
  simp only [PiLp.add_apply, pt3_zero, pt3_one, pt3_two] at k0 k1 k2 k3 k4
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma frontier_pyr_eq_diff : frontier pyr = pyr \ pyrInt := by
  rw [frontier, isClosed_pyr.closure_eq, interior_pyr]

/-! ### The six triangles -/

lemma mem_triangle (a b c : E) {w₀ w₁ w₂ : ℝ} (h₀ : 0 ≤ w₀) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂)
    (h : w₀ + w₁ + w₂ = 1) : w₀ • a + w₁ • b + w₂ • c ∈ convexHull ℝ {a, b, c} := by
  have := (convex_convexHull ℝ ({a, b, c} : Set E)).sum_mem (t := Finset.univ)
    (w := ![w₀, w₁, w₂]) (z := ![a, b, c]) (fun i _ => by fin_cases i <;> simpa)
    (by simp [Fin.sum_univ_three, h])
    (fun i _ => subset_convexHull ℝ _ (by fin_cases i <;> simp))
  simpa [Fin.sum_univ_three] using this

/-- A point of the pyramid where one inequality is an equality lies on one of the six triangles. -/
lemma mem_faces_of_tight {x : E} (hx : x ∈ pyr) (ht : x ∉ pyrInt) :
    x ∈ lat0 ∪ lat1 ∪ lat2 ∪ lat3 ∪ baseA ∪ baseB := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  simp only [pyrInt, Set.mem_ofPred_eq, not_and_or, not_lt] at ht
  rcases ht with ht | ht | ht | ht | ht
  · rcases le_total 0 (x 1) with hy | hy
    · refine Or.inl (Or.inr ?_)
      have := mem_triangle b0 b1 b2 (w₀ := (1 - x 1 + x 0) / 2) (w₁ := x 1)
        (w₂ := (1 - x 1 - x 0) / 2) (by linarith) hy (by linarith) (by ring)
      unfold baseA; convert this using 2; ext i; fin_cases i <;> simp [b0, b1, b2] <;> linarith
    · refine Or.inr ?_
      have := mem_triangle b0 b2 b3 (w₀ := (1 + x 1 + x 0) / 2) (w₁ := (1 + x 1 - x 0) / 2)
        (w₂ := -x 1) (by linarith) (by linarith) (by linarith) (by ring)
      unfold baseB; convert this using 2; ext i; fin_cases i <;> simp [b0, b2, b3] <;> linarith
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))
    have := mem_triangle b0 b1 apex (w₀ := x 0) (w₁ := x 1) (w₂ := x 2 / 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
    unfold lat0; convert this using 2; ext i; fin_cases i <;> simp [b0, b1, apex]
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
    have := mem_triangle b1 b2 apex (w₀ := x 1) (w₁ := -x 0) (w₂ := x 2 / 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
    unfold lat1; convert this using 2; ext i; fin_cases i <;> simp [b1, b2, apex]
  · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
    have := mem_triangle b2 b3 apex (w₀ := -x 0) (w₁ := -x 1) (w₂ := x 2 / 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
    unfold lat2; convert this using 2; ext i; fin_cases i <;> simp [b2, b3, apex]
  · refine Or.inl (Or.inl (Or.inr ?_))
    have := mem_triangle b3 b0 apex (w₀ := -x 1) (w₁ := x 0) (w₂ := x 2 / 2)
      (by linarith) (by linarith) (by linarith) (by linarith)
    unfold lat3; convert this using 2; ext i; fin_cases i <;> simp [b3, b0, apex]

/-! ### The planes of the faces, and where two faces meet -/

/-- The plane `α x + β y + γ z = c`. -/
def plane (α β γ c : ℝ) : Set E := {x | α * x 0 + β * x 1 + γ * x 2 = c}

lemma convex_plane (α β γ c : ℝ) : Convex ℝ (plane α β γ c) := by
  intro x hx y hy a b _ _ hab
  simp only [plane, Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  linear_combination a * hx + b * hy + c * hab

/-- A line has zero area. -/
lemma hausdorff_line (p d : E) : (μHE[2] : Measure E) (Set.range fun t : ℝ => p + t • d) = 0 := by
  set f : ℝ → E := fun t ↦ p + t • d
  have hdim : dimH (Set.range f) < ((2 : NNReal) : ENNReal) := by
    have hd : Differentiable ℝ f := by fun_prop
    calc dimH (Set.range f) ≤ (Module.finrank ℝ ℝ : ENNReal) := hd.dimH_range_le
      _ < ((2 : NNReal) : ENNReal) := by simp
  have hzero : μH[(2 : NNReal)] (Set.range f) = 0 := hausdorffMeasure_of_dimH_lt hdim
  have h2 : μH[((2 : ℕ) : ℝ)] (Set.range f) = 0 := by simpa using hzero
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h2, smul_zero]

/-- The plane of face `0`. -/
abbrev pz : Set E := plane 0 0 (1) 0

/-- The plane of face `1`. -/
abbrev p1 : Set E := plane 1 1 (1 / 2) 1

/-- The plane of face `2`. -/
abbrev p2 : Set E := plane (-1) 1 (1 / 2) 1

/-- The plane of face `3`. -/
abbrev p3 : Set E := plane (-1) (-1) (1 / 2) 1

/-- The plane of face `4`. -/
abbrev p4 : Set E := plane 1 (-1) (1 / 2) 1

lemma null_pz_p1 : (μHE[2] : Measure E) (pz ∩ p1) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 1 0) (pt3 1 (-1) 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [pz, p1, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_pz_p2 : (μHE[2] : Measure E) (pz ∩ p2) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 1 0) (pt3 1 1 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [pz, p2, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_pz_p3 : (μHE[2] : Measure E) (pz ∩ p3) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 (-1) 0) (pt3 1 (-1) 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [pz, p3, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_pz_p4 : (μHE[2] : Measure E) (pz ∩ p4) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 (-1) 0) (pt3 1 1 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [pz, p4, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_p1_p2 : (μHE[2] : Measure E) (p1 ∩ p2) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 1 0) (pt3 0 (-1 / 2) 1))
  obtain ⟨h1, h2⟩ := hx
  simp only [p1, p2, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 2, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_p1_p3 : (μHE[2] : Measure E) (p1 ∩ p3) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 0 2) (pt3 1 (-1) 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [p1, p3, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_p1_p4 : (μHE[2] : Measure E) (p1 ∩ p4) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 1 0 0) (pt3 (-1 / 2) 0 1))
  obtain ⟨h1, h2⟩ := hx
  simp only [p1, p4, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 2, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_p2_p3 : (μHE[2] : Measure E) (p2 ∩ p3) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 (-1) 0 0) (pt3 (1 / 2) 0 1))
  obtain ⟨h1, h2⟩ := hx
  simp only [p2, p3, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 2, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_p2_p4 : (μHE[2] : Measure E) (p2 ∩ p4) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 0 2) (pt3 1 1 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [p2, p4, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_p3_p4 : (μHE[2] : Measure E) (p3 ∩ p4) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line (pt3 0 (-1) 0) (pt3 (0) (1 / 2) 1))
  obtain ⟨h1, h2⟩ := hx
  simp only [p3, p4, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 2, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

lemma null_base : (μHE[2] : Measure E) (pz ∩ {x : E | x 1 = 0}) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (hausdorff_line 0 (pt3 1 0 0))
  obtain ⟨h1, h2⟩ := hx
  simp only [pz, plane, Set.mem_ofPred_eq] at h1 h2
  refine ⟨x 0, ?_⟩
  ext k; fin_cases k <;> simp <;> linarith

/-! ### The six faces -/

lemma lat0_sub : lat0 ⊆ pyr ∩ p1 :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_inter_iff, mem_pyr]
    simp [b0, b1, apex, p1, plane]) (convex_pyr.inter (convex_plane _ _ _ _))

lemma lat1_sub : lat1 ⊆ pyr ∩ p2 :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_inter_iff, mem_pyr]
    simp [b1, b2, apex, p2, plane]) (convex_pyr.inter (convex_plane _ _ _ _))

lemma lat2_sub : lat2 ⊆ pyr ∩ p3 :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_inter_iff, mem_pyr]
    simp [b2, b3, apex, p3, plane]) (convex_pyr.inter (convex_plane _ _ _ _))

lemma lat3_sub : lat3 ⊆ pyr ∩ p4 :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_inter_iff, mem_pyr]
    simp [b3, b0, apex, p4, plane]) (convex_pyr.inter (convex_plane _ _ _ _))

lemma baseA_sub : baseA ⊆ pyr ∩ pz :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_inter_iff, mem_pyr]
    simp [b0, b1, b2, pz, plane]) (convex_pyr.inter (convex_plane _ _ _ _))

lemma baseB_sub : baseB ⊆ pyr ∩ pz :=
  convexHull_min (by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_inter_iff, mem_pyr]
    simp [b0, b2, b3, pz, plane]) (convex_pyr.inter (convex_plane _ _ _ _))

lemma baseA_sub_y : baseA ⊆ {x : E | 0 ≤ x 1} :=
  convexHull_min (by simp [Set.insert_subset_iff, b0, b1, b2])
    (convex_halfSpace_ge (EuclideanSpace.proj (1 : Fin 3)).isLinear 0)

lemma baseB_sub_y : baseB ⊆ {x : E | x 1 ≤ 0} :=
  convexHull_min (by simp [Set.insert_subset_iff, b0, b2, b3])
    (convex_halfSpace_le (EuclideanSpace.proj (1 : Fin 3)).isLinear 0)

/-- The six faces: four lateral triangles and the two halves of the base. -/
def face6 : Fin 6 → Set E := ![lat0, lat1, lat2, lat3, baseA, baseB]

/-- **Two faces meet in a set of zero area.** -/
theorem hausdorff_face6_inter {i j : Fin 6} (hij : i ≠ j) :
    (μHE[2] : Measure E) (face6 i ∩ face6 j) = 0 := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine measure_mono_null ?_ null_p1_p2
    exact fun x hx => ⟨(lat0_sub hx.1).2, (lat1_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_p1_p3
    exact fun x hx => ⟨(lat0_sub hx.1).2, (lat2_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_p1_p4
    exact fun x hx => ⟨(lat0_sub hx.1).2, (lat3_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p1
    exact fun x hx => ⟨(baseA_sub hx.2).2, (lat0_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_pz_p1
    exact fun x hx => ⟨(baseB_sub hx.2).2, (lat0_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_p1_p2
    exact fun x hx => ⟨(lat0_sub hx.2).2, (lat1_sub hx.1).2⟩
  · exact absurd rfl hij
  · refine measure_mono_null ?_ null_p2_p3
    exact fun x hx => ⟨(lat1_sub hx.1).2, (lat2_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_p2_p4
    exact fun x hx => ⟨(lat1_sub hx.1).2, (lat3_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p2
    exact fun x hx => ⟨(baseA_sub hx.2).2, (lat1_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_pz_p2
    exact fun x hx => ⟨(baseB_sub hx.2).2, (lat1_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_p1_p3
    exact fun x hx => ⟨(lat0_sub hx.2).2, (lat2_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_p2_p3
    exact fun x hx => ⟨(lat1_sub hx.2).2, (lat2_sub hx.1).2⟩
  · exact absurd rfl hij
  · refine measure_mono_null ?_ null_p3_p4
    exact fun x hx => ⟨(lat2_sub hx.1).2, (lat3_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p3
    exact fun x hx => ⟨(baseA_sub hx.2).2, (lat2_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_pz_p3
    exact fun x hx => ⟨(baseB_sub hx.2).2, (lat2_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_p1_p4
    exact fun x hx => ⟨(lat0_sub hx.2).2, (lat3_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_p2_p4
    exact fun x hx => ⟨(lat1_sub hx.2).2, (lat3_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_p3_p4
    exact fun x hx => ⟨(lat2_sub hx.2).2, (lat3_sub hx.1).2⟩
  · exact absurd rfl hij
  · refine measure_mono_null ?_ null_pz_p4
    exact fun x hx => ⟨(baseA_sub hx.2).2, (lat3_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_pz_p4
    exact fun x hx => ⟨(baseB_sub hx.2).2, (lat3_sub hx.1).2⟩
  · refine measure_mono_null ?_ null_pz_p1
    exact fun x hx => ⟨(baseA_sub hx.1).2, (lat0_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p2
    exact fun x hx => ⟨(baseA_sub hx.1).2, (lat1_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p3
    exact fun x hx => ⟨(baseA_sub hx.1).2, (lat2_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p4
    exact fun x hx => ⟨(baseA_sub hx.1).2, (lat3_sub hx.2).2⟩
  · exact absurd rfl hij
  · refine measure_mono_null ?_ null_base
    exact fun x hx => ⟨(baseA_sub hx.1).2, le_antisymm (baseB_sub_y hx.2) (baseA_sub_y hx.1)⟩
  · refine measure_mono_null ?_ null_pz_p1
    exact fun x hx => ⟨(baseB_sub hx.1).2, (lat0_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p2
    exact fun x hx => ⟨(baseB_sub hx.1).2, (lat1_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p3
    exact fun x hx => ⟨(baseB_sub hx.1).2, (lat2_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_pz_p4
    exact fun x hx => ⟨(baseB_sub hx.1).2, (lat3_sub hx.2).2⟩
  · refine measure_mono_null ?_ null_base
    exact fun x hx => ⟨(baseB_sub hx.1).2, le_antisymm (baseB_sub_y hx.1) (baseA_sub_y hx.2)⟩
  · exact absurd rfl hij

lemma face6_sub (i : Fin 6) : face6 i ⊆ pyr \ pyrInt := by
  fin_cases i
  · exact fun x hx => ⟨(lat0_sub hx).1, fun h => by
      have := (lat0_sub hx).2; simp [p1, plane] at this; linarith [h.2.1]⟩
  · exact fun x hx => ⟨(lat1_sub hx).1, fun h => by
      have := (lat1_sub hx).2; simp [p2, plane] at this; linarith [h.2.2.1]⟩
  · exact fun x hx => ⟨(lat2_sub hx).1, fun h => by
      have := (lat2_sub hx).2; simp [p3, plane] at this; linarith [h.2.2.2.1]⟩
  · exact fun x hx => ⟨(lat3_sub hx).1, fun h => by
      have := (lat3_sub hx).2; simp [p4, plane] at this; linarith [h.2.2.2.2]⟩
  · exact fun x hx => ⟨(baseA_sub hx).1, fun h => by
      have := (baseA_sub hx).2; simp [pz, plane] at this; linarith [h.1]⟩
  · exact fun x hx => ⟨(baseB_sub hx).1, fun h => by
      have := (baseB_sub hx).2; simp [pz, plane] at this; linarith [h.1]⟩

/-- **The skin of the pyramid is the union of its six faces.** -/
theorem frontier_pyr : frontier pyr = ⋃ i, face6 i := by
  rw [frontier_pyr_eq_diff]
  refine subset_antisymm (fun x hx => ?_) (Set.iUnion_subset face6_sub)
  rcases mem_faces_of_tight hx.1 hx.2 with ((((h | h) | h) | h) | h) | h
  · exact Set.mem_iUnion.2 ⟨0, h⟩
  · exact Set.mem_iUnion.2 ⟨1, h⟩
  · exact Set.mem_iUnion.2 ⟨2, h⟩
  · exact Set.mem_iUnion.2 ⟨3, h⟩
  · exact Set.mem_iUnion.2 ⟨4, h⟩
  · exact Set.mem_iUnion.2 ⟨5, h⟩

end SymmetricCentroids.Pyramid

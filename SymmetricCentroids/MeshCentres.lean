/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids

/-!
# The centres of a mesh

A triangle mesh is a family of vertices `p : ι → ℝⁿ` and a family of triangles `t : τ → Fin 3 → ι`,
each given by the indices of its three vertices. Three centres are built from it without
favouring a direction:

* `vertexMean`: the mean of the vertices;
* `triangleMean`: the mean of the triangle centroids;
* `areaMean`: the mean of the triangle centroids weighted by the triangle areas, which is `S` for a
  polyhedral skin.

All three are weighted means (`wmean`). An affine map carries a weighted mean to the weighted mean
of the images (`map_wmean`), so an affine map that permutes the points and keeps the weights fixes
the mean (`wmean_fixed`).

A symmetry of the mesh (`KeepsMesh`) is an affine isometry that permutes the vertices and maps
each triangle onto a triangle, its vertices possibly in another order. It fixes the three centres
(`vertexMean_fixed`, `triangleMean_fixed`, `areaMean_fixed`), so when the symmetries of the mesh
fix at most one point `c`, the three centres are all `c` (`centres_eq_of_unique_fixed_point`).

The area of a triangle is written from its side lengths in a form symmetric in its three vertices
(`triangleArea`), and agrees with the usual `√(|u|²|v|² - ⟪u, v⟫²) / 2` (`triangleArea_eq`).
-/

open Finset

@[expose] public noncomputable section

namespace SymmetricCentroids.Mesh

variable {n : ℕ} {ι τ : Type*}

/-! ### Weighted means -/

section WeightedMean

variable [Fintype ι]

/-- The mean of the points `x i` weighted by `w i`. -/
def wmean (w : ι → ℝ) (x : ι → Space n) : Space n := (∑ i, w i)⁻¹ • ∑ i, w i • x i

/-- A weighted mean with nonzero total weight is an affine combination. -/
lemma wmean_eq_affineCombination (w : ι → ℝ) (x : ι → Space n) (hw : ∑ i, w i ≠ 0) :
    wmean w x = univ.affineCombination ℝ x fun i ↦ (∑ j, w j)⁻¹ * w i := by
  have h1 : ∑ i, (∑ j, w j)⁻¹ * w i = 1 := by rw [← mul_sum, inv_mul_cancel₀ hw]
  rw [univ.affineCombination_eq_linear_combination _ _ h1, wmean, smul_sum]
  simp only [smul_smul]

/-- **An affine map carries a weighted mean to the weighted mean of the images.** -/
lemma map_wmean (f : Space n →ᵃ[ℝ] Space n) (w : ι → ℝ) (x : ι → Space n)
    (hw : ∑ i, w i ≠ 0) : f (wmean w x) = wmean w (f ∘ x) := by
  rw [wmean_eq_affineCombination w x hw, univ.map_affineCombination _ _ (by
    rw [← mul_sum, inv_mul_cancel₀ hw]), wmean_eq_affineCombination w _ hw]

/-- Reindexing the points and the weights together does not move the mean. -/
lemma wmean_comp_perm (σ : Equiv.Perm ι) (w : ι → ℝ) (x : ι → Space n) :
    wmean (w ∘ σ) (x ∘ σ) = wmean w x := by
  simp only [wmean, Function.comp_apply]
  rw [Equiv.sum_comp σ w, Equiv.sum_comp σ fun i ↦ w i • x i]

/-- An affine map that permutes the points and keeps their weights fixes their weighted mean. -/
theorem wmean_fixed (f : Space n →ᵃ[ℝ] Space n) (σ : Equiv.Perm ι) (w : ι → ℝ)
    (x : ι → Space n) (hw : ∑ i, w i ≠ 0) (hwσ : ∀ i, w (σ i) = w i)
    (hx : ∀ i, f (x i) = x (σ i)) : f (wmean w x) = wmean w x := by
  rw [map_wmean f w x hw]
  have hw' : w = w ∘ σ := funext fun i ↦ (hwσ i).symm
  have hx' : f ∘ x = x ∘ σ := funext hx
  rw [hx']
  conv_lhs => rw [hw']
  exact wmean_comp_perm σ w x

end WeightedMean

/-! ### The area of a triangle -/

/-- The area of the triangle on `q 0`, `q 1`, `q 2`, from its side lengths, in a form symmetric in
the three vertices (Heron's formula: `16 A² = (Σ dᵢⱼ²)² / 4 - Σ dᵢⱼ⁴`, the sums running over
ordered pairs). -/
def triangleArea (q : Fin 3 → Space n) : ℝ :=
  √((∑ i, ∑ j, dist (q i) (q j) ^ 2) ^ 2 / 4 - ∑ i, ∑ j, dist (q i) (q j) ^ 4) / 4

/-- Reordering the vertices does not change the area. -/
lemma triangleArea_comp_perm (q : Fin 3 → Space n) (ρ : Equiv.Perm (Fin 3)) :
    triangleArea (q ∘ ρ) = triangleArea q := by
  have key : ∀ f : Fin 3 → Fin 3 → ℝ, ∑ i, ∑ j, f (ρ i) (ρ j) = ∑ i, ∑ j, f i j := fun f ↦ by
    rw [Equiv.sum_comp ρ fun i ↦ ∑ j, f i (ρ j)]
    exact sum_congr rfl fun i _ ↦ Equiv.sum_comp ρ (f i)
  simp only [triangleArea, Function.comp_apply]
  rw [key fun i j ↦ dist (q i) (q j) ^ 2, key fun i j ↦ dist (q i) (q j) ^ 4]

/-- An isometry does not change the area. -/
lemma triangleArea_isometry (g : Space n ≃ᵃⁱ[ℝ] Space n) (q : Fin 3 → Space n) :
    triangleArea (g ∘ q) = triangleArea q := by
  simp only [triangleArea, Function.comp_apply, AffineIsometryEquiv.dist_map]

/-- The area is the usual `√(|u|²|v|² - ⟪u, v⟫²) / 2`, with `u` and `v` two sides from `q 0`. -/
lemma triangleArea_eq (q : Fin 3 → Space n) :
    triangleArea q =
      √(‖q 1 - q 0‖ ^ 2 * ‖q 2 - q 0‖ ^ 2 - inner ℝ (q 1 - q 0) (q 2 - q 0) ^ 2) / 2 := by
  set X := ‖q 1 - q 0‖ ^ 2
  set Y := ‖q 2 - q 0‖ ^ 2
  set Z := ‖q 2 - q 1‖ ^ 2
  have hinner : inner ℝ (q 1 - q 0) (q 2 - q 0) = (X + Y - Z) / 2 := by
    have h := norm_sub_sq_real (q 1 - q 0) (q 2 - q 0)
    rw [show q 1 - q 0 - (q 2 - q 0) = -(q 2 - q 1) by abel, norm_neg] at h
    linarith
  have d01 : dist (q 0) (q 1) ^ 2 = X := by rw [dist_eq_norm, norm_sub_rev]
  have d02 : dist (q 0) (q 2) ^ 2 = Y := by rw [dist_eq_norm, norm_sub_rev]
  have d12 : dist (q 1) (q 2) ^ 2 = Z := by rw [dist_eq_norm, norm_sub_rev]
  have d4 : ∀ i j, dist (q i) (q j) ^ 4 = (dist (q i) (q j) ^ 2) ^ 2 := fun i j ↦ by ring
  simp only [triangleArea, Fin.sum_univ_three, d4, dist_self, dist_comm (q 1) (q 0),
    dist_comm (q 2) (q 0), dist_comm (q 2) (q 1), d01, d02, d12, hinner]
  rw [show ((0 : ℝ) ^ 2 + X + Y + (X + 0 ^ 2 + Z) + (Y + Z + 0 ^ 2)) ^ 2 / 4 -
      ((0 ^ 2) ^ 2 + X ^ 2 + Y ^ 2 + (X ^ 2 + (0 ^ 2) ^ 2 + Z ^ 2) +
        (Y ^ 2 + Z ^ 2 + (0 ^ 2) ^ 2)) = 2 ^ 2 * (X * Y - ((X + Y - Z) / 2) ^ 2) by ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

/-! ### A mesh and its centres -/

variable (p : ι → Space n) (t : τ → Fin 3 → ι)

/-- The mean of the vertices. -/
def vertexMean [Fintype ι] : Space n := wmean (fun _ ↦ 1) p

/-- The centroid of the triangle `k`, the mean of its three vertices. -/
def triCentroid (k : τ) : Space n := (3 : ℝ)⁻¹ • ∑ j, p (t k j)

/-- The area of the triangle `k`. -/
def triArea (k : τ) : ℝ := triangleArea (p ∘ t k)

/-- The mean of the triangle centroids. -/
def triangleMean [Fintype τ] : Space n := wmean (fun _ ↦ 1) (triCentroid p t)

/-- The mean of the triangle centroids weighted by the triangle areas: `S` of a polyhedral skin. -/
def areaMean [Fintype τ] : Space n := wmean (triArea p t) (triCentroid p t)

/-- `g` is a symmetry of the mesh: it permutes the vertices (by `σ`) and maps each triangle `k`
onto the triangle `π k`, whose vertices may come in another order (`ρ`). -/
def KeepsMesh (g : Space n ≃ᵃⁱ[ℝ] Space n) : Prop :=
  ∃ σ : Equiv.Perm ι, ∃ π : Equiv.Perm τ, (∀ i, g (p i) = p (σ i)) ∧
    ∀ k, ∃ ρ : Equiv.Perm (Fin 3), ∀ j, t (π k) (ρ j) = σ (t k j)

/-- The points fixed by every symmetry of the mesh. -/
def meshFixedSet : Set (Space n) := {x | ∀ g, KeepsMesh p t g → g x = x}

variable {p t}

lemma sum_one_ne_zero (α : Type*) [Fintype α] [Nonempty α] : ∑ _ : α, (1 : ℝ) ≠ 0 := by
  simp

lemma map_triCentroid {g : Space n ≃ᵃⁱ[ℝ] Space n} {σ : Equiv.Perm ι} {π : Equiv.Perm τ}
    (hσ : ∀ i, g (p i) = p (σ i)) (k : τ) (ρ : Equiv.Perm (Fin 3))
    (hρ : ∀ j, t (π k) (ρ j) = σ (t k j)) :
    g (triCentroid p t k) = triCentroid p t (π k) := by
  have hw : ∑ _ : Fin 3, (1 : ℝ) ≠ 0 := sum_one_ne_zero (Fin 3)
  have hmean : triCentroid p t k = wmean (fun _ ↦ 1) (p ∘ t k) := by
    simp [triCentroid, wmean]
  have hmean' : triCentroid p t (π k) = wmean (fun _ ↦ 1) (p ∘ t (π k)) := by
    simp [triCentroid, wmean]
  rw [hmean, hmean', ← AffineIsometryEquiv.coe_toAffineEquiv, ← AffineEquiv.coe_toAffineMap,
    map_wmean _ _ _ hw, ← wmean_comp_perm ρ (fun _ ↦ (1 : ℝ)) (p ∘ t (π k))]
  congr 1
  funext j
  simp [hσ, hρ]

lemma triArea_perm {g : Space n ≃ᵃⁱ[ℝ] Space n} {σ : Equiv.Perm ι} {π : Equiv.Perm τ}
    (hσ : ∀ i, g (p i) = p (σ i)) (k : τ) (ρ : Equiv.Perm (Fin 3))
    (hρ : ∀ j, t (π k) (ρ j) = σ (t k j)) :
    triArea p t (π k) = triArea p t k := by
  rw [triArea, triArea, ← triangleArea_comp_perm (p ∘ t (π k)) ρ,
    ← triangleArea_isometry g (p ∘ t k)]
  congr 1
  funext j
  simp [hσ, hρ]

/-- **A symmetry of the mesh fixes the mean of its vertices.** -/
theorem vertexMean_fixed [Fintype ι] [Nonempty ι] {g : Space n ≃ᵃⁱ[ℝ] Space n}
    (hg : KeepsMesh p t g) :
    g (vertexMean p) = vertexMean p := by
  obtain ⟨σ, _, hσ, _⟩ := hg
  exact wmean_fixed g.toAffineEquiv.toAffineMap σ _ p (sum_one_ne_zero ι) (fun _ ↦ rfl) hσ

/-- **A symmetry of the mesh fixes the mean of its triangle centroids.** -/
theorem triangleMean_fixed [Fintype τ] [Nonempty τ] {g : Space n ≃ᵃⁱ[ℝ] Space n}
    (hg : KeepsMesh p t g) :
    g (triangleMean p t) = triangleMean p t := by
  obtain ⟨σ, π, hσ, ht⟩ := hg
  refine wmean_fixed g.toAffineEquiv.toAffineMap π _ _ (sum_one_ne_zero τ) (fun _ ↦ rfl)
    fun k ↦ ?_
  obtain ⟨ρ, hρ⟩ := ht k
  exact map_triCentroid hσ k ρ hρ

/-- **A symmetry of the mesh fixes the area-weighted mean of its triangle centroids**, when the
total area is not zero. -/
theorem areaMean_fixed [Fintype τ] (hA : ∑ k, triArea p t k ≠ 0) {g : Space n ≃ᵃⁱ[ℝ] Space n}
    (hg : KeepsMesh p t g) : g (areaMean p t) = areaMean p t := by
  obtain ⟨σ, π, hσ, ht⟩ := hg
  refine wmean_fixed g.toAffineEquiv.toAffineMap π _ _ hA (fun k ↦ ?_) fun k ↦ ?_
  · obtain ⟨ρ, hρ⟩ := ht k
    exact triArea_perm hσ k ρ hρ
  · obtain ⟨ρ, hρ⟩ := ht k
    exact map_triCentroid hσ k ρ hρ

/-- **The centres of a mesh coincide** when its symmetries fix at most one point `c`: the mean of
the vertices, the mean of the triangle centroids and the area-weighted mean are all `c`. -/
theorem centres_eq_of_unique_fixed_point [Fintype ι] [Fintype τ] [Nonempty ι] [Nonempty τ]
    (hA : ∑ k, triArea p t k ≠ 0) (c : Space n) (huniq : ∀ x ∈ meshFixedSet p t, x = c) :
    vertexMean p = c ∧ triangleMean p t = c ∧ areaMean p t = c :=
  ⟨huniq _ fun _ hg ↦ vertexMean_fixed hg, huniq _ fun _ hg ↦ triangleMean_fixed hg,
    huniq _ fun _ hg ↦ areaMean_fixed hA hg⟩

end SymmetricCentroids.Mesh

/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids

/-!
# Tetrahedra: `S = B` exactly when the tetrahedron is a disphenoid

On a tetrahedron, the surface centroid is the mean of the four face centroids weighted by the
face areas, and the vertex centroid is the mean of the four vertices.

* `surfaceCentroid_eq_iff`: they coincide exactly when the four faces have the same area. The
  face opposite the vertex `vᵢ` has its centroid at `(4B - vᵢ)/3`, so `S = B` exactly when `B`
  is the mean of the vertices weighted by the areas of the opposite faces. The vertices are
  affinely independent, so the weights must all be equal. This part holds for any positive
  weights.
* `disphenoid_of_equal_areas`: a tetrahedron of nonzero volume whose four faces have the same
  area has its opposite edges equal in pairs, that is, it is a disphenoid.
* `disphenoid_of_centroid_eq`: the two together, `S = B` makes a disphenoid.
* `equal_areas_of_disphenoid`: conversely, a disphenoid has four faces of equal area, since each
  face has the same three side lengths and Heron's formula follows from Lagrange's identity.
* `centroid_eq_iff_disphenoid`: hence `S = B` exactly when the tetrahedron is a disphenoid.

Not proved here: that the weighted mean is the `surfCentroid` of the solid tetrahedron, its
centroid under the area measure `μHE[2]`, and that the vertex centroid is its `volCentroid`.
Both are true, but they need the area and the centroid of a triangle under `μHE[2]`. Nor that a
disphenoid has three half turns fixing only its centre.
-/

open Finset Matrix

@[expose] public noncomputable section

namespace SymmetricCentroids.Tetrahedron

variable (v : Fin 4 → E)

/-- The vertex centroid, the mean of the four vertices. -/
def vertexCentroid : E := (4 : ℝ)⁻¹ • ∑ i, v i

/-- The centroid of the face opposite the vertex `i`, the mean of the other three. -/
def faceCentroid (i : Fin 4) : E := (3 : ℝ)⁻¹ • (∑ j, v j - v i)

/-- The mean of the face centroids, weighted by `A`. -/
def weightedCentroid (A : Fin 4 → ℝ) : E := (∑ i, A i)⁻¹ • ∑ i, A i • faceCentroid v i

/-- The area of the face opposite the vertex `i`: half the norm of a cross product of two of
its edges. -/
def faceArea (i : Fin 4) : ℝ :=
  let p := fun k : Fin 3 => v (i.succAbove k)
  ‖(WithLp.toLp 2 ((p 1 - p 0).ofLp ⨯₃ (p 2 - p 0).ofLp) : E)‖ / 2

/-- With positive weights on affinely independent vertices, the weighted mean of the face
centroids is the vertex centroid exactly when the weights are all equal. -/
theorem weightedCentroid_eq_iff (hv : AffineIndependent ℝ v) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) :
    weightedCentroid v A = vertexCentroid v ↔ ∀ i j, A i = A j := by
  set T := ∑ i, A i with hT
  have hT0 : T ≠ 0 := (Finset.sum_pos (fun i _ => hA i) Finset.univ_nonempty).ne'
  set P := ∑ i, v i with hP
  set Q := ∑ i, A i • v i with hQ
  -- The face opposite `vᵢ` has its centroid at `(P - vᵢ)/3`.
  have hsum : ∑ i, A i • faceCentroid v i = (3 : ℝ)⁻¹ • (T • P - Q) := by
    have h1 : ∀ i, A i • faceCentroid v i = (3 : ℝ)⁻¹ • (A i • P) - (3 : ℝ)⁻¹ • (A i • v i) := by
      intro i; simp only [faceCentroid, ← hP]; module
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, ← Finset.smul_sum,
      ← Finset.smul_sum, ← Finset.sum_smul, ← hT, ← hQ, smul_sub]
  have hS : weightedCentroid v A = T⁻¹ • (3 : ℝ)⁻¹ • (T • P - Q) := by
    simp only [weightedCentroid, ← hT, hsum]
  have hB : vertexCentroid v = (4 : ℝ)⁻¹ • P := rfl
  rw [hS, hB]
  constructor
  · intro h
    -- `S = B` turns into `∑ (Aᵢ - T/4) vᵢ = 0`, with weights summing to zero.
    rw [inv_smul_eq_iff₀ hT0, inv_smul_eq_iff₀ (by norm_num : (3 : ℝ) ≠ 0)] at h
    have hQP : Q = (T / 4) • P := by linear_combination (norm := module) -h
    have key : ∑ i, (A i - T / 4) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ← hQ, ← hP, hQP, sub_self]
    have hw : ∑ i, (A i - T / 4) = 0 := by
      rw [Finset.sum_sub_distrib, ← hT]; simp; ring
    have hzero := (affineIndependent_iff_of_fintype ℝ v).1 hv (fun i => A i - T / 4) hw (by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw 0,
        Finset.weightedVSubOfPoint_apply]
      simpa using key)
    intro i j
    have hi : A i - T / 4 = 0 := hzero i
    have hj : A j - T / 4 = 0 := hzero j
    linarith
  · intro h
    have hA0 : ∀ i, A i = A 0 := fun i => h i 0
    have hT4 : T = 4 * A 0 := by
      rw [hT, Fin.sum_univ_four, hA0 1, hA0 2, hA0 3]; ring
    have hQ0 : Q = A 0 • P := by
      rw [hQ, hP, Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hA0 i]
    have hA00 : A 0 ≠ 0 := (hA 0).ne'
    rw [hQ0, hT4, ← sub_smul, smul_smul, smul_smul]
    congr 1
    field_simp
    ring

/-- On a tetrahedron whose four faces have positive area, the area-weighted mean of the face
centroids is the vertex centroid exactly when the four faces have the same area. -/
theorem surfaceCentroid_eq_iff (hv : AffineIndependent ℝ v) (hA : ∀ i, 0 < faceArea v i) :
    weightedCentroid v (faceArea v) = vertexCentroid v ↔
      ∀ i j, faceArea v i = faceArea v j :=
  weightedCentroid_eq_iff v hv _ hA

/-! ### Equal face areas make a disphenoid

Let `a`, `b`, `c` be the edges from one vertex, and `nₐ = b × c`, `n_b = c × a`, `n_c = a × b`
the normals of the three faces through that vertex, the fourth being `m = -(nₐ + n_b + n_c)`.
The four normals have the same length when the faces have the same area, and they sum to zero,
so `nₐ · n_b = n_c · m`. The cross product of two normals is their common edge times the triple
product: `nₐ × n_b = det • c` and `n_c × m = det • (a - b)`. Lagrange's identity then gives
`det² |c|² = det² |a - b|²`, and `det ≠ 0` for a tetrahedron of nonzero volume. -/

/-- One pair of opposite edges: `c` and `a - b` have the same length. -/
lemma opposite_edges (a b c : Fin 3 → ℝ) (hdet : a ⬝ᵥ (b ⨯₃ c) ≠ 0)
    (ha : (b ⨯₃ c) ⬝ᵥ (b ⨯₃ c) = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b))
    (hb : (c ⨯₃ a) ⬝ᵥ (c ⨯₃ a) = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b))
    (h0 : (b ⨯₃ c + c ⨯₃ a + a ⨯₃ b) ⬝ᵥ (b ⨯₃ c + c ⨯₃ a + a ⨯₃ b) =
      (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b)) :
    (a - b) ⬝ᵥ (a - b) = c ⬝ᵥ c := by
  set d := a ⬝ᵥ (b ⨯₃ c)
  set na := b ⨯₃ c
  set nb := c ⨯₃ a
  set nc := a ⨯₃ b
  have L2 : na ⨯₃ nb = d • c := by
    ext i; fin_cases i <;> simp [na, nb, d, cross_apply, dotProduct, Fin.sum_univ_three] <;> ring
  have L3 : nc ⨯₃ -(na + nb + nc) = d • (a - b) := by
    ext i
    fin_cases i <;> simp [na, nb, nc, d, cross_apply, dotProduct, Fin.sum_univ_three] <;> ring
  have e1 := cross_dot_cross na nb na nb
  have e2 := cross_dot_cross nc (-(na + nb + nc)) nc (-(na + nb + nc))
  rw [L2] at e1
  rw [L3] at e2
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, neg_dotProduct, dotProduct_neg,
    add_dotProduct, dotProduct_add, dotProduct_comm nb na, dotProduct_comm nc na,
    dotProduct_comm nc nb] at e1 e2 h0
  have hd : d * d ≠ 0 := mul_ne_zero hdet hdet
  have key : d * d * ((a - b) ⬝ᵥ (a - b)) = d * d * (c ⬝ᵥ c) := by
    -- With `A = nₐ·nₐ`, `X = n_c·n_c`, and `t = (r + q + X - p)/2` for the cross dot products,
    -- the remainder is `t'·(S - X) + (…)·(A - X) + (…)·(B - X)`, `S` the expanded `m · m`.
    linear_combination e2 - e1
      + (nc ⬝ᵥ nc - (na ⬝ᵥ nc + nb ⬝ᵥ nc + nc ⬝ᵥ nc - na ⬝ᵥ nb) / 2) * h0
      + ((na ⬝ᵥ nc + nb ⬝ᵥ nc + nc ⬝ᵥ nc - na ⬝ᵥ nb) / 2 - nc ⬝ᵥ nc - (nb ⬝ᵥ nb - nc ⬝ᵥ nc)) * ha
      + ((na ⬝ᵥ nc + nb ⬝ᵥ nc + nc ⬝ᵥ nc - na ⬝ᵥ nb) / 2 - nc ⬝ᵥ nc) * hb
  exact mul_left_cancel₀ hd key

/-- The three pairs of opposite edges, when the four normals have the same squared length `X`. -/
lemma opposite_edges_all (a b c : Fin 3 → ℝ) (hdet : a ⬝ᵥ (b ⨯₃ c) ≠ 0) (X : ℝ)
    (ha : (b ⨯₃ c) ⬝ᵥ (b ⨯₃ c) = X) (hb : (c ⨯₃ a) ⬝ᵥ (c ⨯₃ a) = X)
    (hc : (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) = X)
    (h0 : (b ⨯₃ c + c ⨯₃ a + a ⨯₃ b) ⬝ᵥ (b ⨯₃ c + c ⨯₃ a + a ⨯₃ b) = X) :
    (a - b) ⬝ᵥ (a - b) = c ⬝ᵥ c ∧ (b - c) ⬝ᵥ (b - c) = a ⬝ᵥ a ∧
      (c - a) ⬝ᵥ (c - a) = b ⬝ᵥ b := by
  have hdet' : b ⬝ᵥ (c ⨯₃ a) ≠ 0 := by
    convert hdet using 1; simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring
  have hdet'' : c ⬝ᵥ (a ⨯₃ b) ≠ 0 := by
    convert hdet using 1; simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring
  have hsum1 : c ⨯₃ a + a ⨯₃ b + b ⨯₃ c = b ⨯₃ c + c ⨯₃ a + a ⨯₃ b := by abel
  have hsum2 : a ⨯₃ b + b ⨯₃ c + c ⨯₃ a = b ⨯₃ c + c ⨯₃ a + a ⨯₃ b := by abel
  refine ⟨opposite_edges a b c hdet (by rw [ha, hc]) (by rw [hb, hc]) (by rw [h0, hc]), ?_, ?_⟩
  · exact opposite_edges b c a hdet' (by rw [hb, ha]) (by rw [hc, ha]) (by rw [hsum1, h0, ha])
  · exact opposite_edges c a b hdet'' (by rw [hc, hb]) (by rw [ha, hb]) (by rw [hsum2, h0, hb])

/-- Six times the signed volume of the tetrahedron: the triple product of the edges from `v 0`. -/
def tripleProduct : ℝ :=
  (v 1 - v 0).ofLp ⬝ᵥ ((v 2 - v 0).ofLp ⨯₃ (v 3 - v 0).ofLp)

lemma norm_sq_toLp (y : Fin 3 → ℝ) : ‖(WithLp.toLp 2 y : E)‖ ^ 2 = y ⬝ᵥ y := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, Fin.sum_univ_three, sq]

lemma dist_sq (p q : E) : dist p q ^ 2 = (p - q).ofLp ⬝ᵥ (p - q).ofLp := by
  rw [dist_eq_norm, ← norm_sq_toLp]

lemma faceArea_sq (i : Fin 4) :
    (2 * faceArea v i) ^ 2 =
      ((v (i.succAbove 1) - v (i.succAbove 0)).ofLp ⨯₃ (v (i.succAbove 2) - v (i.succAbove 0)).ofLp)
        ⬝ᵥ ((v (i.succAbove 1) - v (i.succAbove 0)).ofLp ⨯₃
          (v (i.succAbove 2) - v (i.succAbove 0)).ofLp) := by
  rw [faceArea, mul_div_cancel₀ _ two_ne_zero, norm_sq_toLp]

/-- **Equal face areas make a disphenoid.** A tetrahedron of nonzero volume whose four faces have
the same area has its opposite edges equal in pairs. -/
theorem disphenoid_of_equal_areas (hvol : tripleProduct v ≠ 0)
    (h : ∀ i j, faceArea v i = faceArea v j) :
    dist (v 0) (v 1) = dist (v 2) (v 3) ∧ dist (v 0) (v 2) = dist (v 1) (v 3) ∧
      dist (v 0) (v 3) = dist (v 1) (v 2) := by
  set x := fun i => (v i).ofLp with hx
  set a := x 1 - x 0
  set b := x 2 - x 0
  set c := x 3 - x 0
  have f0 : (2 * faceArea v 0) ^ 2 =
      ((x 2 - x 1) ⨯₃ (x 3 - x 1)) ⬝ᵥ ((x 2 - x 1) ⨯₃ (x 3 - x 1)) := faceArea_sq v 0
  have f1 : (2 * faceArea v 1) ^ 2 = (b ⨯₃ c) ⬝ᵥ (b ⨯₃ c) := faceArea_sq v 1
  have f2 : (2 * faceArea v 2) ^ 2 =
      ((x 1 - x 0) ⨯₃ (x 3 - x 0)) ⬝ᵥ ((x 1 - x 0) ⨯₃ (x 3 - x 0)) := faceArea_sq v 2
  have f3 : (2 * faceArea v 3) ^ 2 = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) := faceArea_sq v 3
  set X := (2 * faceArea v 3) ^ 2
  have e0 : (x 2 - x 1) ⨯₃ (x 3 - x 1) = b ⨯₃ c + c ⨯₃ a + a ⨯₃ b := by
    ext i; fin_cases i <;> simp [a, b, c, cross_apply] <;> ring
  have e2 : (x 1 - x 0) ⨯₃ (x 3 - x 0) = -(c ⨯₃ a) := by
    ext i; fin_cases i <;> simp [a, c, cross_apply] <;> ring
  obtain ⟨k1, k2, k3⟩ := opposite_edges_all a b c hvol X
    (by rw [← f1, h 1 3])
    (by rw [show (c ⨯₃ a) ⬝ᵥ (c ⨯₃ a) = (-(c ⨯₃ a)) ⬝ᵥ (-(c ⨯₃ a)) by
      rw [neg_dotProduct, dotProduct_neg, neg_neg], ← e2, ← f2, h 2 3])
    (by rw [← f3])
    (by rw [← e0, ← f0, h 0 3])
  have d : ∀ i j, dist (v i) (v j) ^ 2 = (x i - x j) ⬝ᵥ (x i - x j) := fun i j => dist_sq _ _
  have sq_eq : ∀ {p q r s : Fin 4}, dist (v p) (v q) ^ 2 = dist (v r) (v s) ^ 2 →
      dist (v p) (v q) = dist (v r) (v s) := fun h' =>
    (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h'
  refine ⟨sq_eq ?_, sq_eq ?_, sq_eq ?_⟩
  · rw [d, d, show x 0 - x 1 = -a by simp [a], show x 2 - x 3 = b - c by simp [b, c]]
    simpa using k2.symm
  · rw [d, d, show x 0 - x 2 = -b by simp [b], show x 1 - x 3 = a - c by simp [a, c]]
    have : (a - c) ⬝ᵥ (a - c) = (c - a) ⬝ᵥ (c - a) := by
      rw [show a - c = -(c - a) by abel, neg_dotProduct, dotProduct_neg, neg_neg]
    simpa [this] using k3.symm
  · rw [d, d, show x 0 - x 3 = -c by simp [c], show x 1 - x 2 = a - b by simp [a, b]]
    simpa using k1.symm

/-- **`S = B` makes a disphenoid.** On a tetrahedron of nonzero volume whose faces have positive
area, if the area-weighted mean of the face centroids is the vertex centroid, then the opposite
edges are equal in pairs. -/
theorem disphenoid_of_centroid_eq (hv : AffineIndependent ℝ v) (hA : ∀ i, 0 < faceArea v i)
    (hvol : tripleProduct v ≠ 0) (h : weightedCentroid v (faceArea v) = vertexCentroid v) :
    dist (v 0) (v 1) = dist (v 2) (v 3) ∧ dist (v 0) (v 2) = dist (v 1) (v 3) ∧
      dist (v 0) (v 3) = dist (v 1) (v 2) :=
  disphenoid_of_equal_areas v hvol ((surfaceCentroid_eq_iff v hv hA).1 h)

/-! ### A disphenoid has four faces of equal area -/

/-- Heron's formula, in squares: four times the squared area of a triangle whose sides have squared
lengths `x`, `y`, `z`. -/
def heron (x y z : ℝ) : ℝ := x * y - ((x + y - z) / 2) ^ 2

/-- The squared length of a cross product of two sides depends only on the three sides. -/
lemma cross_sq_heron (p₀ p₁ p₂ : Fin 3 → ℝ) :
    ((p₁ - p₀) ⨯₃ (p₂ - p₀)) ⬝ᵥ ((p₁ - p₀) ⨯₃ (p₂ - p₀)) =
      heron ((p₁ - p₀) ⬝ᵥ (p₁ - p₀)) ((p₂ - p₀) ⬝ᵥ (p₂ - p₀)) ((p₂ - p₁) ⬝ᵥ (p₂ - p₁)) := by
  simp only [heron, cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- **A disphenoid has four faces of equal area.** When the opposite edges are equal in pairs,
every face has the same three side lengths, hence the same area. -/
theorem equal_areas_of_disphenoid
    (h₁ : dist (v 0) (v 1) = dist (v 2) (v 3)) (h₂ : dist (v 0) (v 2) = dist (v 1) (v 3))
    (h₃ : dist (v 0) (v 3) = dist (v 1) (v 2)) :
    ∀ i j, faceArea v i = faceArea v j := by
  set x := fun i => (v i).ofLp
  have dd : ∀ i j, (x i - x j) ⬝ᵥ (x i - x j) = dist (v i) (v j) ^ 2 :=
    fun i j => (dist_sq (v i) (v j)).symm
  have f0 : (2 * faceArea v 0) ^ 2 = heron (dist (v 2) (v 1) ^ 2) (dist (v 3) (v 1) ^ 2)
      (dist (v 3) (v 2) ^ 2) := by
    rw [← dd, ← dd, ← dd]; exact (faceArea_sq v 0).trans (cross_sq_heron (x 1) (x 2) (x 3))
  have f1 : (2 * faceArea v 1) ^ 2 = heron (dist (v 2) (v 0) ^ 2) (dist (v 3) (v 0) ^ 2)
      (dist (v 3) (v 2) ^ 2) := by
    rw [← dd, ← dd, ← dd]; exact (faceArea_sq v 1).trans (cross_sq_heron (x 0) (x 2) (x 3))
  have f2 : (2 * faceArea v 2) ^ 2 = heron (dist (v 1) (v 0) ^ 2) (dist (v 3) (v 0) ^ 2)
      (dist (v 3) (v 1) ^ 2) := by
    rw [← dd, ← dd, ← dd]; exact (faceArea_sq v 2).trans (cross_sq_heron (x 0) (x 1) (x 3))
  have f3 : (2 * faceArea v 3) ^ 2 = heron (dist (v 1) (v 0) ^ 2) (dist (v 2) (v 0) ^ 2)
      (dist (v 2) (v 1) ^ 2) := by
    rw [← dd, ← dd, ← dd]; exact (faceArea_sq v 3).trans (cross_sq_heron (x 0) (x 1) (x 2))
  simp only [dist_comm (v 2) (v 1), dist_comm (v 3) (v 1), dist_comm (v 3) (v 2),
    dist_comm (v 2) (v 0), dist_comm (v 3) (v 0), dist_comm (v 1) (v 0)] at f0 f1 f2 f3
  rw [← h₁, ← h₂, ← h₃] at f0
  rw [← h₁] at f1
  rw [← h₂] at f2
  rw [← h₃] at f3
  have hsq : ∀ i, (2 * faceArea v i) ^ 2 = (2 * faceArea v 3) ^ 2 := by
    intro i; fin_cases i
    · change (2 * faceArea v 0) ^ 2 = _
      rw [f0, f3]; simp only [heron]; ring
    · change (2 * faceArea v 1) ^ 2 = _
      rw [f1, f3]; simp only [heron]; ring
    · change (2 * faceArea v 2) ^ 2 = _
      rw [f2, f3]; simp only [heron]; ring
    · rfl
  have nonneg : ∀ i, 0 ≤ 2 * faceArea v i := fun i => by
    simp only [faceArea]; positivity
  intro i j
  have hi := (pow_left_inj₀ (nonneg i) (nonneg 3) two_ne_zero).1 (hsq i)
  have hj := (pow_left_inj₀ (nonneg j) (nonneg 3) two_ne_zero).1 (hsq j)
  linarith

/-- **`S = B` exactly when the tetrahedron is a disphenoid**, for a tetrahedron of nonzero volume
whose faces have positive area, `S` being the area-weighted mean of the face centroids. -/
theorem centroid_eq_iff_disphenoid (hv : AffineIndependent ℝ v) (hA : ∀ i, 0 < faceArea v i)
    (hvol : tripleProduct v ≠ 0) :
    weightedCentroid v (faceArea v) = vertexCentroid v ↔
      dist (v 0) (v 1) = dist (v 2) (v 3) ∧ dist (v 0) (v 2) = dist (v 1) (v 3) ∧
        dist (v 0) (v 3) = dist (v 1) (v 2) :=
  ⟨disphenoid_of_centroid_eq v hv hA hvol, fun ⟨h₁, h₂, h₃⟩ =>
    (surfaceCentroid_eq_iff v hv hA).2 (equal_areas_of_disphenoid v h₁ h₂ h₃)⟩

end SymmetricCentroids.Tetrahedron

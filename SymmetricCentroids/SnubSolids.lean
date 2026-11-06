/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids

/-!
# The two snub solids

The snub cube and the snub dodecahedron are chiral: they have no plane and no centre of symmetry.
Their rotations alone still fix a single point, so `S = B` there. This file checks it on their
vertices, written with the usual coordinates.

* The snub cube: the even permutations of `(±1, ±1/t, ±t)` with an even number of plus
  signs, and the odd permutations with an odd number of plus signs, `t` being the tribonacci
  constant. It turns onto itself by a quarter turn about the `z` axis, `(x, y, z) ↦ (-y, x, z)`,
  and about the `x` axis, `(x, y, z) ↦ (x, -z, y)`.
* The snub dodecahedron: the even permutations, with an even number of plus signs, of five
  triples of coordinates. It turns onto itself by a half turn about the `z` axis,
  `(x, y, z) ↦ (-x, -y, z)`, and about the `x` axis, `(x, y, z) ↦ (x, -y, -z)`.

In both cases, the two rotations fix nothing but the origin, so `S = B = 0` for the solid, the
convex hull of the vertices. The invariance holds whatever the values in the triples: it only
moves coordinates and flips signs.
-/

open MeasureTheory Equiv

@[expose] public noncomputable section

namespace SymmetricCentroids.Snub

/-- A sign: `false` is `+1`, `true` is `-1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

/-- The point whose coordinate `i` is `± base (σ i)`, the sign given by `s i`: `base` permuted by
`σ`, with the signs `s`. -/
def vertex (base : Fin 3 → ℝ) (q : Perm (Fin 3) × (Fin 3 → Bool)) : E :=
  WithLp.toLp 2 fun i => sgn (q.2 i) * base (q.1 i)

/-- The number of plus signs. -/
def plus (s : Fin 3 → Bool) : ℕ := (Finset.univ.filter fun i => s i = false).card

/-- The isometry `p ↦ (±p (τ i))ᵢ`, which permutes the coordinates by `τ` and flips the signs
`ε`. -/
def signedPerm (τ : Perm (Fin 3)) (ε : Fin 3 → Bool) : E ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ τ.symm).trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun i =>
      if ε i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma signedPerm_apply (τ : Perm (Fin 3)) (ε : Fin 3 → Bool) (p : E) (i : Fin 3) :
    signedPerm τ ε p i = sgn (ε i) * p (τ i) := by
  simp only [signedPerm, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, PiLp.toLp_apply, sgn]
  split_ifs <;> simp [Equiv.piCongrLeft']

/-- What a signed permutation does to the parameters of a vertex. -/
def act (τ : Perm (Fin 3)) (ε : Fin 3 → Bool) (q : Perm (Fin 3) × (Fin 3 → Bool)) :
    Perm (Fin 3) × (Fin 3 → Bool) :=
  (q.1 * τ, fun i => xor (ε i) (q.2 (τ i)))

lemma signedPerm_vertex (τ : Perm (Fin 3)) (ε : Fin 3 → Bool) (base : Fin 3 → ℝ)
    (q : Perm (Fin 3) × (Fin 3 → Bool)) :
    signedPerm τ ε (vertex base q) = vertex base (act τ ε q) := by
  ext i
  simp only [signedPerm_apply, vertex, act, PiLp.toLp_apply, sgn_xor, Perm.mul_apply]
  ring

/-- A signed permutation that maps the parameters onto themselves maps the vertices onto
themselves. -/
lemma image_vertices (τ : Perm (Fin 3)) (ε : Fin 3 → Bool) (base : Fin 3 → ℝ)
    (P : Finset (Perm (Fin 3) × (Fin 3 → Bool))) (hP : P.image (act τ ε) = P) :
    signedPerm τ ε '' (vertex base '' ↑P) = vertex base '' ↑P := by
  rw [Set.image_image]
  simp only [signedPerm_vertex]
  rw [← Set.image_image (vertex base) (act τ ε), ← Finset.coe_image, hP]

/-! ### The rotations -/

/-- The quarter turn about the `z` axis: `(x, y, z) ↦ (-y, x, z)`. -/
def quarterZ : E ≃ₗᵢ[ℝ] E := signedPerm (swap 0 1) ![true, false, false]

/-- The quarter turn about the `x` axis: `(x, y, z) ↦ (x, -z, y)`. -/
def quarterX : E ≃ₗᵢ[ℝ] E := signedPerm (swap 1 2) ![false, true, false]

/-- The half turn about the `z` axis: `(x, y, z) ↦ (-x, -y, z)`. -/
def halfZ : E ≃ₗᵢ[ℝ] E := signedPerm 1 ![true, true, false]

/-- The half turn about the `x` axis: `(x, y, z) ↦ (x, -y, -z)`. -/
def halfX : E ≃ₗᵢ[ℝ] E := signedPerm 1 ![false, true, true]

/-- The two quarter turns fix nothing but the origin. -/
lemma eq_zero_of_quarter (p : E) (hz : quarterZ p = p) (hx : quarterX p = p) : p = 0 := by
  have h := fun i => congrArg (· i) hz
  have h' := fun i => congrArg (· i) hx
  simp only [quarterZ, quarterX, signedPerm_apply, sgn] at h h'
  have h0 := h 0; have h1 := h 1; have h1' := h' 1; have h2' := h' 2
  simp at h0 h1 h1' h2'
  ext i
  fin_cases i <;> simp <;> linarith

/-- The two half turns fix nothing but the origin. -/
lemma eq_zero_of_half (p : E) (hz : halfZ p = p) (hx : halfX p = p) : p = 0 := by
  have h := fun i => congrArg (· i) hz
  have h' := fun i => congrArg (· i) hx
  simp only [halfZ, halfX, signedPerm_apply, sgn] at h h'
  have h0 := h 0; have h1 := h 1; have h2' := h' 2
  simp at h0 h1 h2'
  ext i
  fin_cases i <;> simp <;> linarith

/-! ### The snub cube -/

/-- The parameters of the snub cube's vertices: the even permutations with an even number of plus
signs, and the odd permutations with an odd number of plus signs. -/
def cubeParams : Finset (Perm (Fin 3) × (Fin 3 → Bool)) :=
  Finset.univ.filter fun q => Perm.sign q.1 = (-1) ^ plus q.2

/-- The 24 vertices of the snub cube, for the tribonacci constant `t`. -/
def snubCube (t : ℝ) : Set E := vertex ![1, t⁻¹, t] '' ↑cubeParams

lemma cubeParams_card : cubeParams.card = 24 := by decide

lemma quarterZ_snubCube (t : ℝ) : quarterZ '' snubCube t = snubCube t :=
  image_vertices _ _ _ _ (by decide)

lemma quarterX_snubCube (t : ℝ) : quarterX '' snubCube t = snubCube t :=
  image_vertices _ _ _ _ (by decide)

/-! ### The snub dodecahedron -/

/-- The parameters of the snub dodecahedron's vertices: the even permutations with an even number
of plus signs. -/
def dodecaParams : Finset (Perm (Fin 3) × (Fin 3 → Bool)) :=
  Finset.univ.filter fun q => Perm.sign q.1 = 1 ∧ Even (plus q.2)

/-- The 60 vertices of the snub dodecahedron, from its five triples of coordinates. -/
def snubDodecahedron (bases : Fin 5 → Fin 3 → ℝ) : Set E :=
  ⋃ k, vertex (bases k) '' ↑dodecaParams

lemma dodecaParams_card : dodecaParams.card = 12 := by decide

lemma halfZ_snubDodecahedron (bases : Fin 5 → Fin 3 → ℝ) :
    halfZ '' snubDodecahedron bases = snubDodecahedron bases := by
  rw [snubDodecahedron, Set.image_iUnion]
  exact Set.iUnion_congr fun k => image_vertices _ _ _ _ (by decide)

lemma halfX_snubDodecahedron (bases : Fin 5 → Fin 3 → ℝ) :
    halfX '' snubDodecahedron bases = snubDodecahedron bases := by
  rw [snubDodecahedron, Set.image_iUnion]
  exact Set.iUnion_congr fun k => image_vertices _ _ _ _ (by decide)

/-! ### `S = B` for the solids -/

/-- A linear isometry that maps a set of vertices onto itself is a symmetry of their convex hull. -/
lemma isSymmetry_convexHull (g : E ≃ₗᵢ[ℝ] E) (V : Set E) (h : g '' V = V) :
    IsSymmetry (convexHull ℝ V) g.toAffineIsometryEquiv := by
  have := (g.toLinearEquiv.toLinearMap).image_convexHull V
  simpa [IsSymmetry, h] using this

/-- The centroids of the solid snub cube are both at the origin. -/
theorem snubCube_centroids (t : ℝ) (hV : volume (convexHull ℝ (snubCube t)) ≠ 0)
    (hA₀ : μHE[2] (frontier (convexHull ℝ (snubCube t))) ≠ 0)
    (hA : μHE[2] (frontier (convexHull ℝ (snubCube t))) ≠ ⊤) :
    surfCentroid (convexHull ℝ (snubCube t)) = 0 ∧ volCentroid (convexHull ℝ (snubCube t)) = 0 :=
  centroids_eq_of_unique_fixed_point (convexHull ℝ (snubCube t))
    ((cubeParams.finite_toSet.image _ : (snubCube t).Finite).isCompact_convexHull (𝕜 := ℝ))
    hV hA₀ hA 0 fun p hp => eq_zero_of_quarter p
      (hp _ (isSymmetry_convexHull quarterZ _ (quarterZ_snubCube t)))
      (hp _ (isSymmetry_convexHull quarterX _ (quarterX_snubCube t)))

/-- The centroids of the solid snub dodecahedron are both at the origin. -/
theorem snubDodecahedron_centroids (bases : Fin 5 → Fin 3 → ℝ)
    (hV : volume (convexHull ℝ (snubDodecahedron bases)) ≠ 0)
    (hA₀ : μHE[2] (frontier (convexHull ℝ (snubDodecahedron bases))) ≠ 0)
    (hA : μHE[2] (frontier (convexHull ℝ (snubDodecahedron bases))) ≠ ⊤) :
    surfCentroid (convexHull ℝ (snubDodecahedron bases)) = 0 ∧
      volCentroid (convexHull ℝ (snubDodecahedron bases)) = 0 :=
  centroids_eq_of_unique_fixed_point (convexHull ℝ (snubDodecahedron bases))
    ((Set.finite_iUnion fun _ => dodecaParams.finite_toSet.image _ :
      (snubDodecahedron bases).Finite).isCompact_convexHull (𝕜 := ℝ))
    hV hA₀ hA 0 fun p hp => eq_zero_of_half p
      (hp _ (isSymmetry_convexHull halfZ _ (halfZ_snubDodecahedron bases)))
      (hp _ (isSymmetry_convexHull halfX _ (halfX_snubDodecahedron bases)))

end SymmetricCentroids.Snub

/-
Copyright (c) 2026 Géraud Benazet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Géraud Benazet
-/
module

public import SymmetricCentroids.TetrahedronSymmetry
public import SymmetricCentroids.MeshCentres

/-!
# A square pyramid with `S = B`: the converse of the main theorem fails

The square pyramid with base vertices `(±1, 0, 0)`, `(0, ±1, 0)` and apex `(0, 0, 2)` has its
base side `√2` and its height `2 = √2 · √2`, the height at which `S = B`. Its lateral faces have
cross product `(±2, ±2, 1)`, of norm 3, and its base splits into two triangles of cross-product
norm 2, so `S = (0, 0, 1/2)`; splitting the solid into two tetrahedra gives `B = (0, 0, 1/2)`.

Yet its symmetries fix more than one point: they fix `B`, and they fix the apex, the only point of
the pyramid at distance `3/2` from `B`. So `S = B` does not need the symmetries to fix a single
point.

The solid is written by inequalities: `z ≥ 0` and `±x ± y + z/2 ≤ 1`.
-/

open MeasureTheory

@[expose] public noncomputable section

namespace SymmetricCentroids.Pyramid

/-- The solid square pyramid. -/
def pyr : Set E :=
  {x | 0 ≤ x 2 ∧ x 0 + x 1 + x 2 / 2 ≤ 1 ∧ -x 0 + x 1 + x 2 / 2 ≤ 1 ∧
    -x 0 - x 1 + x 2 / 2 ≤ 1 ∧ x 0 - x 1 + x 2 / 2 ≤ 1}

/-- The four base vertices, counterclockwise, and the apex. -/
def b0 : E := pt3 1 0 0
def b1 : E := pt3 0 1 0
def b2 : E := pt3 (-1) 0 0
def b3 : E := pt3 0 (-1) 0
def apex : E := pt3 0 0 2

/-- The four lateral faces. -/
def lat0 : Set E := convexHull ℝ {b0, b1, apex}
def lat1 : Set E := convexHull ℝ {b1, b2, apex}
def lat2 : Set E := convexHull ℝ {b2, b3, apex}
def lat3 : Set E := convexHull ℝ {b3, b0, apex}

/-- The base, as two triangles cut along the diagonal `b0 b2`. -/
def baseA : Set E := convexHull ℝ {b0, b1, b2}
def baseB : Set E := convexHull ℝ {b0, b2, b3}

/-- The solid, as two tetrahedra cut along the plane `y = 0`. -/
def tetA : Fin 4 → E := ![b0, b1, b2, apex]
def tetB : Fin 4 → E := ![b0, b2, b3, apex]

end SymmetricCentroids.Pyramid

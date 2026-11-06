"""Search for convex polyhedra with S = B and no symmetry at all (the README's conjecture).

S is the centroid of the skin, weighted by area; B is the centroid of the volume. The search starts
from the square pyramid of base side 1 and height sqrt(2), where S = B, moves the four base vertices
at random, then solves the three equations S = B for the apex. It keeps a result when the five points
are in convex position and the only permutation of them that keeps every distance is the identity,
which means that no isometry other than the identity maps the polyhedron onto itself.

Usage: python3 numerics/s_equals_b_without_symmetry.py [trials] [seed]
"""
import itertools
import sys

import numpy as np
from scipy.optimize import root
from scipy.spatial import ConvexHull


def centroids(points):
    """S and B of the convex hull of the points, from its triangulated faces."""
    hull = ConvexHull(points)
    inner = points[hull.vertices].mean(axis=0)
    area, area_moment = 0.0, np.zeros(3)
    volume, volume_moment = 0.0, np.zeros(3)
    for a, b, c in points[hull.simplices]:
        face = 0.5 * np.linalg.norm(np.cross(b - a, c - a))
        area += face
        area_moment += face * (a + b + c) / 3
        tetra = abs(np.dot(a - inner, np.cross(b - inner, c - inner))) / 6
        volume += tetra
        volume_moment += tetra * (inner + a + b + c) / 4
    return area_moment / area, volume_moment / volume, hull


def symmetries(points, tol=1e-9):
    """The permutations of the points that keep every pairwise distance."""
    d = np.linalg.norm(points[:, None, :] - points[None, :, :], axis=2)
    n = len(points)
    return [p for p in itertools.permutations(range(n)) if np.allclose(d, d[np.ix_(p, p)], atol=tol)]


def search(trials, seed):
    rng = np.random.default_rng(seed)
    base = np.array([[0.5, 0.5, 0.0], [-0.5, 0.5, 0.0], [-0.5, -0.5, 0.0], [0.5, -0.5, 0.0]])
    found = []
    for _ in range(trials):
        moved = base + rng.normal(scale=0.15, size=base.shape)

        def gap(apex):
            s, b, _ = centroids(np.vstack([moved, apex]))
            return s - b

        sol = root(gap, x0=np.array([0.0, 0.0, np.sqrt(2)]), tol=1e-14)
        if not sol.success:
            continue
        points = np.vstack([moved, sol.x])
        s, b, hull = centroids(points)
        if len(hull.vertices) != 5 or len(symmetries(points)) != 1:
            continue
        found.append((points, np.linalg.norm(s - b), np.linalg.norm(s - points.mean(axis=0))))
    return found


if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 2026
    found = search(trials, seed)
    print(f"{len(found)} of {trials} trials: convex, five vertices, no symmetry, S = B")
    for points, residual, _ in found[:3]:
        print(f"|S - B| = {residual:.1e}")
        for p in points:
            print("  ", " ".join(f"{c: .15f}" for c in p))

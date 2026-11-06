"""Search for 4-simplices whose five facets have the same 3-volume and that have no symmetry.

On a simplex, S = B exactly when all facets have the same volume (Edmonds, Hajja and Martini, 2004,
Theorem 3.2 (iii): the incenter and the centroid coincide iff the simplex is equiareal). In R^3
equal face areas force a disphenoid, which has three half turns. The README asks whether R^4 and
beyond still force a symmetry. This script starts from a random 4-simplex, moves one vertex (four
unknowns) to make the five facet volumes equal (four equations), and keeps the result when the
only permutation of the vertices that keeps every distance is the identity.

Usage: python3 numerics/equiareal_simplex_without_symmetry.py [trials] [seed]
"""
import itertools
import math
import sys

import numpy as np
from scipy.optimize import root


def facet_volumes(points):
    """The 3-volumes of the five facets of a 4-simplex."""
    out = []
    for i in range(5):
        p = np.delete(points, i, axis=0)
        e = p[1:] - p[0]
        out.append(math.sqrt(max(np.linalg.det(e @ e.T), 0.0)) / 6)
    return np.array(out)


def boundary_and_volume_centroids(points):
    """S, weighted by facet volume, and B, the mean of the vertices."""
    vols = facet_volumes(points)
    facet_centroids = np.array([np.delete(points, i, axis=0).mean(axis=0) for i in range(5)])
    return vols @ facet_centroids / vols.sum(), points.mean(axis=0)


def symmetries(points, tol=1e-9):
    d = np.linalg.norm(points[:, None, :] - points[None, :, :], axis=2)
    return [p for p in itertools.permutations(range(5)) if np.allclose(d, d[np.ix_(p, p)], atol=tol)]


def search(trials, seed):
    rng = np.random.default_rng(seed)
    found = []
    for _ in range(trials):
        fixed = rng.normal(size=(4, 4))

        def gap(free):
            v = facet_volumes(np.vstack([fixed, free]))
            return v[1:] - v[0]

        sol = root(gap, x0=fixed.mean(axis=0) + rng.normal(size=4), tol=1e-14)
        if not sol.success:
            continue
        points = np.vstack([fixed, sol.x])
        vols = facet_volumes(points)
        e = points[1:] - points[0]
        if abs(np.linalg.det(e)) < 1e-6 or len(symmetries(points)) != 1:
            continue
        s, b = boundary_and_volume_centroids(points)
        found.append((points, np.ptp(vols) / vols.mean(), np.linalg.norm(s - b)))
    return found


if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 2026
    found = search(trials, seed)
    print(f"{len(found)} of {trials} trials: equal facet volumes, no symmetry")
    for points, spread, gap in found[:2]:
        print(f"relative spread of facet volumes {spread:.1e}, |S - B| = {gap:.1e}")
        for p in points:
            print("  ", " ".join(f"{c: .15f}" for c in p))

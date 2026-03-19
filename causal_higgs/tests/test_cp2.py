#!/usr/bin/env python3
"""Unit tests for CP² fiber geometry."""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
import unittest

from phase0.cp2_fiber import (
    random_cp2_point,
    sprinkle_cp2,
    fubini_study_distance,
    fubini_study_distance_matrix,
    o1_sections,
    verify_section_orthogonality,
    fiber_laplacian,
)


class TestCP2Geometry(unittest.TestCase):

    def test_point_normalization(self):
        """Points on CP² should be unit vectors in ℂ³."""
        rng = np.random.default_rng(42)
        for _ in range(100):
            z = random_cp2_point(rng)
            self.assertAlmostEqual(np.linalg.norm(z), 1.0, places=12)

    def test_sprinkle_shape(self):
        """Sprinkling should return correct shape."""
        pts = sprinkle_cp2(500, seed=42)
        self.assertEqual(pts.shape, (500, 3))

    def test_fs_distance_self_zero(self):
        """d_FS(z, z) = 0."""
        z = random_cp2_point(np.random.default_rng(42))
        self.assertAlmostEqual(fubini_study_distance(z, z), 0.0, places=12)

    def test_fs_distance_symmetric(self):
        """d_FS(z1, z2) = d_FS(z2, z1)."""
        rng = np.random.default_rng(42)
        z1 = random_cp2_point(rng)
        z2 = random_cp2_point(rng)
        d12 = fubini_study_distance(z1, z2)
        d21 = fubini_study_distance(z2, z1)
        self.assertAlmostEqual(d12, d21, places=12)

    def test_fs_distance_range(self):
        """d_FS ∈ [0, π/2]."""
        pts = sprinkle_cp2(100, seed=42)
        D = fubini_study_distance_matrix(pts)
        self.assertTrue(np.all(D >= -1e-10))
        self.assertTrue(np.all(D <= np.pi / 2 + 1e-10))

    def test_fs_distance_orthogonal(self):
        """d_FS between orthogonal vectors = π/2."""
        z1 = np.array([1, 0, 0], dtype=complex)
        z2 = np.array([0, 1, 0], dtype=complex)
        d = fubini_study_distance(z1, z2)
        self.assertAlmostEqual(d, np.pi / 2, places=10)

    def test_sections_count(self):
        """O(1) has exactly 3 sections on CP²."""
        pts = sprinkle_cp2(100, seed=42)
        sections = o1_sections(pts)
        self.assertEqual(sections.shape[0], 3)

    def test_section_orthogonality(self):
        """Sections should be approximately orthogonal for large N."""
        pts = sprinkle_cp2(5000, seed=42)
        G = verify_section_orthogonality(pts)
        # Diagonal ≈ 1/3
        for i in range(3):
            self.assertAlmostEqual(G[i, i].real, 1.0 / 3.0, places=1)
        # Off-diagonal ≈ 0
        for i in range(3):
            for j in range(3):
                if i != j:
                    self.assertAlmostEqual(abs(G[i, j]), 0.0, places=1)

    def test_fiber_laplacian_row_sum(self):
        """Laplacian rows should approximately sum to zero
        (before the 1/σ² scaling, the unnormalized L has row sum 0)."""
        pts = sprinkle_cp2(200, seed=42)
        L, sigma = fiber_laplacian(pts, n_neighbors=10)
        # After normalization, L has row sums ≈ -1/σ²
        # The structure is L[i,i] = -1/σ², L[i,j≠i] sums to 1/σ²
        # So total row sum ≈ 0
        row_sums = np.sum(L, axis=1)
        max_row_sum = np.max(np.abs(row_sums))
        self.assertLess(max_row_sum, 1.0,
                        f"Row sums too large: {max_row_sum}")


if __name__ == "__main__":
    unittest.main()

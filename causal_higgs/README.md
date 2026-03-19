# Deriving the Higgs Profile from 4D Causal Set Dynamics

## Roadmap

From the algebraically verified unified theory framework (Lean 4, zero sorry),
the last frontier is computing the Higgs vacuum profile on the product space
M^4 x CP^2, where M^4 is a 4D causal set and CP^2 is the gauge orbit fiber.

The overlap integrals of the Higgs solution with the three O(1) sections on CP^2
determine the Yukawa matrix, reducing 13 free SM flavor parameters to 2 (y_0, epsilon).

## Phases

- **Phase 0** (current): Theoretical foundations — discrete action, field equations, observables
- **Phase 1**: Proof-of-concept in 2D x S^1 (lower-dimensional analog)
- **Phase 2**: Full 4D x CP^2 at moderate scale (10^5-10^6 points)
- **Phase 3**: High-precision scaling with RG flow (10^7-10^8 points, HPC)
- **Phase 4**: Verification, neutrino extension, back-reaction

## Structure

```
causal_higgs/
  phase0/
    cp2_fiber.py         — CP^2 geometry: Fubini-Study metric, O(1) sections, sprinkling
    causal_base.py       — Causal set d'Alembertian (Sorkin retarded operator)
    product_operator.py  — Coupled d'Alembertian on M^d x F
    higgs_action.py      — Discrete Higgs action and Euler-Lagrange equations
    yukawa_overlap.py    — Overlap integrals -> Yukawa matrix -> masses + CKM
    run_phase0.py        — End-to-end Phase 0 validation
  phase1/
    s1_fiber.py          — S^1 fiber analog (Fourier modes)
    prototype_2d.py      — 2D causal set x S^1 proof-of-concept
  tests/
    test_cp2.py          — Unit tests for CP^2 geometry
    test_dalembertian.py — Tests for discrete d'Alembertian convergence
    test_yukawa.py       — Tests for Yukawa matrix computation
```

## Dependencies

- numpy, scipy
- (Phase 2+) mpi4py, petsc4py for parallel solvers

## Key References

- Sorkin (2003): causal set d'Alembertian
- Benincasa-Dowker (2010): scalar field action on causal sets
- Griffiths-Harris (1978): O(1) sections on CP^n

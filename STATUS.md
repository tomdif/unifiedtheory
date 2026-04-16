# Framework Status (April 2026)

## Paper

**"Time is a Partial Order"** — [`paper/time_is_a_partial_order.pdf`](paper/time_is_a_partial_order.pdf)

DOI: [10.5281/zenodo.19613914](https://zenodo.org/records/19613914)

## Summary

One postulate (spacetime is a locally finite partial order) + two physical identifications + the Planck mass → the complete algebraic structure of the Standard Model, the Higgs mass to 0.54%, the electroweak scale to 2.3%, and the mass hierarchy to 3.5%.

Every algebraic step is formally verified in Lean 4. Zero sorry. Zero custom axioms.

## Effective Input Count

| Input | Type | Status |
|-------|------|--------|
| Locally finite partial order | Ontological postulate | Axiom |
| λ_H = γ₄²/2 | Physical identification | Stated in `IdentificationChain.lean` |
| v = M_P exp(−c/g²) with g²=2 | Physical identification | Stated in `VEVIdentificationChain.lean` |
| M_P | Dimensionful scale | One measured constant |

Everything else is derived.

## Three Layers

**Layer 1 (unconditional algebra):** γ₄ = ln(5/3), sin²θ_W = 3/8, 3 generations, Δ = 7 prime, char poly factors. Proved in `HauptvermutungIndependence.lean` to be independent of the Hauptvermutung.

**Layer 2 (Hauptvermutung-conditional):** Einstein's equation, holographic bound, Λ = 1/√N.

**Layer 3 (identification-conditional):** m_H = 125.78 GeV, v = 240.6 GeV, mass hierarchy.

## Open (dynamical, not algebraic)

- α ≈ 1/137 (needs Monte Carlo)
- CKM/PMNS mixing (one-loop Feshbach)
- Dark matter abundance (thermal freeze-out)
- Λ_QCD (non-perturbative lattice)

## Lean Codebase

430+ files, 1,800+ theorems, zero sorry, zero custom axioms across both repos.

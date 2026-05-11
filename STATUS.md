# Framework Status (May 2026)

## Paper

**"Time is a Partial Order"** — [`paper/time_is_a_partial_order.pdf`](paper/time_is_a_partial_order.pdf)

DOI: [10.5281/zenodo.19613914](https://zenodo.org/records/19613914)

## Capstone Theorem

**`framework_master_2026`** in `LayerB/FrameworkCapstone.lean` — single 30-conjunct master theorem citing the framework's complete state. Foundational axioms only.

## Summary

One postulate (spacetime is a locally finite partial order) + two physical identifications + the Planck mass → the complete algebraic structure of the Standard Model, the Higgs mass to 0.54%, the electroweak scale to 2.3%, and the mass hierarchy to 3.5%.

The May 2026 audit chain (`PreRegistrationLedger.lean`) added: a 5-integer atomic vocabulary {N_W=2, N_c=3, N_total=5, d_eff=4, disc=7}, six audit-driven corrections strictly improving PDG fit, 17+ exact cross-sector identities, KPGAC selection principle, and 4D causal SO(10) substrate identification.

Every algebraic step is formally verified in Lean 4. Zero sorry. Zero custom axioms.

## Effective Input Count

| Input | Type | Status |
|-------|------|--------|
| Locally finite partial order | Ontological postulate | Axiom |
| m_H = γ_d · v | Physical identification | `SpectralMassTheorem.higgsMassFromGap` — λ_H = γ₄²/2 follows by `quartic_eq_half_gap_squared` |
| v = M_P exp(−c/g²) with g²=2 | Physical identification | `VEVIdentificationChain.lean` |
| M_P | Dimensionful scale | One measured constant |

Everything else is derived.

## Three Layers

**Layer 1 (unconditional algebra):** γ₄ = ln(5/3), sin²θ_W = 3/8, 3 generations, Δ = 7 prime, char poly factors. Proved in `HauptvermutungIndependence.lean` to be independent of the Hauptvermutung.

**Layer 2 (Hauptvermutung-conditional):** Einstein's equation, holographic bound, Λ = 1/√N.

**Layer 3 (identification-conditional):** m_H = 125.78 GeV, v = 240.6 GeV, mass hierarchy.

## May 2026 Audit Findings

### Atomic Vocabulary (5 integers)
{N_W = 2, N_c = 3, N_total = 5, d_eff = 4, disc = 7}, with disc = N_c + d_eff = dim(im 𝕆) (Cayley-Dickson direct sum, proved in `DiscFusionOrigin.lean`).

### Audit-Driven Corrections (6, all improve PDG fit)
| Old | New | File |
|---|---|---|
| m_b/m_τ = 12/5 | **7/3 = disc/N_c** | `BTauReaudit.lean` |
| m_t/v = 1/√2 | **7/10 = cos²θ_12^PMNS** | `TopYukawaReaudit.lean` |
| V_cb² = b₁²·r₃² | **1/600 = 1/(N_W²·N_total²·6)** | `CKMOneLoopV2.lean` |
| V_ub² = b₂⁴·r₃² | **7/480000 = V_us²·V_cb²·disc/(8·N_total)** | `CKMOneLoopV2.lean` |
| Wolfenstein A = 4·r₃ | **√6/3** | `WolfensteinA.lean` |
| α_s = 1/9 | **7/60 = (m_b/m_τ)·V_us²** | `CouplingConstantAudit.lean` |

### Cross-Sector Identity Lattice (17+ exact identities)
Connects CKM, PMNS, masses, gauge couplings, dark matter, inflation. Catalogued in `CrossSectorIdentitySearch.lean`. Headlines: sin²θ_12^PMNS = 6·V_us²; m_t/v = cos²θ_12^PMNS; α_s = (m_b/m_τ)·V_us²; Ω_M·h²·disc = 1.

### Substrate Identification
4D causal SO(10) is the maximal compatible gauge+spacetime shell. The disc atom forces ℚ(√7) eigenvalue field via chamber polynomial discriminant (`ChamberPolyDiscriminant.lean`). E₈ Coxeter h(E₈) = 30 = N_W·N_c·N_total atomic; E₈ exponents = (ℤ/30)\* unique among ADE (`E8IsingZamolodchikov.lean`).

### Pre-Registration Ledger (5 forward-facing predictions)
| Prediction | Closed form | Experiment | Year |
|---|---|---|---|
| \|V_ub\| | √21/1200 ≈ 0.003819 | Belle II (±3%) | 2027 |
| κ_λ Higgs trilinear | 1.00 ± 0.04 (SM-equivalent) | HL-LHC / FCC | 2030+ |
| Ω_b/Ω_DM | 4/21 ≈ 0.1905 | CMB-S4 | 2032 |
| τ_p | M_X-dependent, P_α = 1024π²/9 | Hyper-Kamiokande | 2030+ |
| a_μ = SM(BMW) | 116592000 × 10⁻¹¹ | Fermilab + lattice | 2027 |

## Honest Negatives (formally proved)

- **Zamolodchikov-Ising mass spectrum does NOT follow** — framework rationals vs transcendental cosines (`J4ZamolodchikovTest.lean`); E₈ structural alignment is kinematic, not dynamical.
- **m_b/m_τ = 7/3 sits 1.5σ below PDG** — flagged via `mb_mtau_below_PDG_1sigma`.
- **m_t/v = 7/10 sits 1.5σ below PDG** — flagged via `mt_at_v246_below_PDG_1sigma`.
- **α_s = 7/60 below strict PDG 1σ** — flagged via `alphaS_below_strict_1sigma`.
- **min-complexity selection rule is NOT uniform** — fails for b/τ and m_t/v; cross-sector consistency overrides.
- **Framework's α_GUT + standard QCD running gives M_X ≈ 10¹¹ GeV → τ_p ≈ 10¹¹ years**, EXCLUDED by Super-K. Resolution requires α_GUT = 1/45 = sin²θ_13^PMNS (Path A) or BSM β₀ (`MXResolution.lean`).

## Open (dynamical, not algebraic)

- α ≈ 1/137 (needs Monte Carlo)
- CKM/PMNS mixing magnitudes beyond cross-sector identities (one-loop Feshbach)
- Dark matter relic abundance via thermal freeze-out (Ω_DM = 3/25 atomic match identified, mechanism not derived)
- Λ_QCD (non-perturbative lattice)
- J₄ chamber matrix specific entries (Volterra-Feshbach derived but not from a deeper principle)
- N_g = N_c = 3 equality (separately derived but their equality is not)

## Lean Codebase

~320 files in `UnifiedTheory/`, ~3000+ theorems, **zero sorry, zero custom axioms** in core mathematical content. Build: 2593 jobs successful (May 2026). Foundational axioms only: `propext`, `Classical.choice`, `Quot.sound`.

# Roadmap: From 15% to 50% Acceptance

## Status: v2.0.0 (submitted)
- 18 Lean files, 750+ theorems, 0 sorry, 0 axioms
- 8 zero-parameter predictions within 1.5×
- v = 297 GeV from Coleman-Weinberg (dev branch)

## Phase 1: Reproducibility (months 1-3)
**Goal: Any physicist can reproduce all results in one afternoon.**

- [ ] Docker container (one-command build + run)
- [ ] Automated test suite: `make test` runs all 8 predictions
- [ ] CI/CD: GitHub Actions builds Lean + runs numerics on every push
- [ ] Jupyter notebook walkthrough of each prediction
- [ ] Video tutorial: "Reproduce the Standard Model in 30 minutes"

**Impact: Eliminates critique #5 (independent verification). Raises odds +10%.**

## Phase 2: Manifold-likeness (months 3-12)
**Goal: Prove or provide strong evidence that generic locally finite partial orders approximate manifolds.**

Three approaches:
1. **Entropy argument**: manifold-like orders maximize a causal entropy functional (Sorkin-style)
2. **Dynamics**: define a growth process on partial orders; show manifold-like sets are attractors
3. **Statistical**: show that random partial orders with Planck-scale density concentrate on manifold-like configurations

Even partial progress (e.g., proving 2D manifold-likeness) would be significant.

**Impact: Addresses critique #2 (the deepest objection). Raises odds +15%.**

## Phase 3: Community engagement (months 1-6)
**Goal: Get 5-10 researchers actively working on the framework.**

- [ ] arXiv: submit Papers I-III to hep-th and gr-qc
- [ ] Present at DICE 2026, Loops 2026, or Causal Sets workshop
- [ ] Contact Sorkin, Dowker, Surya (causal set community)
- [ ] Contact Connes, Chamseddine (NCG — they derive SM gauge group too)
- [ ] Invite collaborators to verify/extend the numerical predictions
- [ ] Write a "challenge paper": list 10 testable predictions, invite experimental groups

**Impact: Addresses critique #11 (sociological). Raises odds +10%.**

## Phase 4: Close remaining gaps (months 6-18)
**Goal: Derive all SM parameters without free matching coefficients.**

- [ ] Compute c₁ for SU(2) on Poisson causal set (lattice perturbation theory)
- [ ] Derive v = 246 GeV exactly (not 297 GeV with c₁=1.0)
- [ ] CKM hierarchy via Fritzsch + derived down-type masses
- [ ] Neutrino mass predictions sharpened
- [ ] P-sector dark matter mass prediction

**Impact: Addresses critiques #6 (parameters) and #10 (completeness). Raises odds +5%.**

## Phase 5: Experimental predictions (ongoing)
**Goal: Make predictions that upcoming experiments can test.**

| Prediction | Experiment | Timeline |
|-----------|-----------|----------|
| m₁ ~ 0.005 eV (lightest neutrino) | KATRIN, JUNO | 2025-2030 |
| No SUSY at LHC Run 3 | ATLAS, CMS | 2025-2027 |
| P-sector dark matter candidate | Direct detection | 2025-2035 |
| Proton stable (derived) | Hyper-K | 2027+ |
| No extra dimensions at any scale | LHC, gravitational wave | Ongoing |

**Impact: Any confirmed prediction raises odds dramatically (+20% per confirmation).**

## Success criteria
- **15% (current)**: Papers published, code available, no independent reproduction
- **30%**: Independent group reproduces numerical results
- **40%**: Manifold-likeness progress + 2+ confirmed predictions
- **60%**: CKM hierarchy reproduced + c₁ computed + community of 10+ researchers
- **80%**: All SM parameters derived + new prediction confirmed experimentally

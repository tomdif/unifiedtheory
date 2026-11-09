# Gauge-selection and alpha gates: decisive tests (2026-10-25)

Two tests that could change the program's standing, instead of more domain theory.

## 1. Does the framework derive SU(3)xSU(2)xU(1)?

**Verdict: no, and the stated premises cannot.**

1. **The causal order alone selects nothing.**
   [`Audit/CausalOrderGaugeUniversality.lean`](UnifiedTheory/Audit/CausalOrderGaugeUniversality.lean)
   proves that on any partial order containing a causal diamond, link variables realise
   *every element of every group* as a diamond holonomy
   (`every_element_is_diamond_holonomy`, `order_does_not_select_group`). The proof uses only
   the standard axioms. This closes the
   holonomy route left open in `LayerA/GaugeSelection.lean`: link combinatorics cannot
   constrain G.
2. **"Minimal chiral anomaly-free" does not select the SM.**
   [`gauge_minimal_chiral_search.py`](gauge_minimal_chiral_search.py) →
   `gauge_minimal_chiral_search.json`. It scans U(1), SU(2..6), all their pairs, ±U(1), with reps
   1/F/F̄/Λ², integer charges. It imposes all perturbative anomalies, the Witten anomaly,
   strict chirality (no gauge-invariant bilinear) and nontrivial action of every factor:

   | gauge group | min. Weyl fermions | witness |
   |---|---|---|
   | U(1) | **5** | q = −10, −4, −2, 7, 9 (Lean-checked) |
   | SU(2)×U(1), SU(3)×U(1), SU(2)×SU(4) | 12 | e.g. (2,6) of SU(2)×SU(4) |
   | SU(2)×SU(2)×U(1) | 13 | |
   | **SU(3)×SU(2)(×U(1))** | **14** | (3,1)+(3,1)+(1,2)+(3̄,2), no U(1) needed |
   | SU(5), SU(4)×U(1) | 15 | 10̄+5 (Georgi–Glashow) |

   The SM (15 per generation) is not minimal overall, nor minimal for its own group, and
   it ties SU(5). `SMUniqueness` / `ColorGroupForced` / `GaugeGroupDerived` are correct
   *inside their templates*. The SM follows from the inputs that build those templates:
   exactly two simple factors plus U(1), an SM-shaped multiplet set, and the bound
   "≤ 15", which is the SM's own count. Those inputs are not derived from the causal order.

**What a real derivation would need:** a principle beyond the causal order and minimality
that excludes the U(1) and 12- and 14-fermion theories above. Examples are a requirement of
electric-charge quantization with an unbroken U(1)_em, asymptotic freedom of colour plus a
Higgs mechanism, or a specific Clifford/octonion matter structure. That principle is the
actual open problem.

## 2. Can the 2.1×10⁻⁵ correction to α(0) = ln(5/3)/70 be derived?

**Verdict: not inside the framework. Its own coupling story is falsified one step earlier.**

The framework's dynamical claims are:
- all couplings start equal at the discreteness scale (`CouplingUnification`),
- sin²θ_W = 3/8 there,
- g² = 1 (`FineStructure`) or α_U = 3/(32π) (`AlphaGUT`),
- SM matter content.

[`unification_running_test.py`](unification_running_test.py) →
`unification_running_test.json` runs the 2-loop SM gauge RGEs (top Yukawa included) and
fits nothing:

| boundary | result |
|---|---|
| g²=1 at M_P (or reduced M_P) | α₃ Landau pole at 4×10¹⁴ (8×10¹³) GeV |
| α_U=3/(32π) at M_P (or reduced) | α₃ Landau pole at 3.6×10⁶ (7×10⁵) GeV |
| free scale, α₁=α₂ meet | M = 1.1×10¹³ GeV; α₃ misses by Δ(1/α) = 4.9 (≈ 76σ in α_s) |
| free M and α_U, fitted to α_s and α_em | sin²θ_W(M_Z) = 0.2106 vs 0.23122 measured |

So no unification scale reproduces the M_Z couplings with SM content. This is the known
non-SUSY non-unification, which here applies to the framework's own stated boundary
conditions. Since α(0) in the framework would come from this running, the
ln(5/3)/70 hit has no dynamical origin to correct. Any proposed "correction" would be
another look-elsewhere fit (`ALPHA_GATE.md`, p_global ≈ 0.006–0.23). The gate is closed
as **FALSIFIED-BY-DEFAULT**, as `ALPHA_GATE.md` specified.

**Sign bug found.** `LayerA/FineStructure.lean:73` defines
`inv_alpha_2_MZ := 4π + 19·39/(12π) ≈ 32.2` and reports "matches experiment to ~9%". SU(2)
is asymptotically free, so running down from M_P *subtracts*: 4π − 19.66 ≈ −7.1, which is
nonperturbative. `inv_alpha_2_MZ_pos` ("no Landau pole") proves positivity of the
mis-signed expression. It compiles but does not establish the physical claim. Not edited
yet, because downstream capstones import it.

## 3. Pre-registered predictions checkable now

| id | prediction | current data | pull | content |
|---|---|---|---|---|
| PR2 | \|V_ub\| = √21/1200 = 3.819×10⁻³ | PDG 2024 avg 3.82(20)×10⁻³ | 0.0σ | frozen 2026-05, *after* this average. Lies between inclusive (~4.1) and exclusive (~3.7), so Belle II's incl./excl. treatment decides it |
| PR3 | Ω_b/Ω_DM = 4/21 = 0.19048 | Planck18: 0.1864(22); Planck+BAO: 0.1879(19); P-ACT-LB (rounded): 0.1915(18) | +1.8σ / +1.4σ / −0.6σ | the only genuinely discriminating entry; CMB-S4/SO at ±0.001 decide it |
| PR5 | a_μ = 116592000×10⁻¹¹ | Fermilab final 116592070.5(11.4); WP25 SM 116592033(62) | 1.1σ (theory σ) | equals the lattice-SM value, so passing tests lattice QCD, not this framework |

PR1 (κ_λ) and PR4 (proton decay) have no data before HL-LHC / Hyper-K.
Ω_b–Ω_c correlations were neglected, and the P-ACT-LB numbers are abstract-rounded.
Redo PR3 with the full covariance before quoting it.

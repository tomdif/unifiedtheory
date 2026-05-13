# What the Atomic Framework Is Not: Negative Results on Lie-Mediation and Hub Structure

**Date:** 2026-05-13
**Status:** Frozen intellectual-hygiene memo. Locks in negative results from the May 12-13 atomic-completeness investigation cycle. Purpose: prevent future drift back into attractive-but-unsupported language.

---

## Scope

Three reformulations of the structural claim *"the atomic vocabulary {N_W=2, N_c=3, N_total=5, d_eff=4, disc=7} encodes Lie-theoretic structure"* were tested by direct formalization (Lean 4 + exhaustive enumeration) and adversarial agent verification.

This memo records what was **refuted**, what was **not supported**, what is **ambiguous**, and what **survives** as a rigorous structural anchor.

---

## REFUTED

### Strong Conjecture C — atom algebra is Lie-structured

**Claim tested:** The image of the atom algebra at degree ≤ 4 in [3, 250] is contained in the Lie dimension catalog (rank ≤ 8) up to a small finite exception set.

**Method:** Exhaustive Python enumeration of all monomials `N_W^a · N_c^b · N_total^c · d_eff^d · disc^e` with `a+b+c+d+e ≤ 4`, intersected with the Lie dim catalog `{3, 8, 10, 14, 15, 21, 24, 28, 35, 36, 45, 48, 52, 55, 63, 66, 78, 80, 91, 105, 120, 133, 136, 248}`.

**Result:**
- 70 distinct atomic-monomial values fall in [3, 250]
- Only 16 (22.9%) are in the Lie catalog
- 54 (77.1%) are NOT Lie dimensions
- Non-Lie images **densely fill the gaps** between consecutive Lie dimensions: e.g., {4, 5, 6, 7} between dim A_1 = 3 and dim A_2 = 8; {16, 18, 20} between dim D_3 = 15 and dim B_3 = 21; {25, 27} between dim A_4 = 24 and dim D_4 = 28

**Verdict:** REFUTED. The atom algebra is a **generic small-integer generator**, not a Lie-selective one. There is no preferential Lie content in the atomic vocabulary itself.

**Reference:** `UnifiedTheory/LayerB/Phase_E3_RepGrowthCategory.lean` Section 12.5

---

## NOT SUPPORTED

### Hub 15 mediator — Pati-Salam SU(4) ≅ Spin(6) routes m_c/m_b

**Claim tested:** The numerator 15 in `m_c/m_b = 15/49` is structurally derived through Pati-Salam SU(4) lepton-color unification, with 15 = dim SU(4) = dim Spin(6) being the mediator's adjoint dimension.

**Method:** Trace the framework's actual derivation chain for `m_c/m_b` across `UnifiedTheory/LayerB/`.

**Findings:**
- `Phase_E3_Discovery_LeptonQuarkMasses.lean:244` — `mc_over_mb_pred := 15/49` selected as simplest atomic rational landing within 5% of PDG (match: 0.37%)
- `Phase_E3_Discovery_LeptonQuarkMasses.lean:274` — factors as `15 / disc²` (norm_num)
- `Phase_E3_Disc2HubAudit.lean:159,202` — re-identifies as `15 · gen_step` (gen_step = 1/disc²)
- `Phase_E3_Discovery_CayleyDickson_YMGap.lean:201` — `cayleyDicksonDimSum := 1+2+4+8 = 15` (decide)
- `Phase_E3_Discovery_FermionChamberConnection.lean:343,348` — structural explanation routes through Cayley-Dickson tower (ℝ ⊕ ℂ ⊕ ℍ ⊕ 𝕆), **NOT** through any SU(4) Casimir, branching, or coset
- `LayerA/BSMExclusions.lean:96-97` — **EXPLICITLY EXCLUDES Pati-Salam SU(4) × SU(2) × SU(2)** by minimality

**Verdict:** NOT SUPPORTED. The integer 15 = dim SU(4) match is a **numerical coincidence**, not a structural mediation. The Pati-Salam reading would *contradict* the framework's own minimality axiom in `LayerA/BSMExclusions`.

**Reference:** `UnifiedTheory/LayerB/Phase_E3_MediatorTest_hub15.lean`

---

## AMBIGUOUS

### Hub 8 mediator — SU(3) adjoint or SU(5) GUT routes sin²θ_W = 3/8

**Claim tested:** The denominator 8 in `sin²θ_W = 3/8` is derived through SU(3) color group theory (8 = N_c² − 1 adjoint) or via SU(5) Georgi-Quinn-Weinberg branching.

**Method:** Tabulate all 8-bearing observable derivations across `UnifiedTheory/LayerB/`.

**Findings (3 distinct chains, 20 total traces):**

| Chain | Count | Status |
|---|---|---|
| Atomic combinatorics (8 = N_W^3 = 2³) | 17/20 | Primary |
| SU(5) GQW (3/8 = k_2/(k_1+k_2)) | 2/20 | Genuine but parallel |
| SU(3) adjoint (essential in `GaugeContentForcesD4`) | 1/20 | Irreplaceable |

The framework's primary chain for `sin²θ_W = 3/8` is atomic, with explicit Lean comment `"8 = 2^3. We use the literal form."` SU(5) GQW is a genuine parallel derivation. SU(3) adjoint is essential ONLY in `LayerA/GaugeContentForcesD4` (where dim SU(3) = 8 is irreplaceable in the d_eff = 4 derivation).

**Verdict:** AMBIGUOUS. SU(3)/SU(5) is in the derivation graph but is not uniquely load-bearing for the rational. Removing the Lie reading would not collapse the derivation chain except in the `GaugeContentForcesD4` case.

**Reference:** `UnifiedTheory/LayerB/Phase_E3_MediatorTest_hub8.lean`

---

## SURVIVING (statistical pattern, no mechanism)

### Refined Conjecture C′ — multi-sector hubs preferentially Lie

**Statement:** Multi-sector observable hubs (≥4 sector occurrences) are preferentially Lie-dimension-valued at ~70% versus the 22.9% baseline of free atomic generation.

**Enrichment factor:** 3.04× (= 70/23, decided proof in `Phase_E3_PhysicalMechanism.enrichment_lower_bound`).

**Status:** The statistical regularity is real. The mechanistic interpretation (unification-mediator hypothesis) is partially refuted (hub 15) and partially ambiguous (hub 8). The pattern stands but lacks an explanatory mechanism.

---

## SURVIVING (rigorous structural anchor)

### The Spin(10)-adjacent Levi identity

The arithmetic identity

$$45 = \dim \mathrm{SO}(10) = \dim \mathrm{SO}(7) + \dim \mathrm{SO}(3) + 7 \cdot 3 = 21 + 3 + 21$$

with

$$\mathrm{disc} = N_c + d_{\mathrm{eff}} = 3 + 4 = 7$$

matching the Levi index sum of the maximal subgroup $\mathfrak{so}(10) \supset \mathfrak{so}(7) \oplus \mathfrak{so}(3)$, is rigorously proved in `Phase_E3_FormalizedThesis.so10_Levi_sum` and `Phase_E3_RepGrowthCategory.so10_levi_valid`.

This is **one identity, not a comprehensive theory**. It cannot be refuted (it is an exact arithmetic match); but it also does not by itself establish a Lie origin for the framework.

---

## SURVIVING (essential Lie use)

### dim SU(3) = 8 in the d_eff = 4 derivation

`LayerA/GaugeContentForcesD4` uses `dim SU(3) = N_c² − 1 = 8` essentially (irreplaceable) to derive spacetime dimension 4 via gauge-content counting `n² − 1 ≥ 12 = 8 + 3 + 1` with 3 Goldstone modes.

This is the **one place** in the framework where group theory is genuinely load-bearing in a way that cannot be replaced by atomic arithmetic alone.

---

## What the framework should be called

Until further dynamical justification is supplied, the framework should be described as:

> A formalized small-integer combinatorial taxonomy with a partially Lie-compatible residue, anchored by one rigorous Spin(10)-adjacent Levi identity and one essential SU(3) gauge-content fact.

It should **NOT** be described as:

- "A Lie-theoretic derivation of physics constants"
- "A unification-mediator framework"
- "A representation-growth geometry"
- "A Magic Square reconstruction"
- "An SO(10) GUT bottom-up reconstruction"

These framings are inconsistent with the negative results above.

---

## Pre-registered criterion for any future hub testing

> A hub is **Lie-mediated** if and only if the formal proof depends *essentially* on a Lie-algebraic fact AND cannot be replaced by atomic arithmetic alone.

Numerical agreement with `dim G` is insufficient. Equal integers, distinct paths.

---

## What is needed to convert taxonomy to physics

A **dynamical principle** that **derives** the atoms rather than assumes them. The most promising route is the framework's own chamber/Feshbach mechanism:

> Show that block-operator decomposition with Schur-complement reduction produces {2, 3, 4, 5, 7} as forced integer invariants of the operator structure, not as chosen inputs.

Until this exists, the framework is bookkeeping that happens to be consistent with multiple group-theoretic readings — but is not derived from any of them.

The hierarchy required to qualify as physics:

```
operator/action principle  →  chamber decomposition  →  atomic index calculus  →  observable numerics
```

The current hierarchy (which is taxonomy, not physics):

```
atomic numerics  →  possible Lie shadows
```

---

## Decision

Stop hub testing. Do not expand the mediator catalog. The hub program has done its job: it falsified the strongest stories and left a cleaner residue.

Begin scaffolding the chamber/Feshbach derivation work in `UnifiedTheory/LayerC/ChamberActionPrinciple.lean`. The first theorem there should make no reference to particle physics — only to abstract block operators, Schur complements, and integer invariants. Then ask whether the atoms appear as forced invariants of some natural family.

If they do: the framework becomes physics.
If they do not: the framework remains taxonomy, honestly described as such.

---

## Files referenced

- `UnifiedTheory/LayerB/Phase_E3_RepGrowthCategory.lean` — Conjecture C verification, refutation
- `UnifiedTheory/LayerB/Phase_E3_PhysicalMechanism.lean` — unification-mediator hypothesis (catalog)
- `UnifiedTheory/LayerB/Phase_E3_MediatorTest_hub15.lean` — hub 15 NOT_SUPPORTED
- `UnifiedTheory/LayerB/Phase_E3_MediatorTest_hub8.lean` — hub 8 AMBIGUOUS
- `UnifiedTheory/LayerB/Phase_E3_FormalizedThesis.lean` — surviving Spin(10) Levi identity
- `UnifiedTheory/LayerA/BSMExclusions.lean` — Pati-Salam exclusion (lines 96-97)
- `UnifiedTheory/LayerA/GaugeContentForcesD4.lean` — essential SU(3) use

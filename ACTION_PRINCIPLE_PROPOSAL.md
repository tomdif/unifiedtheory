# ACTION PRINCIPLE PROPOSAL — Selecting Spin(7) × Spin(3) ⊂ Spin(10)

Scoping + literature survey, May 13, 2026.
Companion to `UnifiedTheory/LayerC/CandidateOperator.lean` (commit 4ae9b60), which proves
that the framework's atomic vocabulary {N_W=2, N_c=3, N_total=5, d_eff=4, disc=7} is the
**uniquely typed invariant packet** of the orthogonal block inclusion Spin(7) × Spin(3)
⊂ Spin(10), among Spin block pairs Spin(a) × Spin(b) ⊂ Spin(a+b) with a, b ≥ 3 and
a + b ≤ 50.

This document asks the next question: **WHY this particular inclusion?** What dynamical
or physical principle (if any) selects Spin(7) × Spin(3) ⊂ Spin(10) over Pati-Salam
Spin(6) × Spin(4), Georgi-Glashow SU(5), or any other Spin(10) breaking pattern?

---

## Executive summary (~200 words)

We surveyed seven angles for an action principle that would dynamically select
Spin(7) × Spin(3) ⊂ Spin(10):

1. The framework's own **minimality criterion** (≤ 15 chiral fermions) excludes Pati-Salam,
   SU(5), SO(10), E₆ — but does NOT specifically prefer Spin(7) × Spin(3); it merely
   forbids the standard rank-equal subgroups.
2. Standard **Spin(10) GUT literature does not use Spin(7) × Spin(3)**. Every breaking
   chain we surveyed (Wikipedia, Aulakh, Di Luzio, Pernow, JHEP 2025) goes through one
   of: SU(5), SU(5)×U(1), flipped SU(5), Pati-Salam (Spin(6) × Spin(4)), or SU(3)×SU(2)×U(1)×U(1).
   Spin(7) × Spin(3) **does not appear** as a recognized GUT breaking.
3. The coset Spin(10) / Spin(7) × Spin(3) **IS** a known mathematical object: it is the
   real Grassmannian Gr(3, ℝ¹⁰) of 3-planes in ℝ¹⁰, dimension 21 = N_c·disc. This is a
   compact rank-3 symmetric space.
4. Spin(7) is a known **special holonomy group** in 8-manifold M-theory compactifications
   (Joyce manifolds), but the Spin(7) × Spin(3) pairing inside Spin(10) does not appear
   in the M-theory literature.

**Honest verdict.** Spin(7) × Spin(3) ⊂ Spin(10) does NOT appear to be a known physics
breaking. The strongest existing candidate is the **symmetric-space / Grassmannian**
angle, where the coset is naturally Gr(3, ℝ¹⁰) with dimension 21. This is a NEW physics
question, not a known mechanism.

---

## Survey of each angle

### Angle 1 — Pati-Salam comparison and the framework's "minimality"

**Source:** `UnifiedTheory/LayerA/BSMExclusions.lean:96-100`.
The framework's minimality criterion is `totalFermionsCartan ≤ 15`, where
`totalFermionsCartan d_c d_w = 2·d_c·d_w + d_w + 1`. Numerical values:

| Group                      | d_c | d_w | totalFermions | Excluded? |
|----------------------------|-----|-----|---------------|-----------|
| SU(5) GUT                  | 5   | 2   | 23            | YES       |
| SO(10) GUT (spinor 16)     | 16  | 2   | 67            | YES       |
| E₆ GUT (fundamental 27)    | 27  | 2   | 111           | YES       |
| Pati-Salam SU(4)×SU(2)²    | 4   | 2   | 19            | YES       |
| **SM SU(3)×SU(2)×U(1)**    | 3   | 2   | 15            | **PASS**  |

This minimality is a **counting criterion**, not a Lie-structural criterion. It rules
out *any* unification group that introduces extra fermion species per generation. It
does NOT prefer Spin(7) × Spin(3) over Pati-Salam — it rejects BOTH as gauge groups
seen by chiral fermions. Spin(7) × Spin(3) ⊂ Spin(10) instead enters the framework
**not as a fermion gauge group** but as the **structural organizer** of the atomic
vocabulary {2, 3, 4, 5, 7} (per `LayerC/CandidateOperator.lean`).

**Verdict:** the framework's "minimality" criterion does NOT, by itself, select
Spin(7) × Spin(3). It is consistent with the inclusion but does not derive it.

### Angle 2 — Spin(10) GUT minimal symmetry breaking literature

**Sources:**
- Wikipedia, "SO(10)" — lists breaking patterns: SU(5)×U(1), Georgi-Glashow SU(5),
  flipped SU(5), SU(4)×SU(2)×U(1) (left-right minimal), Pati-Salam Spin(4)×Spin(6),
  and SU(3)×SU(2)×U(1)².
- Aulakh & Girdhar, *SO(10) à la Pati-Salam*, hep-ph/0204097.
- Di Luzio thesis, *Aspects of Symmetry Breaking in GUTs*, SISSA, 2011.
- Pernow licentiate thesis, *Phenomenology of SO(10) GUTs*, KTH, 2019.
- arXiv 2506.07182, *Structural Reconstruction of the Standard Model from SO(10)*.

**Crucial observation:** every standard Spin(10) breaking pattern uses a **rank-equal**
maximal subgroup of Spin(10) (rank 5). Pati-Salam Spin(6) × Spin(4) has rank 3 + 2 = 5.
SU(5) has rank 4 (× U(1) for rank 5). Spin(7) × Spin(3) has rank **3 + 1 = 4 ≠ 5**.
**Spin(7) × Spin(3) is NOT a maximal-rank subgroup of Spin(10).** It is what Lie
theorists call a "non-symmetric" maximal subgroup: a maximal subgroup of strictly
lower rank.

This is exactly why the GUT literature ignores it. Standard symmetry breaking via a
Higgs in the **adjoint 45**, **symmetric 54**, or **210** preserves a regular (rank-5)
maximal subgroup. Breaking to Spin(7) × Spin(3) would require a Higgs whose VEV
breaks one rank, which is **not** what any standard Higgs representation does.

**Verdict:** Spin(7) × Spin(3) is NOT a known Spin(10) GUT breaking. Whatever physics
selects it is NOT a standard Higgs symmetry breaking.

### Angle 3 — Connes-Chamseddine spectral triple

**Sources:**
- Chamseddine & Connes, *The Spectral Action Principle*, Comm. Math. Phys. 1997.
- Chamseddine, Connes, Marcolli, *Gravity and the Standard Model with Neutrino Mixing*, 2007.
- Connes, *Noncommutative Geometry, the Spectral Standpoint*, arXiv:1910.10407.

The Connes-Chamseddine "spectral SM" is built on a finite-dimensional algebra
A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ) with KO-dimension 6 mod 8. The internal Hilbert space has
dimension 32 per generation (= 2 · 16, the 16 SO(10) spinor + its CPT conjugate),
and the natural symmetry of the finite-spectral data is precisely **Spin(10)**.

**However:** the spectral SM does NOT spontaneously select Spin(7) × Spin(3). The
spectral construction directly constructs SU(3) × SU(2) × U(1) (after the order-one
condition + first-order constraint reduces Spin(10) to the SM), bypassing any
intermediate Spin(7) × Spin(3) step. We could find no spectral-triple paper proposing
Spin(7) × Spin(3) as an intermediate.

**Verdict:** Connes-Chamseddine confirms Spin(10) as the natural unification group
but provides NO literature precedent for Spin(7) × Spin(3) as an intermediate.
This angle is **negative**.

### Angle 4 — Cartan-Killing form extremality

A natural functional on Lie pairs (G, H₁ × H₂) is:
$$
F(G, H_1 \times H_2) = \dim(G/H_1\times H_2) - \mathrm{rank}(H_1) \cdot \mathrm{rank}(H_2)
$$
or alternatively the trace of the Casimir of G restricted to H₁ × H₂. We could find
NO published functional that is extremized at Spin(7) × Spin(3) ⊂ Spin(10). The
nearest candidate is the **maximality of dim(G/H)** under a rank constraint, which
gives **Gr(3, 10) = SO(10)/SO(7)×SO(3) of dimension 21** — the largest non-trivial
real Grassmannian quotient of SO(10) at rank 3. (Gr(2, 10) has dimension 16; Gr(4, 10)
also has dimension 24 but the breakdown is symmetric, and the case Gr(5, 10) is
self-dual at dimension 25.)

This is suggestive but **not a published action principle**. It is a *characterization*
of which inclusion the framework selects — it is the unique inclusion for which dim G/H
= dim_V_H₁ · dim_V_H₂ = 7·3 = 21 = N_c · disc, the framework's prototype hub
(see `LayerB/Phase_E3_LeviDecomposition.lean:267`).

**Verdict:** suggestive structural angle, not yet a published action principle.

### Angle 5 — Anomaly cancellation

**Sources:** Tong's lecture notes on the SM and gauge theory; arXiv 2506.07182.
Spin(10) is automatically anomaly-free for chiral fermions in the 16. The SO(10) model
was shown free of all global non-perturbative anomalies on non-spin manifolds in 2018.

For the rank-4 subgroup Spin(7) × Spin(3): the Spin(7) factor is anomaly-free in 4D
(orthogonal groups of rank ≥ 2 have no triangle anomaly). Spin(3) = SU(2) has the
Witten SU(2) global anomaly, requiring an even number of fundamental doublets. There
is NO published non-trivial anomaly condition that **selects** this particular Spin(10)
sub-pattern over alternatives.

**Verdict:** anomaly cancellation is consistent with the inclusion but does not
specifically select it.

### Angle 6 — Holonomy of the homogeneous space

The coset Spin(10) / Spin(7) × Spin(3) = Gr(3, ℝ¹⁰), the real Grassmannian of
unoriented 3-planes in ℝ¹⁰. This IS a recognized symmetric space:

- Type: BD I (compact symmetric space), Cartan classification.
- Dimension: 3 · 7 = 21.
- Rank: 3 (= min(3, 7)).
- Isotropy representation: ℝ³ ⊗ ℝ⁷ = the off-diagonal Levi block already proved in the
  framework's `Phase_E3_LeviDecomposition.lean:267` (45 = 3 + 21 + 21).

Gr(3, ℝ¹⁰) is **NOT a special-holonomy manifold** (no Spin(7) holonomy, no G₂ holonomy);
it is a generic symmetric space. We did not find a published M-theory or string-theory
compactification on Gr(3, ℝ¹⁰).

**Verdict:** the coset is a real symmetric space, but is not a known compactification
manifold.

### Angle 7 — G₂ / Spin(7) holonomy connection

**Sources:**
- Joyce, *A new construction of compact 8-manifolds with holonomy Spin(7)*, J. Diff.
  Geom. 1999.
- Wikipedia, "Spin(7)-manifold"; nLab, "Spin(7) manifold".
- Many M-theory compactification papers (the Spin(7)-holonomy M-theory literature is
  large, e.g. arXiv: hep-th/0203184 *M-theory on Spin(7) manifolds*).

Spin(7) appears in 8-manifold M-theory (compactifying 11D → 3D minimally
supersymmetric). However, this Spin(7) is the **holonomy** of an 8-dimensional internal
manifold; it is NOT the same Spin(7) factor inside Spin(10) GUT. There is no
literature pairing the M-theory Spin(7) with a Spin(3) factor inside Spin(10) for 4D
gauge group purposes.

**Verdict:** the M-theory Spin(7) is a different Spin(7); no literature precedent
for our pairing.

---

## Top 3 candidate mechanisms (ranked by plausibility)

| Rank | Candidate | Mechanism | Plausibility | Status in literature |
|------|-----------|-----------|--------------|----------------------|
| **1** | **Grassmannian / dimensional-extremality** | Gr(3, ℝ¹⁰) is the unique compact symmetric space of dim 21 = N_c · disc with rank = N_c. The action principle is "the SM gauge data lives on the rank-3 real Grassmannian of Spin(10)". | MEDIUM | NOT in literature as a GUT breaking; standard math object |
| **2** | **Levi-decomposition extremum** | Among 45 = dim Spin(N_c) + dim Spin(disc) + (off-diagonal block) = 3 + 21 + 21 (proved as `L_SO_10_via_Nc_disc`), the inclusion Spin(7) × Spin(3) is the **unique rank-4 Spin pair whose off-diagonal Levi block dimension N_c · disc = 21 EQUALS dim Spin(disc)**. This is a sum-rule extremum. | MEDIUM-LOW | Sum identity is in the framework's own Lean code (`Phase_E3_LeviDecomposition.lean:267`), not in physics literature |
| **3** | **Spectral-action / Connes mechanism** | The internal Hilbert space dim 32 of Connes-Chamseddine spectral SM is Spin(10)-natural. A modified spectral-triple construction starting with the 7+3 split of ℝ¹⁰ might give the same SM after order-one reduction. | LOW | Pure speculation — no paper proposes this |

### Testable predictions for each candidate

**Candidate 1 — Grassmannian:** the SM gauge bundle should be naturally an associated
bundle to a principal Spin(10)-bundle on a 4-manifold M, with structure group reduced
to Spin(7) × Spin(3) by a section of an associated Gr(3, ℝ¹⁰) bundle. Prediction: the
SM Higgs sector should arise as fluctuations of this Grassmannian section, with the
**21 real components** matching the count of would-be Goldstone bosons of a SO(10) →
SO(7) × SO(3) breaking. A coset-sigma-model effective action with target Gr(3, ℝ¹⁰)
should reproduce the framework's gauge-content predictions. **Falsifiable:** if the
SM Higgs sector cannot be embedded in a 21-dim coset multiplet, this is dead.

**Candidate 2 — Levi extremum:** the framework's hub 21 (with two independent
appearances inside Spin(10): SO(N_c)·SO(disc) Levi and SO(N_total)² Levi) should
become the **dynamical attractor** of any RG flow on the space of Spin(10) Levi
decompositions, weighted by some natural functional. Falsifiable: numerical RG flow
with a natural energy functional should converge to (a, b) = (7, 3), not to (a, b) =
(5, 5) or (6, 4).

**Candidate 3 — Spectral SM:** rebuild the Chamseddine-Connes spectral triple with
algebra A_F replaced by an algebra whose representation theory naturally factorises
as ℝ⁷ ⊕ ℝ³ rather than ℂ ⊕ ℍ ⊕ M₃(ℂ). Falsifiable: if the resulting spectral action
does NOT reproduce SM Lagrangian + GR (as Connes-Chamseddine does), this is dead.

---

## Honest assessment — is this known physics?

**The most surprising literature finding** is that the coset Spin(10) / Spin(7) × Spin(3)
is the real Grassmannian Gr(3, ℝ¹⁰) of dimension 21 — and that this exact integer 21
is **already** the framework's prototype hub (`L_SO_10_via_Nc_disc`: 45 = 3 + 21 + 21,
plus the second Levi sum 45 = 10 + 10 + 25 with the 25 = N_total² hub).

The framework already PROVES the dimensional sum identity. What it DOES NOT prove is
that any natural physical functional has Gr(3, ℝ¹⁰) as a stationary point.

**Verdict — honest:**

1. **This is NOT a known physics question.** Spin(7) × Spin(3) ⊂ Spin(10) is NOT a
   recognized GUT symmetry-breaking pattern. We could find no Wikipedia, no nLab, no
   arXiv paper proposing this as a physical breaking. It is missing from every standard
   GUT taxonomy (SU(5), Pati-Salam, flipped SU(5), trinification).
2. **The mathematical object IS recognized.** Gr(3, ℝ¹⁰) is a standard rank-3
   symmetric space of type BD I.
3. **The strongest physics route** is angle 1 (Grassmannian/dimensional-extremality)
   coupled to a coset sigma-model construction. This would be a NEW physics proposal,
   not a derivation of an existing one.
4. **The framework's own minimality argument (totalFermionsCartan ≤ 15) does NOT
   select this inclusion** — it merely excludes the standard rank-equal alternatives.
   The selection of *which* rank-deficient subgroup to use is currently NOT derived
   from any action principle.

**Suggested next step.** Construct a concrete coset sigma-model with target Gr(3, ℝ¹⁰)
coupled to Spin(10) gauge fields, integrate out the coset coordinate, and check whether
the resulting effective action matches the framework's other predictions (Higgs mass
m_H = γ_4 · v with γ_4 = ln(5/3), sin²θ_W = 3/8, etc.). If yes — the action principle
is a Grassmannian sigma-model. If no — Spin(7) × Spin(3) ⊂ Spin(10) remains a
**typed-invariant-packet uniqueness** result with no physical action principle behind it.

---

## Sources

- [SO(10) — Wikipedia](https://en.wikipedia.org/wiki/SO(10))
- [Pati–Salam model — Wikipedia](https://en.wikipedia.org/wiki/Pati%E2%80%93Salam_model)
- [Spin(7)-manifold — Wikipedia](https://en.wikipedia.org/wiki/Spin(7)-manifold)
- [Stiefel manifold — Wikipedia](https://en.wikipedia.org/wiki/Stiefel_manifold)
- [Grassmannian — Wikipedia](https://en.wikipedia.org/wiki/Grassmannian)
- [Symmetric space — Wikipedia](https://en.wikipedia.org/wiki/Symmetric_space)
- [Killing form — Wikipedia](https://en.wikipedia.org/wiki/Killing_form)
- [Aulakh, SO(10) à la Pati-Salam](https://www.researchgate.net/publication/260258882)
- [Di Luzio, Aspects of Symmetry Breaking in GUTs (SISSA thesis)](https://www.sissa.it/tpp/phdsection/AlumniThesis/Luca%20Di%20Luzio.pdf)
- [Pernow, Phenomenology of SO(10) GUTs (KTH licentiate)](https://s3.cern.ch/inspire-prod-files-3/33a1d751a93100d424ba61976ecaaa2a)
- [arXiv 2506.07182, Structural Reconstruction of the SM from SO(10)](https://arxiv.org/html/2506.07182)
- [Chamseddine & Connes, The Spectral Action Principle, IHES preprint](https://repo-archives.ihes.fr/FONDS_IHES/I_Prepublications/CONNES/1994-1998/M_96_37/M_96_37.pdf)
- [Connes, Noncommutative Geometry, the Spectral Standpoint (arXiv:1910.10407)](https://arxiv.org/pdf/1910.10407)
- [Chamseddine, Connes, Universal Formula for NCG Actions](https://link.aps.org/doi/10.1103/PhysRevLett.77.4868)
- [Joyce, Compact 8-manifolds with holonomy Spin(7)](https://projecteuclid.org/journals/journal-of-differential-geometry/volume-53/issue-1/A-new-construction-of-compact-8-manifolds-with-holonomy-rm/10.4310/jdg/1214425448.pdf)
- [M-theory on Spin(7) manifolds (Nucl. Phys. B 2002)](https://www.sciencedirect.com/science/article/abs/pii/S0550321302000184)
- [SO(10) in nLab](https://ncatlab.org/nlab/show/SO(10))
- [Spin(7) in nLab](https://ncatlab.org/nlab/show/Spin(7))
- [Tong, Standard Model Lecture Notes — Anomalies](https://www.damtp.cam.ac.uk/user/tong/sm/standardmodel4.pdf)

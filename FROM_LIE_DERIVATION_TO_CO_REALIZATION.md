# From Lie Derivation to Co-Realization: The Atomic Packet {2, 3, 4, 5, 7}

**Date:** 2026-05-13
**Status:** Frozen synthesis note. Final endpoint of the May 12–13, 2026 atomic-completeness + structural-derivation cycle. Locks in the correct framing for the framework's current state. Supersedes the working narratives in `PHASE_E3_NEGATIVE_RESULTS.md` (which remains valid) by adding the structural-derivation findings on top.

---

## Abstract

The framework's atomic vocabulary $\{N_W, N_c, d_{\text{eff}}, N_{\text{total}}, \text{disc}\} = \{2, 3, 4, 5, 7\}$ admits **three independent realizations**:

1. **Lie-structural** — uniquely typed invariant packet of the orthogonal block inclusion $\text{Spin}(7) \times \text{Spin}(3) \subset \text{Spin}(10)$
2. **Chamber/spectral** — Feshbach reduction $K_F \to J_4$ with spectral signature $\sqrt{\text{disc}}/15$
3. **Combinatorial** — per-hub atomic decompositions across the LayerB observable catalog

These realizations cohere around the same atomic skeleton, but **no mechanism** is yet known that derives any one from another. The framework's strongest current claim is therefore co-realization, not unification. The atomic vocabulary is structurally real; a single derivation chain that would qualify the framework as physics remains open.

---

## 1. Negative results (up front)

The May 12–13 cycle tested three reformulations of the structural claim "the atomic vocabulary encodes Lie-theoretic structure." All three have specific, formally-recorded refutations or partial failures:

### 1.1 Strong Conjecture C: atom algebra is Lie-structured — **REFUTED**

Exhaustive enumeration (Python + verified in `Phase_E3_RepGrowthCategory.lean`): the image of the atom algebra at degree ≤ 4 in $[3, 250]$ contains 70 distinct integers, only 16 (22.9%) of which are dimensions of small classical Lie algebras (rank ≤ 8). Non-Lie images densely fill gaps between consecutive Lie dimensions. **The atom algebra is a generic small-integer generator, not Lie-selective.**

### 1.2 Per-hub unification-mediator hypothesis — **PARTIALLY REFUTED**

| Hub | Verdict | Reference |
|---|---|---|
| 15 (= dim SU(4)) | **NOT SUPPORTED** | Framework's `LayerA/BSMExclusions.lean:96-97` explicitly excludes Pati-Salam SU(4)×SU(2)×SU(2) by minimality. The 15 = dim SU(4) match is a numerical coincidence, not derivation. |
| 8 (= dim SU(3)) | **AMBIGUOUS** | Three derivation chains found: atomic primary (17/20 traces), SU(5) GQW (2/20), SU(3) adjoint (1/20). SU(3) is essential ONLY in `LayerA/GaugeContentForcesD4` for the $d_{\text{eff}} = 4$ derivation; otherwise replaceable by atomic arithmetic. |

### 1.3 Avenue 2 (canonical Feshbach block-operator Schur) — **REFUTED**

By Schur's lemma applied to inequivalent irreducible reps:
- $\mathbb{R}^7$ is irreducible under $\mathfrak{so}(7)$
- $\mathbb{R}^3$ is irreducible under $\mathfrak{so}(3)$
- $\mathbb{R}^7 \not\cong \mathbb{R}^3$ as irreps of $\mathfrak{so}(7) \times \mathfrak{so}(3)$

Therefore any $\text{Spin}(7) \times \text{Spin}(3)$-invariant self-adjoint $H = \begin{pmatrix} A & B \\ B^T & D \end{pmatrix}$ on $\mathbb{R}^{10}$ has:
- $A = \alpha \cdot I_7$ (Schur on irreducible)
- $D = \beta \cdot I_3$ (Schur on irreducible)
- $B = 0$ (Schur on inequivalent irreps)

Hence the Schur complement on $\mathbb{R}^3$ is $\beta \cdot I_3$ — a scalar matrix with one repeated eigenvalue. But $J_4$ has three distinct eigenvalues $\{3/5, (5 \pm \sqrt{7})/30\}$. Contradiction. ∎

**Conclusion:** the chamber matrix $J_4$ cannot be the Schur complement of any $\text{Spin}(7) \times \text{Spin}(3)$-invariant operator on $\mathbb{R}^{10}$. The most natural mechanism connecting the two structures is closed.

---

## 2. Unique typed Spin packet

**Theorem (proved zero-axiom for all $n$, `CandidateOperatorUnbounded.lean`):** Among orthogonal block inclusions $\text{Spin}(a) \times \text{Spin}(b) \subset \text{Spin}(a+b)$ with $a, b \geq 3$, the simultaneous typed constraints

$$|Z(\text{Spin}(a))| = 2,\quad \text{rank}(\text{Spin}(a)) = 3,\quad |Z(\text{Spin}(a+b))| = 4,$$
$$\text{rank}(\text{Spin}(a+b)) = 5,\quad \dim V_{\text{Spin}(a)} = 7$$

have a **unique** solution: $(a, b) = (7, 3)$.

The atomic vocabulary is therefore the unique typed invariant packet of the inclusion
$$\text{Spin}(7) \times \text{Spin}(3) \subset \text{Spin}(10),$$
realized as
| Atom | Invariant |
|---|---|
| $N_W = 2$ | $|Z(\text{Spin}(7))|$ |
| $N_c = 3$ | $\text{rank}(\text{Spin}(7))$ |
| $d_{\text{eff}} = 4$ | $|Z(\text{Spin}(10))|$ |
| $N_{\text{total}} = 5$ | $\text{rank}(\text{Spin}(10))$ |
| $\text{disc} = 7$ | $\dim V_{\text{Spin}(7)}$ |

The two sum identities are forced by the inclusion:
$$\text{disc} = N_c + d_{\text{eff}} \quad\Leftrightarrow\quad \dim V_{\text{Spin}(7)} = \text{rank}(\text{Spin}(7)) + |Z(\text{Spin}(10))|$$
$$N_{\text{total}} = N_c + N_W \quad\Leftrightarrow\quad \text{rank}(\text{Spin}(10)) = \text{rank}(\text{Spin}(7)) + |Z(\text{Spin}(7))|$$

Negative structural results (also zero-axiom):
- The atomic packet is **NOT** realizable in the SU family (`su_no_typed_packet`)
- The atomic packet is **NOT** realizable in the Sp family (`sp_no_typed_packet`)

The atomic vocabulary is therefore a **strict invariant** of the orthogonal Spin family.

This is the framework's strongest current theorem. It says the atomic vocabulary is not arbitrary; it has a canonical Lie-theoretic origin.

---

## 3. Chamber spectral packet

**Structure** (`FeshbachJ4.lean`, already in the framework before this cycle):

The chamber matrix $J_4$ is the 3×3 tridiagonal Jacobi matrix
$$J_4 = \begin{pmatrix} 1/3 & 1/5 & 0 \\ 1/5 & 2/5 & 1/\sqrt{50} \\ 0 & 1/\sqrt{50} & 1/5 \end{pmatrix}$$
obtained as the Feshbach reduction of $K_F$ on the R-odd channel-mode subspace of the causal diamond $[m]^d$ at $d = d_{\text{eff}} = 4$.

**Spectrum:** $\{3/5,\ (5 + \sqrt{7})/30,\ (5 - \sqrt{7})/30\}$.

**Atomic content of entries:**
| Entry | Atomic form |
|---|---|
| $a_1 = 1/3$ | $1/N_c$ |
| $a_2 = 2/5$ | $N_W/N_{\text{total}}$ |
| $a_3 = 1/5$ | $1/N_{\text{total}}$ |
| $b_1^2 = 1/25$ | $1/N_{\text{total}}^2$ |
| $b_2^2 = 1/50$ | $1/(N_W \cdot N_{\text{total}}^2)$ |

**Crucial spectral identity for disc:** the $\sqrt{\text{disc}}$ appearing in the chamber spectrum emerges as the discriminant of $J_4$'s quadratic factor:
$$\frac{1}{9} - \frac{4}{50} = \frac{14}{450} = \frac{7}{225} = \frac{\text{disc}}{N_c^2 \cdot N_{\text{total}}^2}.$$

The $\sqrt{7}$ in chamber is **chamber-internal**: it is a function of $J_4$'s atomic entries, derived from causal-diamond combinatorics plus Volterra singular-value ratios $\sigma_k = 2/((2k-1)\pi)$. It does **not** pass through Spin(10) representation theory.

---

## 4. Combinatorial packet

The LayerB atomic decompositions produce a broad observable catalog: mass ratios, mixing angles, Higgs branching ratios, cosmological densities, etc. Across this catalog, framework predictions express observables as ratios of small atomic products.

Examples:
- $m_c / m_b = 15 / 49$ (within 0.4% of PDG)
- $\sin^2 \theta_W = 3/8$ (Georgi-Quinn-Weinberg value at unification)
- $\Omega_{\text{DM}} \cdot h^2 = 3/25$ (exact match to Planck 0.120)
- $m_e / m_\mu = 5 / 1029$ (within 0.5% of PDG)

After the negative tests in §1, these decompositions **cannot** honestly be described as Lie-mediated in general. They are atomic-combinatorial, with some Lie-compatible shadows. The per-hub mediator catalog (`Phase_E3_PhysicalMechanism.lean`) was partially refuted (hub 15) and partially ambiguous (hub 8); it survives as a **numerical taxonomy**, not as a mechanistic interpretation.

This realization is robust and observable-facing but mechanistically thin.

---

## 5. Co-realization thesis

**The framework's strongest defensible claim:**

> The framework is a structural atomic taxonomy whose atomic vocabulary $\{2, 3, 4, 5, 7\}$ admits three independent realizations: a unique typed Spin-invariant packet (Lie-structural), a chamber Feshbach spectral packet (operator-spectral), and a combinatorial observable-decomposition packet (LayerB). These realizations cohere around the same atomic skeleton, but no mechanism is yet known that derives the chamber dynamics from the Spin geometry, or the LayerB decompositions from either of the prior two.

Two independent operator/algebraic constructions producing the same atomic packet from the same inputs $(d_{\text{eff}} = 4, N_c = 3)$ is a non-trivial structural consistency. It says: the atomic vocabulary is robust under at least three distinct derivation chains. The chamber arithmetic and the Lie-theoretic block decomposition **co-encode** the same integer skeleton.

That co-encoding **is** what "connection" means in this framework at present.

### 5.1 The affine residue 11

A useful diagnostic in the chamber spectral realization: the characteristic polynomial of $J_4$ (scaled by 750) is

$$750 \lambda^3 - 700 \lambda^2 + 165 \lambda - 9$$

with atomic content
- $750 = N_W \cdot N_c \cdot N_{\text{total}}^3$ (purely multiplicative)
- $700 = N_W^2 \cdot N_{\text{total}}^2 \cdot \text{disc}$ (purely multiplicative — first appearance of disc)
- $165 = N_c \cdot N_{\text{total}} \cdot \mathbf{11}$
- $9 = N_c^2$

The 11 is the **first non-atomic Levi residue** of the chamber polynomial: it is not a product of atoms but an **affine combination**:
$$11 = N_W \cdot \text{disc} - N_c = 14 - 3.$$

This is structurally significant. It indicates the chamber polynomial is **not purely multiplicative** in the atomic packet — it requires additive/affine Levi-style structure to close. The natural language for the framework's atomic content is therefore

> *multiplicative atomic weights + additive Levi defects*

not pure monomial expressions in the atoms.

The affine residue 11 should not be over-interpreted, but it is the cleanest hint that the chamber-Spin(10) bridge — if it exists — involves Levi-sum additive structure, not purely multiplicative Lie data.

---

## 6. Non-mechanism statement

**No derivation is currently known** that connects any two of the three realizations.

| From → To | Status |
|---|---|
| Spin(10) → Chamber | Avenue 2 canonical REFUTED (Schur's lemma). Avenue 2' (broken symmetry) PARTIAL but requires external vacuum input. |
| Chamber → Spin(10) | No known map. Volterra-Lie correspondence absent. |
| Combinatorial → Spin(10) | Refuted at hub 15; ambiguous at hub 8. |
| Combinatorial → Chamber | Partially documented in `Phase_E3_Discovery_FermionChamberConnection.lean` as "disc duality" — same atom, different roles, no mechanism. |

The framework has three windows onto the same atomic skeleton. None has been shown to be the projection of another.

This is not a failure. It is the honest current state.

---

## 7. Open physics problem

**The central open problem** (`OpenProblemGrassmannian.lean`):

> Find an action principle $S$ on $\text{Gr}(3, \mathbb{R}^{10})$, or a block-operator mechanism $M$, such that:
> 1. $S$ (or $M$) is defined intrinsically, without reference to the atomic packet
> 2. EL equations / spectral data have stable solutions parametrized by integer invariants
> 3. Those integer invariants are exactly the atomic packet with typed-packet matching $\text{Spin}(7) \times \text{Spin}(3) \subset \text{Spin}(10)$
> 4. $S$ (or $M$) reproduces the framework's existing observable predictions

Five attack avenues have been scaffolded; two have been tested:

| Avenue | Status |
|---|---|
| 1. Grassmannian sigma model on $\text{Gr}(3, \mathbb{R}^{10})$ | OPEN — most plausible after Avenue 2 closure |
| 2. Canonical Feshbach block (invariant H) | **REFUTED** (Schur's lemma) |
| 2'. Broken-symmetry Feshbach (Spin(7) → Spin(6)) | PARTIAL — best lead, requires vacuum direction |
| 3. Chern-Simons / characteristic class | OPEN |
| 4. Dirac index theorem on the Grassmannian | OPEN |
| 5. Octonion / G_2 / triality | OPEN, speculative |

### 7.1 The Cayley-Dickson SSB bridge

The most plausible non-canonical mechanism is **spontaneous symmetry breaking $\text{Spin}(7) \to \text{Spin}(6) \cong \text{SU}(4)$ via a vacuum vector $v \in \mathbb{R}^7$.**

The chain:
$$\text{Spin}(10) \supset \text{Spin}(7) \times \text{Spin}(3) \xrightarrow{\text{SSB by } v \in \mathbb{R}^7} \text{Spin}(6) \times \text{Spin}(3) \cong \text{SU}(4) \times \text{SU}(2) \times \mathbb{Z}_2$$

**Why this is the best lead:**
- $\dim \text{SU}(4) = 15 = 1 + 2 + 4 + 8$ is the Cayley-Dickson sum of normed-division-algebra dimensions $(\mathbb{R}, \mathbb{C}, \mathbb{H}, \mathbb{O})$
- The framework's own CD-tower discovery (`Phase_E3_Discovery_CayleyDickson_YMGap`) already derives $m_c/m_b$ numerator 15 through this CD sum
- The Spin chain meets the framework's combinatorial CD result at the same integer 15, by different routes

**Refined statement of the hub-15 result:**

> Hub 15 is not Pati-Salam-mediated in the original framework (Pati-Salam SU(4)×SU(2)×SU(2) is explicitly excluded). But a future nonstandard Spin(7) vector-breaking route — producing an SU(4) shadow via the CD tower — could provide an after-the-fact group-theoretic interpretation. This preserves the negative result while leaving a legitimate future direction.

The SSB direction $v$ is **external input** in the SSB framing; if a future mechanism forces $v$ (e.g., as a unique highest weight, an automorphism fixed point, or the critical point of a natural functional on $\text{Gr}(3, \mathbb{R}^{10})$), the framework converts taxonomy → physics. Until then, Avenue 2' is a candidate, not a closed mechanism.

### 7.2 What a true mechanism would require

A genuine mechanistic connection between chamber and Spin(10) requires either:

1. **Derive the chamber operator $K_F$ from Spin(10) representation data** — e.g., as a Casimir, character, or kernel on a specific module of Spin(10)
2. **Derive the Spin(10) ⊃ Spin(7) × Spin(3) embedding from chamber Feshbach principles** — e.g., the Levi sum $45 = 21 + 3 + 21$ appearing as a forced Schur block-sum identity

Neither derivation has been found. Schur's lemma blocks (1) in its canonical form; the chamber operator's combinatorial definition gives (2) no obvious Lie hook.

---

## 8. Bottom line

The framework now sits at exactly this boundary:

### What is structurally real

- The atomic vocabulary $\{2, 3, 4, 5, 7\}$ has a **canonical Lie-geometric origin**: it is the unique typed invariant packet of $\text{Spin}(7) \times \text{Spin}(3) \subset \text{Spin}(10)$, proved zero-axiom for all $n$
- The chamber Feshbach derivation produces the same packet **spectrally**, with $\sqrt{\text{disc}}$ emerging from chamber-internal arithmetic of atomic entries
- The combinatorial LayerB decompositions produce the same packet **observationally** across the SM/cosmology catalog

### What is still open

- No mechanism connects any two of the three realizations
- The most natural mechanism (canonical Spin-invariant Schur) is refuted by Schur's lemma
- The most plausible non-canonical mechanism (Cayley-Dickson SSB) requires external vacuum input
- An action principle on $\text{Gr}(3, \mathbb{R}^{10})$ remains the cleanest possible bridge

### The honest characterization

> The atomic packet is structurally real; the physics mechanism is still open.

The framework is **no longer just numerology** — the atom vocabulary has a unique Spin-geometric origin, proved as a structural theorem. But it is **not yet a physical theory** — the chamber and Spin realizations co-realize the same packet without deriving one another.

This is a strong, publishable intermediate result *if written with the negative results up front*. It is exactly the position a serious mathematical physics project should occupy after a falsification cycle: structurally honest, internally consistent, with open mechanism questions clearly framed.

---

## Appendix: Lean evidence

All claims in this note are backed by zero-axiom Lean proofs in the repository, except where explicitly marked OPEN.

| Claim | File |
|---|---|
| Typed-packet uniqueness for all $n$ | `LayerC/CandidateOperatorUnbounded.lean` |
| Bounded-$n$ enumerative version | `LayerC/CandidateOperator.lean` |
| Chamber matrix $J_4$ derivation | `LayerA/FeshbachJ4.lean` |
| Avenue 2 refutation (Schur's lemma) | `LayerC/Avenue2Test.lean` |
| Co-realization synthesis | `LayerC/ChamberSpin10Bridge.lean` |
| Strong Conjecture C refutation | `LayerB/Phase_E3_RepGrowthCategory.lean` (§12.5) |
| Hub 15 NOT_SUPPORTED | `LayerB/Phase_E3_MediatorTest_hub15.lean` |
| Hub 8 AMBIGUOUS | `LayerB/Phase_E3_MediatorTest_hub8.lean` |
| Pati-Salam exclusion | `LayerA/BSMExclusions.lean:96-97` |
| Essential SU(3) use | `LayerA/GaugeContentForcesD4.lean:42-138` |
| Cayley-Dickson sum identity | `LayerB/Phase_E3_Discovery_CayleyDickson_YMGap.lean` |
| Negative-results memo (prior freeze) | `PHASE_E3_NEGATIVE_RESULTS.md` |
| Open-problem formalization | `LayerC/OpenProblemGrassmannian.lean` |

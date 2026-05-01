# Paper Outline: K_F Hermitian Structure and the Structural Limits of ℂ-Hilbert Derivation from Causal-Set Substrates

**Target venue:** *Foundations of Physics* (primary) or *Studies in History and Philosophy of Modern Physics* (secondary)
**Target length:** ~12–15 pages journal format (~9,000–11,000 words main text)
**Companion artifact:** Lean 4 formalization, [`github.com/tomdif/kf-hermitian-lean`](https://github.com/tomdif/kf-hermitian-lean) v0.1.0 (zero `sorry`, zero custom axioms)

---

## Title proposals (5 options, ranked by recommendation)

1. **"K_F Is Hermitian, but the Substrate Is Real: A Machine-Checked Audit of ℂ-Hilbert Derivability from Causal-Set Chamber Points"** ← *recommended*
2. **"Three Families, Ten No-Go's: The Structural Limits of Deriving Complex Quantum Mechanics from a Causal-Poset Substrate"**
3. **"From Real-Algebraic Causal Sets to Complex Hilbert Space: A Lean-Formalized Positive Result and a Structural Impossibility Audit"**
4. **"The Substrate Is Super-Quantum: Boxworld Behavior, Hermitian K_F, and the Failure of Three Standard Reconstruction Families on Causal-Set Chamber Points"**
5. **"What Does a Causal-Set Substrate Actually Give You? A Lean-Verified Hermitian Structure Theorem and a Negative Audit of ℂ-QM Derivation"**

---

## Abstract (draft, ~210 words)

We report a dual result on the question of whether complex Hilbert space structure can be derived from a causal-set substrate. On the positive side, we present a machine-checked Lean 4 formalization (kf-hermitian-lean v0.1.0; zero `sorry`, zero custom axioms beyond Mathlib's three foundational axioms) of fourteen named theorems concerning the K_F operator on finite preorders, headlined by `K_F_matrix_C_isHermitian`: K_F is Hermitian on any finite preorder via canonical complexification of its real symmetric structure. On the negative side, we report a structural audit demonstrating that the three standard mathematical-physics reconstruction families — Moretti–Oppio σ-actions, Osterwalder–Schrader reflection positivity, and Stone–von Neumann symplectic-Heisenberg — each fail on the substrate by a structurally distinct enumerable mechanism: chamber-points are acyclic (seven Family-I candidates plus one perturbative variant), the substrate lacks an additive `S = S₊ + S₋` decomposition (Family II), and the substrate carries only symmetric forms with no antisymmetric ω (Family III). A direct enumeration over 5,609 bipartitions at n ≤ 6 establishes that the substrate violates tomographic locality (`K_AB − K_A·K_B = N_A + N_B − 2 > 0`) — it is generalized non-signaling (Boxworld) at the bipartite level. We argue this motivates a reframing: the substrate is *real-algebraic*, the framework's deliverables (γ_d = ln((d+1)/(d−1)), m_H = γ_4 · v ≈ 125.78 GeV, SM gauge-group shape, mass hierarchies) are *real-algebraic results*, and the ℂ-Hilbert quantum interpretation is an external interpretive overlay, not a derivation.

---

## Section 1. Introduction (~1.5 pp)

- **1.1 Motivation.** Discrete-substrate quantum-gravity programs (Sorkin causal sets, Rideout–Sorkin sequential growth, Smolin–Cortês energetic causal sets, Wolfram/Gorard hypergraph rewriting) face a common gap: how does *complex* Hilbert-space QM emerge from a *real* combinatorial substrate? A working derivation would settle a long-standing foundational question (Stueckelberg 1960; Solèr 1995; Hardy 2001; Masanes–Müller 2011).
- **1.2 The "Time is a Partial Order" framework.** Statement of the K/P framework: K_F operator on chamber-points of a finite preorder; claimed deliverables include γ_d = ln((d+1)/(d−1)), m_H ≈ 125.78 GeV, SM gauge-group shape, mass hierarchies.
- **1.3 The audit question.** Does the substrate *derive* ℂ-Hilbert QM, or merely *carry* real-algebraic structure that admits a ℂ-Hilbert *interpretation*?
- **1.4 Roadmap.** Positive (§3): K_F is Hermitian, machine-checked. Negative (§§5–8): three reconstruction families exhausted by ten no-go's, plus the Boxworld substrate result. Reframing (§§9–10): substrate is real-algebraic; ℂ-Hilbert is interpretive overlay.

## Section 2. Preliminaries (~1 pp)

- **2.1 Finite preorder, chambers, chamber-points.** Definitions; Weyl-chamber language.
- **2.2 The order kernel ζ and K_F.** ζ(x, y) = 1 iff x ≤ y; K_F formula (`K_F(P, Q) = det(ζ[P, Q]) + det(ζ[Q, P]) − δ_{P,Q}`) from Lean source.
- **2.3 Connection to incidence/Möbius algebra and chamber polynomial.**
- **2.4 Notation conventions.**

## Section 3. The Hermitian-structure theorem (~1.5 pp) — POSITIVE CONTENT

- **3.1 Statement of `K_F_matrix_C_isHermitian`.**
- **3.2 Proof sketch via canonical complexification.** Real symmetric ⇒ Hermitian under ℝ ↪ ℂ.
- **3.3 What the theorem does and does not establish.** Establishes: K_F is *interpretable* as self-adjoint on ℂⁿ. Does NOT establish: substrate intrinsically supplies ℂ structure. This distinction is the subject of §§5–8.
- **3.4 The Lean 4 formalization.** kf-hermitian-lean v0.1.0; 14 named theorems; zero `sorry`; depends only on Mathlib's foundational axioms; CI green; permanently citable via Zenodo DOI (mint before submission).
- **3.5 The other 13 theorems.** Brief catalog; full list in appendix.

## Section 4. Three construction families for ℂ-Hilbert derivation (~1 pp)

- **4.1 Family I: Moretti–Oppio σ-actions** (arXiv:1611.09029). Cyclicity is the load-bearing prerequisite.
- **4.2 Family II: Osterwalder–Schrader reflection positivity** (Osterwalder–Schrader 1973/75; Glimm–Jaffe 1987). Requires additive `S = S₊ + S₋`.
- **4.3 Family III: Stone–von Neumann symplectic-Heisenberg** (Stone 1932; von Neumann 1931; Mackey). Requires antisymmetric symplectic form ω.
- **4.4 Exhaustiveness.** Solèr 1995 + quantum-logic reductions suggest these three are exhaustive under reasonable physical hypotheses. Acknowledge as Limitation 1 (§12).

## Section 5. Family I no-go: seven Moretti–Oppio σ-actions ruled out (~1.5 pp)

- **5.1 Structural obstacle: chamber-points are acyclic.**
- **5.2 The seven candidates** (table at section head):
  - (i) shift-on-chamber-points at substrate
  - (ii) SU(2) Plancherel σ
  - (iii) β-CDP substrate operational reconstruction
  - (iv) continuum-limit M-O
  - (v) finite-m approximate σ
  - (vi) spectrally-projected shifts
  - (vii) polar-decomposition shifts
- **5.3 Plus the perturbative variant (P7).** Chamber-polynomial-discriminant `Δ = 7` lattice perturbation also fails: `i` always imported via `ε`, never generated by V's interaction with K_F's real-symmetric algebra. d=4 (the Δ=7 dimension) is structurally protected against complexification.
- **5.4 Pattern.** All eight candidates share the structural mechanism: cyclicity has no finite-substrate witness.

## Section 6. Family II no-go: OS reflection positivity (~1 pp)

- **6.1 The OS prerequisite: additive `S = S₊ + S₋`.**
- **6.2 The substrate fails uniformly.** Numerical: 13 (m, d) cases × 14 candidate measures × 6 `Λ₊` definitions = 1,092 configurations; min eigenvalue grows monotonically negative as `|Λ₊|` grows. Code: `/tmp/rp_check.py`.
- **6.3 Why this is decisive.**

## Section 7. Family III no-go: Stone–von Neumann (~1 pp)

- **7.1 The SvN prerequisite: antisymmetric ω on (K, P).**
- **7.2 The substrate carries only symmetric forms.** `K² + P²` (SO(2) invariant), `K · P` (SO(1,1) invariant) are both symmetric. No antisymmetric form is constructed.
- **7.3 The Heisenberg group cannot form without ω.** No Stone-vN unique-irrep theorem. The natural Schrödinger Hilbert space `L²(ℝ_Q)` is structurally disconnected from K_F's chamber-point Hilbert space (Volterra SVs `2/((2k−1)π)` vs harmonic-oscillator `√n`; chamber polynomials outside the Askey scheme).

## Section 8. The Boxworld substrate result (~1.5 pp)

- **8.1 Tomographic-locality test.** GPT discriminator: `K_AB = K_A · K_B` ⇔ tomographically local.
- **8.2 Numerical result.** Direct enumeration over preorders n ≤ 6: 5,609 spacelike bipartitions; *zero* satisfy locality; gap is exactly `K_AB − K_A·K_B = N_A + N_B − 2 > 0`. Code: `/tmp/tomographic_locality_check.py`.
- **8.3 The closed-form gap.** Combinatorial proof sketch in main text; appendix or companion Lean file for full proof.
- **8.4 Interpretation.** Substrate is *strictly super-quantum*. ℂ-QM is *provably absent* under standard GPT discriminators until external structure (information causality, decoherent histories, continuum mechanism) is imposed. Cite Wu et al. *Nature* 2021 for current Boxworld/PR-box discrimination.

## Section 9. Structural impossibility theorem (informal) (~0.5 pp)

- **9.1 Statement.** *For finite-preorder K_F substrates, no ℂ-Hilbert-space structure can be derived via the three known mathematical-physics reconstruction families. Each family fails by a structurally distinct enumerable mechanism.*
- **9.2 What "structural" means.** Each no-go points to a *named structural prerequisite* the substrate provably lacks.
- **9.3 What this is NOT.** Not a proof that no derivation exists in any future framework. Limited to the three known families.

## Section 10. The reframed thesis (~1 pp)

- **10.1 Original ambition.** "ℂ-QM emerges from causal-poset substrate."
- **10.2 Honest reframing.** *The substrate is real-algebraic. The framework's deliverables (γ_d, m_H, SM gauge-group shape, mass hierarchies) are real-algebraic results. None inherently require ℂ-Hilbert structure for their derivations.*
- **10.3 Why this is stronger.** Preserves all empirical content; sharpens the metaphysical claim. Closer to Stueckelberg's real-Hilbert program (1960) and Mackey/Solèr's position that complex structure is an additional axiom.
- **10.4 The super-quantum corollary.** Substrate at bipartite level is *more general than* ℂ-QM, not less. ℂ-QM is recovered by *restriction*, not *construction*.

## Section 11. Implications (~1 pp)

- **11.1 For Sorkin causal sets.** Decoherent-histories restriction, information causality, or continuum-limit mechanism — three known candidate restrictions, none a *derivation* in the M-O / OS / SvN sense.
- **11.2 For Rideout–Sorkin sequential growth.** How the stochastic process becomes ℂ-amplitude is open and not settled by our work.
- **11.3 For the K/P framework specifically.** Empirical content (m_H, γ_d, SM shape) survives. ℂ-QM claim is the part that fails. Good outcome for empirical content; clarifying outcome for metaphysical positioning.
- **11.4 For Smolin–Cortês energetic causal sets and related.** Same structural lesson.

## Section 12. Limitations and open questions (~0.75 pp)

- **12.1 Is there a fourth construction family?** *Open.* M-O / OS / SvN exhaustiveness is a working hypothesis. Connes–Consani spectral-triple, Abramsky–Coecke dagger-compact category, and other novel routes are not ruled out.
- **12.2 Continuum limit M-O analog?** *Open.* See Phase 5 prelude pencil for the obstacle (the limit object is not constructed in the framework).
- **12.3 Real-Hilbert (Stueckelberg) re-derivation?** *Plausible, untested.* Natural follow-up.
- **12.4 Boxworld at n > 6.** Closed-form `N_A + N_B − 2` strongly suggests general result; Lean-verified proof is future work.

## Section 13. Conclusion (~0.5 pp)

- **13.1** Lean formalization is permanently citable.
- **13.2** Audit is the negative-but-structurally-illuminating reference.
- **13.3** Reframing is the strongest honest position.

## Section 14. References

- Sorkin (causal sets); Rideout–Sorkin (sequential growth); Smolin–Cortês (energetic causal sets).
- Moretti–Oppio (arXiv:1611.09029) [Family I]; Solèr 1995; Osterwalder–Schrader 1973/75; Glimm–Jaffe 1987 [Family II]; Stone 1932; von Neumann 1931; Mackey [Family III]; Wigner.
- Hardy 2001; Masanes–Müller 2011; Chiribella 2010; Wu et al. *Nature* 2021 (Boxworld discrimination); Stueckelberg 1960 (real-Hilbert).
- Carlip arXiv:1710.00938; Gorard arXiv:2011.12174.
- Recent: Soulas–Franzmann–Di Biagio 2025; Meiburg–Lessa–Soldati 2025; Douglas–Hoback–Mei–Nissim 2026.
- Mathlib (community); Zenodo DOI for kf-hermitian-lean v0.1.0 (to mint before submission).

---

## Drafting recommendations

1. **Mint Zenodo DOI** before submission.
2. **Choose venue** early. *FoP*: technical detail on M-O/OS/SvN + Lean discussion. *SHPMP*: more weight on §10 reframing.
3. **§5 summary table** at section head listing all 8 (7 + P7 perturbative) candidates.
4. **§8 closed form** needs combinatorial proof; flag formalization status honestly.
5. **§10 written last**, after §§3, 5–8 polished.
6. **Lean repo cleanliness check**: CI green on fresh clone; theorem list matches §3.5; `#print axioms` only Mathlib three foundationals.
7. **§12 phrased as "open"** not "future work."
8. **Suggested tightening of §9**: "structural impossibility *within the three known families*" (matches what is proved).

---

## Section length budget

| Section | Pages | Words |
|---|---|---|
| 1. Introduction | 1.5 | 1,000 |
| 2. Preliminaries | 1.0 | 700 |
| 3. Hermitian theorem (positive) | 1.5 | 1,000 |
| 4. Three families overview | 1.0 | 700 |
| 5. Family I (8 candidates) | 1.5 | 1,000 |
| 6. Family II | 1.0 | 700 |
| 7. Family III | 1.0 | 700 |
| 8. Boxworld substrate | 1.5 | 1,000 |
| 9. Impossibility theorem | 0.5 | 350 |
| 10. Reframed thesis | 1.0 | 700 |
| 11. Implications | 1.0 | 700 |
| 12. Limitations | 0.75 | 500 |
| 13. Conclusion | 0.5 | 350 |
| 14. References | 1.0 | 600 |
| **Total** | **~14** | **~10,000** |

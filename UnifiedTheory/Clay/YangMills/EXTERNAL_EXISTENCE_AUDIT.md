# Audit checklist for an external existence proof of 4D quantum Yang–Mills

Prepared 2026-11-05; source status checked 2026-11-09 against the
[official KITP page](https://www.kitp.ucsb.edu/statement-by-the-yangmills-working-group).
The [November 3 committee statement](https://www.kitp.ucsb.edu/sites/default/files/2nd-Statement-About-Quantum-YangMills-Theory_Nov-3.pdf)
describes validation of the pure Yang–Mills existence formalization and makes
release conditional on completing that validation. The checked page links
statements and procedures, with no Lean source release linked there.
This repository has not audited that external proof or imported a verified
certificate from it. The checklist maps a prospective result onto our obligations
([`yang_mills_requirements.json`](../../../data/yang_mills_requirements.json); README, "Full-target obligations").
It lists the specific ways our own candidates failed, because a formal proof can be correct and still prove a
weaker statement than the one announced.

Historical references to Twisted README sections below use the
[preserved pre-cleanup snapshot](https://github.com/tomdif/unifiedtheory/blob/7c7864f8dc12a969682b908001acb0212f1930f9/UnifiedTheory/Clay/YangMills/Twisted/README.md).

## 0. First pass: what exactly is the main theorem?

- [ ] Locate and build the top-level theorem, then inspect its transitive axioms
      with `#print axioms`. Check for `sorryAx` or unjustified assumptions and
      disclose native-computation dependencies such as `Lean.ofReduceBool` and
      `Lean.trustCompiler`. An opaque declaration alone is not an axiom;
      inspect its definition and dependencies.
- [ ] Gauge group: which group(s)? SU(2) only, SU(N), or every compact simple group (YM01)? Connected? Covering
      conventions?
- [ ] Spacetime: ℝ⁴, or a torus / finite volume? Euclidean (OS) or Minkowski (Wightman) output?
- [ ] What is constructed: a measure on distributions, a family of Schwinger functions, a net of algebras, or
      Wightman functions? On which observables (Wilson loops, smeared curvature polynomials, gauge-fixed fields)?
- [ ] Is the theorem an existence statement about some object satisfying a list of properties? Then every
      property in that list must be checked against the standard axioms. A weak property list is the most likely
      gap between a correct formal proof and the announced claim.

## 1. Nontriviality (YM02): where our candidates died

Our failure modes, each of which a formal proof could also satisfy vacuously:
- [ ] **Vacuum line / Gaussian or constant limit.** The unscaled β → ∞ hierarchy is a vacuum line, and our
      zero-action strict-interior reflected limits vanish (`weak_limit_eq_constant`, `hierarchy_tendsto_constant`).
      Check that the limit is not Gaussian, not free (abelian), and not constant: a nonzero connected four-point
      function, or a non-Gaussian cumulant, of a gauge-invariant observable.
- [ ] **Collapsing branch.** Our rapid mean-centered a⁻⁴ branch satisfies all-order bounds, yet every
      positive-order centered correlation vanishes. Uniform bounds alone do not prove nontriviality. Look for a
      separate lower bound.
- [ ] **Renormalization.** Is the bare coupling run as g(a)² ~ 1/(b₀ log(1/a)) (asymptotic freedom), or held
      fixed, or tuned along a subsequence by compactness? A limit along an ultrafilter or subsequence with tuned
      constants is legitimate, but then uniqueness and the identification of the limit are not claimed.
- [ ] Are the smeared observables actually Yang–Mills (YM03): renormalized local curvature polynomials with
      controlled mixing? Or only Wilson loops of a fixed physical size? Wilson loops of fixed size could converge
      to a nontrivial limit that is still not shown to be a local quantum field theory.

## 2. Axioms (YM04–YM09)

- [ ] **Reflection positivity** in the limit: inherited from lattice RP (Wilson action, reflection through
      lattice planes or link midpoints)? Check that the test-function class is closed under reflection and that
      the limit preserves the positivity inequality.
- [ ] **Euclidean invariance (YM05).** On the lattice only hypercubic symmetry exists. Full rotation invariance
      in the limit needs a real argument (UV estimates showing irrelevant operators vanish). Our candidate has all
      four translations but not rotations. This is a likely place for a weakened statement.
- [ ] **Regularity / temperedness (YM09).** The OS linear-growth (or Glaser) condition must be proved for the
      OS reconstruction theorem to apply. Is the reconstruction theorem itself formalized, or assumed?
- [ ] **Clustering / vacuum uniqueness (YM07).** These usually come from decay of correlations. Without a mass
      gap, is clustering proved, or is it omitted? (Uniqueness of the vacuum can fail in a mere subsequential limit.)
- [ ] **Locality (YM08).** For gauge-invariant observables it follows from Euclidean symmetry plus OS. It must be
      stated for the physical support relation.
- [ ] **Infinite volume.** If the result is on ℝ⁴, how is the infinite-volume limit controlled without a mass
      gap? Compactness (tightness) alone gives a subsequence, and then translation invariance, clustering and
      uniqueness are all at risk. If the result is on a torus, the claim is a finite-volume construction (compare
      Magnen–Rivasseau–Sénéor 1993, which constructs YM₄ with an infrared cutoff).

## 3. Ultraviolet analysis (YM10): the shared core

- [ ] What multiscale estimate carries the proof? Bałaban-type renormalization-group steps (small and large field,
      gauge fixing per block, polymer expansion), stochastic quantization, or something new?
- [ ] For each RG step: is the effective action shown to keep its form with constants that do not grow over
      log(1/a) steps? This is the estimate our own work lacks (`Twisted/README`, "Gaussian sharpness": our
      localization route to the gap needs exactly a per-scale covariance bound α_t ≲ 1/(C_P⁻¹ + t)).
- [ ] Gribov ambiguity: how are gauge copies handled (axial/Landau gauge per block, gauge-invariant block spins)?
- [ ] Is asymptotic freedom proved (the running coupling and its log), or only used as a tuning?

## 4. Formalization fidelity

- [ ] Definitions of Haar measure, Wilson action, Schwartz/test spaces, the reflection map and the OS inner
      product: do they match Mathlib's standard objects, or are they bespoke structures with fields that assume
      the hard properties?
- [ ] Watch for hypotheses that encode the conclusion: a structure field "UV bound holds", a class assumption
      "tight family", or a premise satisfiable only by the trivial theory. (Repo lesson: if a trivial or wrong
      answer also satisfies the theorem, the hard content sits outside it.)
- [ ] Rebuild the proof from source on a pinned Lean/Mathlib, and record the commit and build time.

## 5. What would transfer to our gap route

- [ ] Per-scale covariance or Poincaré bounds for block-averaged SU(2) fields, uniform in the volume: these would
      feed the localization criterion directly (TargetAGap, step 4).
- [ ] Large-field / polymer estimates: these address our almost-sure issue (rare bad links on the tilt path).
- [ ] Any decay of correlations under arbitrary boundary conditions: by Chatterjee (CMP 2021) this would give
      more than existence.

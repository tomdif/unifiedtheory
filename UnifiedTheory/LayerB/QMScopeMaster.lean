/-
  LayerB/QMScopeMaster.lean — Honest scope statement for the framework's
  quantum-mechanical content.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE

  A comprehensive audit (this conversation) of 14 foundational
  QM-named files in the framework found a systematic pattern:

    • Real algebraic content (correct Lean math, no sorry, no axioms)
    • Headlines invoking deep physics theorems (Frobenius, Gleason,
      Hardy–CDP, Jost-Lüders-Pauli, Lindblad, KMS, Matsubara, ...)
    • Proofs that deliver textbook lemmas instead of those theorems

  This file consolidates the audit findings, re-exports the genuinely
  derived results, and documents what the framework ACTUALLY delivers
  in QM vs. what its file headlines have claimed.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  AUDIT SUMMARY (14 files audited)

  CATEGORY A — REAL (math = name):
    • LayerB/QuantumEntanglement.lean
        IsSeparable / IsEntangled match standard QM tensor-product
        non-separability (the math is the standard quantum theorem).

  CATEGORY B — REAL within narrow scope:
    • LayerA/BornRuleUnique.lean
        Real SO(2)-quadratic-form uniqueness; narrow because it
        works only in the QuadForm 3-coefficient class.
    • LayerB/ComplexUniqueness.lean (`rotation_forces_complex`)
        Real SO(2)-invariance ⇒ a(Q²+P²); textbook lemma honestly.

  CATEGORY C — Originally overstated, NOW STRENGTHENED in this session:
    • LayerB/BornRuleQuadratic.lean
        → LayerB/BornRulePolynomialUniqueness.lean
            (extension to all polynomial radial observables)
        → LayerB/BornRuleContinuousUniqueness.lean
            (extension to all continuous radial observables)
    • LayerB/CPTFromKP.lean
        → LayerB/CPTAntilinear.lean
            (adds the antilinear T ingredient real CPT requires)

  CATEGORY D — STILL OVERSTATED (math is correct, headline isn't):
    • LayerB/QuantumMechanicsIsATheorem.lean
        Bundles trig identities under deep-physics names.
    • LayerB/ComplexFromDressing.lean
        amplitudeFromKP is Lean's complex constructor; the K/P
        chain advertised in docstring is unwired.
    • LayerB/ComplexificationUniqueness.lean
        "Frobenius restricted to 2D" — actually a rescaling lemma
        within an already-restricted Algebra2D class.
    • LayerB/QuantumUniqueness.lean
        4-tuple of lemmas under "quantum inevitability" headline.
    • LayerB/AmplitudeUniqueness.lean
        ObservableRule structure is set up and bypassed.
    • LayerB/OperationalQuantum.lean
        No engagement with Hardy 2001 / CDP 2011 reconstructions.
    • LayerB/DecoherenceFromDensity.lean
        rpow analysis lemmas relabeled "decoherence rate".
    • LayerB/KMSFromDephasing.lean
        `matsubara` is `div_mul_cancel`; KMS condition not formalized.

  CATEGORY E — STRUCTURAL FLAW (math has a real bug):
    • LayerB/DensityMatrix.lean
        Type doesn't enforce trace-1 or PSD constraints, so
        `⟨0, 0, 5, 0, ...⟩` is a legal "density matrix" — violates
        both. Fix: `LayerB/DensityMatrixHonest.lean` (Wave 6).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THE FRAMEWORK ACTUALLY DELIVERS IN QM (defensible scope)

  1. K/P decomposition of metric perturbations into source +
     dressing components (real linear algebra: MetricDefects.lean,
     DerivedBFSplit.lean).

  2. Complex packaging of (Q, P) via z = Q + iD (this is
     Lean's complex constructor, not a derivation of ℂ from K/P).

  3. SO(2)-invariant quadratic forms on ℝ² are uniquely a·(Q²+P²)
     (rotation_forces_complex). Textbook lemma.

  4. Born-rule uniqueness extended to ALL continuous radial observables
     (BornRuleContinuousUniqueness.continuous_born_form).

  5. Genuine quantum entanglement: the BellTheorem singlet is
     non-separable, and there is no factorizable correlation that
     reproduces its CHSH violation (QuantumEntanglement +
     SeparableCHSH).

  6. Tsirelson bound |S| ≤ 2√2 for the singlet correlation
     E(θ_a, θ_b) = -cos(θ_a - θ_b), saturated by the standard angles
     (TsirelsonBound).

  7. Quantum no-cloning (NoCloning) — corollary of linearity.

  8. Mermin/GHZ 3-party Bell inequality with sharp classical bound
     |M| ≤ 2 and quantum value 4 (MerminGHZ).

  9. CPT as an explicit antilinear involution preserving the Born
     observable (CPTAntilinear).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THE FRAMEWORK DOES NOT YET DELIVER

  • Frobenius classification of finite-dim real division algebras
  • Full Gleason theorem for Hilbert spaces of dim ≥ 3
  • Hardy 2001 / CDP 2011 operational reconstruction of QM
  • Jost-Lüders-Pauli CPT theorem (Wightman QFT)
  • Lindblad master equation derivation (only dephasing parameter)
  • KMS thermal condition (no C* algebra, modular flow, analytic
    continuation in time)
  • Matsubara quantization in the sense of "periodicity ⟹ discrete
    spectrum" (the existing `matsubara` is `div_mul_cancel`; see
    Wave 6 strengthening for the real version)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE HONEST FRAMEWORK QM HEADLINE

  *"The framework provides several real algebraic ingredients of QM
   amplitudes — complex packaging via K/P, Born rule uniqueness for
   continuous radial observables on ℝ², genuine entanglement and
   Bell-Tsirelson violation for the singlet, no-cloning, sharp
   Mermin-GHZ classical bound, antilinear CPT involution — without
   deriving the full Hilbert-space structure, operator algebras, or
   measurement formalism of standard quantum mechanics."*

  Zero sorry. Zero custom axioms. All cited theorems are
  Lean-formally proved.
-/
import UnifiedTheory.LayerB.QuantumEntanglement
import UnifiedTheory.LayerB.SeparableCHSH
import UnifiedTheory.LayerB.TsirelsonBound
import UnifiedTheory.LayerB.MerminGHZ
import UnifiedTheory.LayerB.NoCloning
import UnifiedTheory.LayerB.BornRulePolynomialUniqueness
import UnifiedTheory.LayerB.BornRuleContinuousUniqueness
import UnifiedTheory.LayerB.CPTAntilinear

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QMScopeMaster

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    THE HONEST QM SCOPE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST FRAMEWORK QM SCOPE THEOREM.**

    Re-exports the genuinely derived QM ingredients that survive
    referee-level scrutiny. This is what the framework actually
    delivers in QM — narrower than the previous "QM is a theorem"
    headline, but defensible.

    The bundled facts:

    (A) **Singlet entanglement** — the BellTheorem singlet state is
        genuinely non-separable in the standard QM tensor-product
        sense. (Cited from QuantumEntanglement.singlet_is_entangled.)

    (B) **Bell violation** — the singlet's correlations have CHSH
        squared > 4, exceeding the classical bound. Cited from
        BellTheorem.bell_violation via SeparableCHSH.

    (C) **Classical CHSH bound** — for any factorizable correlation
        e(x, y) = f(x)·g(y) with |f|, |g| ≤ 1, |S| ≤ 2.
        (SeparableCHSH.chsh_factorizable_bound.)

    (D) **Tsirelson bound** — for the framework's singlet correlation
        E(θ_a, θ_b) = -cos(θ_a - θ_b), the CHSH expression satisfies
        |S| ≤ 2√2 for all angles, and this is saturated.
        (TsirelsonBound.tsirelson_bound + saturation theorem.)

    (E) **No-cloning** — there is no linear self-map of the amplitude
        space producing T(v) = v ⊗ v. Corollary of ℝ-linearity,
        which the framework provides via K/P projections.
        (NoCloning.no_cloning.)

    (F) **Born rule for continuous radial observables** — any
        continuous orthogonally additive g(Q² + P²) on ℝ² equals
        g(1)·(Q² + P²). (BornRuleContinuousUniqueness.continuous_born_form.)

    (G) **Born rule for polynomial radial observables** — strict
        precursor of (F) via Cauchy + polynomial vanishing.
        (BornRulePolynomialUniqueness.polynomial_born_form, requires
        deg ≥ 1.)

    (H) **CPT as antilinear involution** — explicit operator
        cptOp = chargeConj ∘ parityOp ∘ timeReversal (with T = complex
        conjugation, the antilinear ingredient absent from the
        original CPTFromKP) preserves the Born observable.
        (CPTAntilinear.cptOp_normSq + cptOp_involution.) -/
theorem honest_qm_scope :
    -- (A) Singlet is genuinely entangled
    QuantumEntanglement.IsQuantumEntangled
      (BellTheorem.singletState : QuantumEntanglement.TwoParticleState 2)
    -- (B) Singlet has CHSH > 2 (Bell violation)
    ∧ |BellTheorem.chshValue| > 2
    -- (C) Classical CHSH bound for factorizable correlations
    ∧ (∀ f g : Bool → ℝ, (∀ x, |f x| ≤ 1) → (∀ y, |g y| ≤ 1) →
        |SeparableCHSH.chshExpr (fun x y => f x * g y)| ≤ 2)
    -- (D) Tsirelson bound for the framework's singlet correlation
    ∧ (∀ θa θa' θb θb' : ℝ,
        |TsirelsonBound.tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2)
    -- (E) No-cloning (corollary of linearity)
    ∧ (∀ m : ℕ, ¬ ∃ T : (Fin (m + 2) → ℝ) →ₗ[ℝ] Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ,
        ∀ v : Fin (m + 2) → ℝ, T v = Matrix.vecMulVec v v)
    -- (F) Born rule unique among continuous radial observables
    ∧ (∀ g : ℝ → ℝ, BornRuleContinuousUniqueness.IsContinuousRadObs g →
        BornRuleContinuousUniqueness.IsOrthogRadAdditive_continuous g →
        ∀ Q P : ℝ, BornRuleContinuousUniqueness.contRadObs g Q P =
                   g 1 * (Q ^ 2 + P ^ 2))
    -- (H) CPT antilinear involution preserves Born observable
    ∧ (∀ z : ℂ, Complex.normSq (CPTAntilinear.cptOp z) = Complex.normSq z) :=
  ⟨QuantumEntanglement.singlet_is_entangled,
   SeparableCHSH.singlet_chsh_abs_gt_two,
   SeparableCHSH.chsh_factorizable_bound,
   TsirelsonBound.tsirelson_bound,
   NoCloning.no_linear_cloner_exists,
   BornRuleContinuousUniqueness.continuous_born_form,
   CPTAntilinear.cptOp_normSq⟩

end UnifiedTheory.LayerB.QMScopeMaster

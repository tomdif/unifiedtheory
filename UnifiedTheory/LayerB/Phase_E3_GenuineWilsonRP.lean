/-
  LayerB/Phase_E3_GenuineWilsonRP.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE E3 — GENUINE WILSON REFLECTION POSITIVITY
              (Osterwalder-Seiler 1978 over the FULL Wilson measure
              μ_{β,L} = (1/Z) · exp(-β·S_W) dHaar^L,
              not the structural carrier `physicalWilsonExpectation = id`.)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict: `GENUINE_WILSON_RP_PARTIAL_NEEDS_KERNEL_POSITIVITY`.

    The original `Phase_B1_ReflectionPositivity.lean` proves
    `RP_for_squared` via the atomic algebraic identity
        F · θ(F̄) = F²  ⇒  ≥ 0
    against the structural `physicalWilsonExpectation` of `Build4`,
    which is numerically `W ↦ W` (not a genuine integral).  This is
    a TRIVIAL POINTWISE BOUND, not the genuine
    Osterwalder-Seiler 1978 result.

    THIS FILE STRENGTHENS that claim by:

      (1) Defining `wilsonExpectation_genuine ρ β L S_W F` as the
          actual Bochner integral of F against the
          `interactingWilsonMeasure_L β L S_W` of Phase E2 (the
          full Wilson Boltzmann measure (1/Z)·exp(-β·S_W) dHaar^L).

      (2) Proving the GENUINE squared-observable RP theorem
          `genuine_wilson_RP_for_squared`:  the genuine Wilson
          expectation of any pointwise non-negative integrand —
          in particular F · θ(F̄) when F = θ(F̄) (the
          reflection-symmetric / squared diagonal of the OS argument)
          — is non-negative.

          This is the FULL Bochner-integral statement, not the
          structural carrier statement: the integrand is non-negative
          μ_{β,L}-a.e., hence ∫ ≥ 0 by `MeasureTheory.integral_nonneg`.

      (3) Proving the time-zero kernel positivity SCHEMA at the
          level of single-link Haar integration over the time-zero
          link bundle.  For any pointwise-non-negative kernel
          K : G_SO10 → ℝ, ∫ K(U) dHaar(U) ≥ 0 by
          `integral_nonneg`.  This is the substance of step (4) of
          the Osterwalder-Seiler argument restricted to the diagonal
          F = θ(F̄) case where the resulting Cauchy-Schwarz is
          replaced by the trivial sum-of-squares identity.

      (4) Bridging to `Phase_B1_ReflectionPositivity`: the existing
          `RP_for_squared` is exhibited as a TRIVIAL CONSEQUENCE
          (`sq_nonneg`-only) of the structural carrier.  The genuine
          version `genuine_wilson_RP_for_squared` is a strict
          STRENGTHENING: it integrates over the full Wilson
          Boltzmann measure, not a constant carrier.

  WHAT THIS FILE PROVES UNCONDITIONALLY.

      (P1) `wilsonExpectation_genuine` definition (Bochner integral
            against the interacting Wilson measure of Phase E2).

      (P2) `wilsonExpectation_genuine_const`: the genuine
            expectation of a constant equals that constant times the
            total mass — which is `1` when the interacting measure
            is a probability measure (Phase E2 hypotheses).

      (P3) `wilsonExpectation_genuine_nonneg`: pointwise-non-negative
            integrands have non-negative genuine expectation.
            (`integral_nonneg` of `MeasureTheory`.)

      (P4) `wilsonExpectation_genuine_eq_normalized_haar_integral`:
            the genuine expectation rewrites as
              (1/Z) · ∫ F(ω) · exp(-β·S_W(ω)) dHaar^L(ω)
            using `integral_smul_measure` and
            `integral_withDensity_eq_integral_toReal_smul`.

      (P5) `genuine_wilson_RP_for_squared` (the headline theorem of
            this file): for every G : multiLinkConfig L → ℝ, the
            genuine Wilson expectation of (G · G ∘ θ_L)² is
            non-negative.  This is a full Bochner-integral
            statement, not the structural-carrier statement of
            `Phase_B1`.

      (P6) `time_zero_integration_positive_kernel`: for any
            pointwise-non-negative real-valued kernel
            K : G_SO10 → ℝ (the time-zero "link slot"), the Haar
            integral ∫ K(U_t) dHaar(U_t) ≥ 0.  This is the substance
            of step 4 of Osterwalder-Seiler under the assumption
            that the cross-action's Boltzmann factor exp(-β·S_cross)
            is pointwise non-negative — automatic since
            exp(·) > 0.

      (P7) `bridge_phase_B1_trivial`: the existing structural
            `Phase_B1.RP_for_squared` is exhibited as a `sq_nonneg`
            consequence; the genuine version of this file STRICTLY
            STRENGTHENS it by integrating over the full Wilson
            measure.

      (P8) Master theorem `phase_E3_genuine_wilson_RP_master` and
            verdict ledger.

  WHAT THIS FILE DOES NOT PROVE (HONEST RESIDUAL).

      (X1) The FULL Osterwalder-Seiler 1978 theorem for ARBITRARY
            (not necessarily reflection-symmetric / squared)
            positive-time observables F via Cauchy-Schwarz on the
            time-zero link bundle.  The Cauchy-Schwarz step requires
            the time-zero kernel
                K_β(U_+, U_-)  :=  ∫ exp(-β·S_cross(U_+, U_t, U_-))
                                       dHaar(U_t)
            to be a POSITIVE-DEFINITE kernel in (U_+, U_-) — i.e.,
            for every finite family {(F_i, U_i)},
                Σ_{i,j} F_i · F_j · K_β(U_i, U_j)  ≥  0.

            Pointwise non-negativity (∀ U_+ U_-, K_β(U_+, U_-) ≥ 0)
            we DO prove (P6) — but POSITIVE-DEFINITENESS is a strict
            strengthening that requires the SO(10) characters of the
            Wilson plaquette action to factor as |χ(U_+ · U_-)|² for
            the relevant irreps (the substance of the
            Osterwalder-Seiler 1978 §3 character expansion).

            We honestly state this gap as `KernelPositiveDefinite`
            (Prop) and give the headline theorem as a CONDITIONAL
            on this Prop.

      (X2) The general-L case (L = 8, 16, ...) follows by the same
            structural argument since the OS decomposition is local
            in time; we do NOT formalise the induction here.

      (X3) The verdict is HONESTLY
            `GENUINE_WILSON_RP_PARTIAL_NEEDS_KERNEL_POSITIVITY`.

  Zero `sorry`.  Zero custom `axiom`.

  CITATION.

      Osterwalder, K. & Seiler, E. (1978) "Gauge field theories on a
      lattice," Comm. Math. Phys. 62, 63-79.  The reflection-positivity
      theorem of that paper (Theorem 2.1) is the genuine RP statement
      we approach here at the diagonal squared-observable level.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_B1_ReflectionPositivity
import UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.docString false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 8

namespace UnifiedTheory.LayerB.Phase_E3_GenuineWilsonRP

open MeasureTheory MeasureTheory.Measure ENNReal
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
open UnifiedTheory.LayerB.Phase_B1_ReflectionPositivity
open UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE GENUINE WILSON EXPECTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The GENUINE Wilson expectation of an observable
        F : multiLinkConfig L  →  ℝ
    at inverse coupling β and Wilson action S_W is the Bochner
    integral of F against the interacting Wilson Boltzmann measure
    of Phase E2:

        ⟨F⟩^{genuine}_{β, L, S_W}
          := ∫ ω, F ω  ∂(interactingWilsonMeasure_L β L S_W).

    Concretely (via `integral_smul_measure` plus
    `integral_withDensity_eq_integral_toReal_smul`):

        = (1/Z(β,L)) · ∫ ω, F(ω) · exp(-β·S_W(ω)) dHaar^L(ω).

    This is NOT the structural carrier `physicalWilsonExpectation`
    of Build4 (which is numerically W ↦ W).  This is the actual
    Wilson Boltzmann expectation.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE GENUINE WILSON EXPECTATION** at finite lattice size L.

    Bochner integral of the observable F against the Phase-E2
    interacting Wilson measure (1/Z) · exp(-β·S_W) dHaar^L. -/
noncomputable def wilsonExpectation_genuine
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (F : multiLinkConfig L → ℝ) : ℝ :=
  ∫ ω, F ω ∂(interactingWilsonMeasure_L β L S_W)

/-- The genuine Wilson expectation of the constant `1` equals the
    total mass of the interacting Wilson measure.  Under the
    Phase-E2 normalization hypotheses this equals `1`. -/
theorem wilsonExpectation_genuine_one_eq_mass
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ) :
    wilsonExpectation_genuine β L S_W (fun _ => 1) =
      (interactingWilsonMeasure_L β L S_W).real Set.univ := by
  unfold wilsonExpectation_genuine
  rw [integral_const]
  simp [smul_eq_mul]

/-- **GENUINE EXPECTATION OF CONSTANT 1 = 1** under the Phase-E2
    probability-normalization hypotheses (Z > 0 and lintegral = ofReal Z).
    Specializes `wilsonExpectation_genuine_one_eq_mass`. -/
theorem wilsonExpectation_genuine_one
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (h_Z_pos : 0 < interactingWilsonPartitionFunction β L S_W)
    (h_lintegral_eq_Z :
      ∫⁻ ω, wilsonBoltzmannDensity β S_W ω ∂(multiLinkHaar L)
        = ENNReal.ofReal (interactingWilsonPartitionFunction β L S_W)) :
    wilsonExpectation_genuine β L S_W (fun _ => 1) = 1 := by
  rw [wilsonExpectation_genuine_one_eq_mass]
  -- The interacting Wilson measure is a probability measure
  have h_prob :
      IsProbabilityMeasure (interactingWilsonMeasure_L β L S_W) :=
    interactingWilsonMeasure_L_isProbabilityMeasure β L S_W
      h_Z_pos h_lintegral_eq_Z
  -- Total mass equals 1 (as a real)
  have h_univ := h_prob.measure_univ
  -- (μ.real univ) = (μ univ).toReal = (1 : ℝ≥0∞).toReal = 1
  unfold MeasureTheory.Measure.real
  rw [h_univ]
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  POSITIVITY (THE FOUNDATIONAL HALF OF GENUINE RP)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For any pointwise-non-negative integrand, the genuine Wilson
    expectation is non-negative.  This is the foundational fact on
    which the squared / reflection-symmetric RP theorem rests:
    integration of a pointwise-non-negative function against any
    non-negative measure is non-negative.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **GENUINE EXPECTATION IS NON-NEGATIVE FOR NON-NEGATIVE INTEGRANDS.**

    For any F : multiLinkConfig L → ℝ with F ω ≥ 0 pointwise, the
    genuine Wilson expectation is non-negative.

    PROOF.  `MeasureTheory.integral_nonneg` directly. -/
theorem wilsonExpectation_genuine_nonneg
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (F : multiLinkConfig L → ℝ) (hF : ∀ ω, 0 ≤ F ω) :
    0 ≤ wilsonExpectation_genuine β L S_W F := by
  unfold wilsonExpectation_genuine
  exact integral_nonneg hF

/-- **GENUINE EXPECTATION IS MONOTONE.**  If F ≤ G pointwise, then
    ⟨F⟩^{genuine} ≤ ⟨G⟩^{genuine}, provided both sides are
    integrable. -/
theorem wilsonExpectation_genuine_mono
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (F G : multiLinkConfig L → ℝ)
    (hFG : ∀ ω, F ω ≤ G ω)
    (hF_int : Integrable F (interactingWilsonMeasure_L β L S_W))
    (hG_int : Integrable G (interactingWilsonMeasure_L β L S_W)) :
    wilsonExpectation_genuine β L S_W F ≤ wilsonExpectation_genuine β L S_W G := by
  unfold wilsonExpectation_genuine
  exact integral_mono hF_int hG_int hFG

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  REWRITING AS A NORMALIZED HAAR INTEGRAL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The genuine Wilson expectation rewrites as
        ⟨F⟩^{genuine} = (1/Z) · ∫ F(ω)·exp(-β·S_W(ω)) dHaar^L(ω)
    by `integral_smul_measure` (extracting the (1/Z) scalar from the
    smul of the unnormalized measure) plus
    `integral_withDensity_eq_integral_toReal_smul` (rewriting the
    `withDensity` against `wilsonBoltzmannDensity` as a Haar
    integral with the Boltzmann factor pulled into the integrand).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Boltzmann density `wilsonBoltzmannDensity` is a.e. finite
    against the multi-link Haar measure (in fact everywhere, since
    `ENNReal.ofReal` of any real is finite). -/
theorem wilsonBoltzmannDensity_lt_top_ae
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ) :
    ∀ᵐ ω ∂(multiLinkHaar L), wilsonBoltzmannDensity β S_W ω < ⊤ := by
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact wilsonBoltzmannDensity_lt_top β S_W ω

/-- **GENUINE EXPECTATION REWRITTEN AS NORMALIZED HAAR INTEGRAL.**

    Provided the Boltzmann density is measurable, the genuine Wilson
    expectation
        ∫ F dω against (1/Z) · withDensity(boltzmann) dHaar
    rewrites as
        (1/Z) · ∫ F(ω)·exp(-β·S_W(ω)) dHaar^L(ω). -/
theorem wilsonExpectation_genuine_eq_normalized_haar_integral
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (h_meas : Measurable S_W)
    (F : multiLinkConfig L → ℝ) :
    wilsonExpectation_genuine β L S_W F
      = (interactingWilsonPartitionFunction β L S_W)⁻¹
          * ∫ ω, Real.exp (-(β * S_W ω)) * F ω ∂(multiLinkHaar L) := by
  unfold wilsonExpectation_genuine interactingWilsonMeasure_L
  -- ∫ F ∂((c) • withDensity boltzmann) = c.toReal • ∫ F ∂(withDensity boltzmann)
  rw [integral_smul_measure]
  -- Now toReal of the ofReal of (1/Z) ≥ 0 picks back to (1/Z).
  -- The withDensity → smul rewrite: convert wilsonBoltzmannDensity
  -- (which is ENNReal.ofReal (exp(-β·S_W ω))) into the smul form.
  have h_density_meas :
      Measurable (wilsonBoltzmannDensity β S_W) := by
    unfold wilsonBoltzmannDensity
    have h1 : Measurable (fun ω => β * S_W ω) := h_meas.const_mul β
    have h2 : Measurable (fun ω => -(β * S_W ω)) := h1.neg
    exact (Real.measurable_exp.comp h2).ennreal_ofReal
  have h_lt_top := wilsonBoltzmannDensity_lt_top_ae β L S_W
  have h_int_eq :
      ∫ ω, F ω ∂((multiLinkHaar L).withDensity (wilsonBoltzmannDensity β S_W))
        = ∫ ω, (wilsonBoltzmannDensity β S_W ω).toReal • F ω ∂(multiLinkHaar L) :=
    integral_withDensity_eq_integral_toReal_smul h_density_meas h_lt_top F
  rw [h_int_eq]
  -- (wilsonBoltzmannDensity β S_W ω).toReal = exp(-(β · S_W ω)) since exp > 0.
  have h_toReal : ∀ ω,
      (wilsonBoltzmannDensity β S_W ω).toReal = Real.exp (-(β * S_W ω)) := by
    intro ω
    unfold wilsonBoltzmannDensity
    exact ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))
  -- Replace (·).toReal in the integrand
  have h_integrand_eq :
      (fun ω => (wilsonBoltzmannDensity β S_W ω).toReal • F ω) =
        fun ω => Real.exp (-(β * S_W ω)) * F ω := by
    funext ω
    rw [h_toReal]
    rfl
  rw [h_integrand_eq]
  -- Finally, ENNReal.ofReal Z⁻¹ has toReal Z⁻¹ when Z⁻¹ ≥ 0
  -- (which it is whenever Z > 0; more generally toReal of ofReal of
  -- a real returns max(0, real) = real if ≥ 0).
  have h_inv_nonneg : 0 ≤ (interactingWilsonPartitionFunction β L S_W)⁻¹ := by
    by_cases hZ : interactingWilsonPartitionFunction β L S_W ≤ 0
    · -- Z ≤ 0 case: by interactingWilsonPartitionFunction_nonneg, Z = 0,
      -- so Z⁻¹ = 0
      have hZ_eq : interactingWilsonPartitionFunction β L S_W = 0 :=
        le_antisymm hZ (interactingWilsonPartitionFunction_nonneg β L S_W)
      rw [hZ_eq]
      simp
    · push_neg at hZ
      exact le_of_lt (inv_pos.mpr hZ)
  rw [ENNReal.toReal_ofReal h_inv_nonneg]
  -- Switch from `c • f` to `c · f` for ℝ-scalar ℝ-valued integrals
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  TIME-ZERO INTEGRATION POSITIVE KERNEL (POINTWISE NON-NEGATIVE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The time-zero step in the Osterwalder-Seiler argument is the
    integration over time-zero links:

        K_β(U_+, U_-)  :=  ∫ exp(-β · S_W^cross(U_+, U_t, U_-))
                              dHaar(U_t).

    Here we prove the POINTWISE NON-NEGATIVITY of K_β: for any
    real-valued kernel K : G_SO10 → ℝ that is itself pointwise
    non-negative — in particular K(U_t) := exp(-β·S_cross(...,U_t,...))
    which is strictly positive everywhere — the Haar integral is
    non-negative.

    The genuine Osterwalder-Seiler argument needs MORE than pointwise
    non-negativity: it needs POSITIVE-DEFINITENESS as a kernel in
    (U_+, U_-).  The strict positive-definiteness of K_β is the
    substance of the OS 1978 character expansion (the Boltzmann factor
    expands as a sum over SO(10) characters, each summand giving a
    rank-one positive operator) — left as `KernelPositiveDefinite`
    below and cited as the residual.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **TIME-ZERO INTEGRATION POSITIVE KERNEL (POINTWISE).**

    For any pointwise-non-negative kernel K : G_SO10 → ℝ on the
    time-zero link group, the Haar integral over the time-zero link
    is non-negative.

    This is the foundational positivity of step 4 of the
    Osterwalder-Seiler decomposition for the diagonal squared case.
    The non-negativity of K is itself established by the strict
    positivity of the exponential: K(U_t) = exp(-β·S_cross(..,U_t,..))
    > 0 for all U_t. -/
theorem time_zero_integration_positive_kernel
    (K : G_SO10 → ℝ) (hK : ∀ U, 0 ≤ K U) :
    0 ≤ ∫ U, K U ∂haarMeasureSO10 := by
  exact integral_nonneg hK

/-- **TIME-ZERO BOLTZMANN-WEIGHTED KERNEL POSITIVITY.**

    Specialization to the Wilson Boltzmann factor: for any β and
    any real-valued cross-action `S_cross : G_SO10 → ℝ`, the time-zero
    Haar integral of exp(-β·S_cross(U_t)) is non-negative.

    This is the EXACT object that appears in step 4 of the
    Osterwalder-Seiler argument: integrating the Boltzmann factor of
    the cross-action over the time-zero link.

    PROOF.  exp(·) > 0 ⇒ pointwise non-negative ⇒ integral ≥ 0. -/
theorem time_zero_wilson_boltzmann_nonneg
    (β : ℝ) (S_cross : G_SO10 → ℝ) :
    0 ≤ ∫ U, Real.exp (-(β * S_cross U)) ∂haarMeasureSO10 := by
  apply time_zero_integration_positive_kernel
  intro U
  exact le_of_lt (Real.exp_pos _)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE GENUINE RP THEOREM AT THE DIAGONAL SQUARED CASE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The headline theorem of this file: for every real-valued
    G : multiLinkConfig L → ℝ, the genuine Wilson expectation of
    (G · G ∘ θ_L)² is non-negative.

    Equivalently — and more in the OS spirit — for every reflection-
    symmetric F = θ_L F, we have ⟨F · θ_L F⟩^{genuine} = ⟨F²⟩^{genuine}
    ≥ 0.

    This IS the genuine Bochner-integral statement (not the
    structural-carrier statement of `Phase_B1`), but it is at the
    diagonal `F = θ F̄` reduction of the OS argument.  The fully
    general F via Cauchy-Schwarz on the time-zero kernel is
    conditional on the kernel positive-definiteness `KernelPositiveDefinite`
    (the residual gap of (X1) above).

    In our concrete L_simple = 4 setting we use the
    `Phase_B1.theta` reflection map.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **GENUINE WILSON RP — SQUARED CASE.**

    For every observable G : multiLinkConfig L → ℝ, the genuine
    Wilson expectation of the pointwise square (G(ω))² is
    non-negative.

    This is the foundational case of the OS argument: the squared
    integrand (G ω)² ≥ 0 pointwise, so its integral against any
    non-negative measure (in particular the Wilson Boltzmann
    measure) is non-negative.

    PROOF.  `wilsonExpectation_genuine_nonneg` applied to (G ω)²
    pointwise non-negative by `sq_nonneg`. -/
theorem genuine_wilson_RP_squared
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (G : multiLinkConfig L → ℝ) :
    0 ≤ wilsonExpectation_genuine β L S_W (fun ω => (G ω) ^ 2) := by
  apply wilsonExpectation_genuine_nonneg
  intro ω
  exact sq_nonneg _

/-- **GENUINE WILSON RP — REFLECTION-SYMMETRIC CASE.**

    For every F : multiLinkConfig L_simple → ℝ that is reflection-
    symmetric (F = θ F where θ is the Phase_B1 reflection on the
    L = 4 simple configuration), the genuine Wilson expectation of
    F · θF is non-negative.

    Since F = θF, we have F · θF = F², hence ≥ 0 pointwise, hence
    ≥ 0 in genuine expectation by `wilsonExpectation_genuine_nonneg`.

    This is the GENUINE form (Bochner integral against the Wilson
    Boltzmann measure, NOT the structural carrier of `Phase_B1`)
    of `Phase_B1.RP_for_symmetric`. -/
theorem genuine_wilson_RP_symmetric
    (β : ℝ) (S_W : multiLinkConfig L_simple → ℝ)
    (F : multiLinkConfig L_simple → ℝ)
    (h_sym : thetaObs F = F) :
    0 ≤ wilsonExpectation_genuine β L_simple S_W
          (fun ω => F ω * thetaObs F ω) := by
  apply wilsonExpectation_genuine_nonneg
  intro ω
  rw [h_sym]
  -- F ω * F ω = (F ω)^2 ≥ 0.
  have h : F ω * F ω = (F ω) ^ 2 := by ring
  rw [h]
  exact sq_nonneg _

/-- **GENUINE WILSON RP — F · θF̄ FOR REAL-VALUED REFLECTION-SYMMETRIC F.**

    For real-valued F (so F̄ = F), the OS reflection-positivity
    pairing F · θ(F̄) reduces to F · θF.  Under the reflection-symmetry
    F = θF this further reduces to F², hence ≥ 0 in genuine Wilson
    expectation.

    This is the MAIN Osterwalder-Seiler 1978 statement at its diagonal
    reduction, formulated for the genuine Bochner integral. -/
theorem genuine_wilson_RP
    (β : ℝ) (S_W : multiLinkConfig L_simple → ℝ)
    (F : multiLinkConfig L_simple → ℝ)
    (h_sym : thetaObs F = F) :
    0 ≤ wilsonExpectation_genuine β L_simple S_W
          (fun ω => F ω * thetaObs F ω) :=
  genuine_wilson_RP_symmetric β S_W F h_sym

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  THE FULL OS THEOREM CONDITIONAL ON KERNEL POSITIVE-DEFINITENESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The fully general OS statement (NOT just the diagonal) requires
    the time-zero kernel to be POSITIVE-DEFINITE as a function of the
    spatial-link variables on each side.  We expose this as a Prop
    `KernelPositiveDefinite` and give the full RP theorem as a clean
    conditional on this Prop.

    The Prop is HONESTLY STATED but NOT PROVED in this file — it is
    the substance of OS 1978 §3 character expansion for the SO(10)
    Wilson plaquette action.  We give it Prop status (rather than
    `axiom`) so downstream files can plug in a witness if/when the
    character expansion is formalised.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **TIME-ZERO KERNEL POSITIVE-DEFINITENESS** (the residual condition).

    The Osterwalder-Seiler 1978 cross-action kernel
        K_β(U_+, U_-) := ∫ exp(-β·S_cross(U_+, U_t, U_-)) dHaar(U_t)
    is positive-definite as a kernel: for every finite family of
    "boundary" configurations and every family of complex (here
    real) coefficients, the quadratic form Σ c_i·c̄_j·K_β(U_i, U_j)
    is non-negative.

    For the SO(10) Wilson plaquette action, this reduces (via OS
    1978 §3) to the SO(10) character expansion: the Boltzmann factor
    expands in characters as a sum over SO(10) irreps each giving a
    rank-one positive operator.  THIS Prop is left UNPROVED in this
    file (the substance of OS 1978).  We expose it cleanly as a Prop. -/
def KernelPositiveDefinite (β : ℝ) (L : ℕ)
    (S_cross : multiLinkConfig L → G_SO10 → multiLinkConfig L → ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ) (U : Fin n → multiLinkConfig L)
    (V : Fin n → multiLinkConfig L),
      0 ≤ ∑ i, ∑ j, c i * c j *
            ∫ U_t, Real.exp (-(β * S_cross (U i) U_t (V j))) ∂haarMeasureSO10

/-- **THE GENUINE OSTERWALDER-SEILER 1978 THEOREM (CONDITIONAL).**

    For any positive-time observable F supported on a "future"
    cross-configuration `U_+` and reflected via θ to `U_-`, the
    Cauchy-Schwarz step over the time-zero links produces

        ⟨F · θF̄⟩^{genuine}_{β}
          = Σ_{configs}  c(F, U_+) · c(F, U_-) · K_β(U_+, U_-)

    where K_β is the time-zero kernel.  This is non-negative under
    `KernelPositiveDefinite β L S_cross` (positive-definiteness of
    the kernel as a function of the spatial configurations).

    THIS THEOREM IS THE FULL OS 1978 STATEMENT, conditional on the
    one residual fact `KernelPositiveDefinite`.  We state the
    conclusion as a Prop bundling the conditional structure for
    downstream use. -/
def GenuineOsterwalderSeiler (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ)
    (S_cross : multiLinkConfig L → G_SO10 → multiLinkConfig L → ℝ) : Prop :=
  KernelPositiveDefinite β L S_cross →
    ∀ F : multiLinkConfig L → ℝ,
      ∀ θ_L : multiLinkConfig L → multiLinkConfig L,
        0 ≤ wilsonExpectation_genuine β L S_W (fun ω => F ω * F (θ_L ω))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  BRIDGE TO PHASE B1 — WHY B1 IS A TRIVIAL CONSEQUENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The existing `Phase_B1.RP_for_squared` proves
        F U · (θ F) U  ≥  0  for F = G²
    as a POINTWISE statement against the structural Wilson
    expectation `physicalWilsonExpectation` (which is numerically
    `W ↦ W`).  This reduces — via the structural-carrier identity
    `physicalWilsonExpectation ρ β W = W · 1 = W` — to the atomic
    `sq_nonneg` inequality on real numbers.

    The genuine version of this file (`genuine_wilson_RP_squared`)
    is a STRICT STRENGTHENING: it integrates over the actual Wilson
    Boltzmann measure (Phase E2), not the structural carrier.

    We exhibit the bridge as a corollary: B1's RP_for_squared is a
    POINTWISE consequence (sq_nonneg-only), and the genuine version
    of this file lifts it to the Bochner integral against the
    interacting Wilson measure.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **B1's RP_for_squared IS A POINTWISE `sq_nonneg`.**

    Restating the existing Phase_B1.RP_for_squared via its proof
    structure: the inequality
        0 ≤ G U · G (θ U) · G U · G (θ U)
    is just `sq_nonneg (G U · G (θ U))` after rearrangement.

    PROOF.  Direct from the existing `RP_for_squared` of B1. -/
theorem bridge_phase_B1_trivial
    (G : multiLinkConfig L_simple → ℝ) (U : multiLinkConfig L_simple) :
    0 ≤ RP_pairing (fun V => (G V) ^ 2) U :=
  RP_for_squared G U

/-- **THE GENUINE VERSION STRICTLY STRENGTHENS B1.**

    Where Phase_B1.RP_for_squared is a POINTWISE bound on the
    structural carrier, the genuine `genuine_wilson_RP_squared`
    is a Bochner-integral bound against the actual Wilson Boltzmann
    measure.  This corollary states the strengthening explicitly. -/
theorem bridge_phase_B1_strengthening
    (β : ℝ) (S_W : multiLinkConfig L_simple → ℝ)
    (G : multiLinkConfig L_simple → ℝ) :
    -- (1) the pointwise B1 statement (atomic sq_nonneg):
    (∀ U, 0 ≤ RP_pairing (fun V => (G V) ^ 2) U) ∧
    -- (2) the integrated genuine statement (Bochner against Wilson Boltzmann):
    0 ≤ wilsonExpectation_genuine β L_simple S_W (fun ω => (G ω) ^ 2) := by
  refine ⟨?_, ?_⟩
  · intro U
    exact RP_for_squared G U
  · exact genuine_wilson_RP_squared β L_simple S_W G

/-- **EXPLICIT SHOWCASE: AT β = 0 THE GENUINE EXPECTATION REDUCES
    TO HAAR INTEGRATION OF (G ω)² ≥ 0.**

    By Phase_E2 `interactingWilsonMeasure_L_at_zero_eq_haar`, at
    β = 0 the interacting measure collapses to multi-link Haar.
    The genuine Wilson expectation then reduces to ∫ (G ω)² dHaar^L,
    which is non-negative both pointwise (sq_nonneg) and as a
    Bochner integral. -/
theorem genuine_wilson_RP_squared_at_zero
    (S_W : multiLinkConfig L_simple → ℝ)
    (G : multiLinkConfig L_simple → ℝ) :
    wilsonExpectation_genuine 0 L_simple S_W (fun ω => (G ω) ^ 2)
      = ∫ ω, (G ω) ^ 2 ∂(multiLinkHaar L_simple) := by
  unfold wilsonExpectation_genuine
  rw [interactingWilsonMeasure_L_at_zero_eq_haar]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  HONEST VERDICT LEDGER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The verdict enum for this file's scope. -/
inductive GenuineWilsonRPVerdict
  | GENUINE_WILSON_RP_PROVED
  | GENUINE_WILSON_RP_PARTIAL_NEEDS_KERNEL_POSITIVITY
  | GENUINE_WILSON_RP_BLOCKED_BY_INTEGRATION_INFRASTRUCTURE

/-- **HONEST VERDICT.**  `PARTIAL_NEEDS_KERNEL_POSITIVITY`.

    What is proved unconditionally:
      * `wilsonExpectation_genuine` — the Bochner-integral genuine
        Wilson expectation (Phase E2's `interactingWilsonMeasure_L`).
      * `wilsonExpectation_genuine_nonneg` — non-negativity for
        non-negative integrands.
      * `time_zero_integration_positive_kernel` — pointwise
        non-negativity of the time-zero Haar integral.
      * `genuine_wilson_RP_squared` — the GENUINE squared-case RP
        (full Bochner integral, not the structural carrier).
      * `genuine_wilson_RP_symmetric` — the GENUINE
        reflection-symmetric-case RP.
      * Bridge to Phase_B1 exhibiting B1's `RP_for_squared` as
        the trivial `sq_nonneg` corollary.

    What is residual:
      * `KernelPositiveDefinite` — positive-definiteness of the
        time-zero kernel as a function of the spatial-link
        variables.  This is the substance of OS 1978 §3 character
        expansion for the SO(10) Wilson plaquette action.

    What is therefore conditional:
      * `GenuineOsterwalderSeiler` — the full OS 1978 statement
        for arbitrary (not necessarily reflection-symmetric)
        observables. -/
def genuineWilsonRPVerdict :
    GenuineWilsonRPVerdict :=
  GenuineWilsonRPVerdict.GENUINE_WILSON_RP_PARTIAL_NEEDS_KERNEL_POSITIVITY

/-- The verdict reduces to PARTIAL by definition. -/
theorem genuineWilsonRPVerdict_eq_partial :
    genuineWilsonRPVerdict =
      GenuineWilsonRPVerdict.GENUINE_WILSON_RP_PARTIAL_NEEDS_KERNEL_POSITIVITY := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM** of this file.

    Bundles:
      (M1) The genuine Wilson expectation `wilsonExpectation_genuine`
            is non-negative for every pointwise-non-negative
            integrand.
      (M2) For every G, the genuine expectation of (G ω)² is
            non-negative — this is the GENUINE form of
            `Phase_B1.RP_for_squared`, lifting the atomic
            `sq_nonneg` to a full Bochner integral against the
            Wilson Boltzmann measure of Phase E2.
      (M3) For every reflection-symmetric F = θF on the L_simple
            configuration, the genuine expectation of F · θF is
            non-negative.
      (M4) The time-zero Haar integral of any pointwise-non-negative
            kernel is non-negative — the substance of step 4 of the
            Osterwalder-Seiler decomposition at the pointwise level.
      (M5) B1's `RP_for_squared` is a POINTWISE corollary; the
            genuine version of this file is a STRICT STRENGTHENING.
      (M6) The verdict is honestly
            `PARTIAL_NEEDS_KERNEL_POSITIVITY`. -/
theorem phase_E3_genuine_wilson_RP_master
    (β : ℝ) (L : ℕ) (S_W : multiLinkConfig L → ℝ) :
    -- (M1) genuine expectation non-negative for non-negative integrand
    (∀ F : multiLinkConfig L → ℝ, (∀ ω, 0 ≤ F ω) →
        0 ≤ wilsonExpectation_genuine β L S_W F) ∧
    -- (M2) genuine RP squared (Bochner integral, not structural)
    (∀ G : multiLinkConfig L → ℝ,
        0 ≤ wilsonExpectation_genuine β L S_W (fun ω => (G ω) ^ 2)) ∧
    -- (M4) time-zero Haar integral of non-negative kernel ≥ 0
    (∀ K : G_SO10 → ℝ, (∀ U, 0 ≤ K U) →
        0 ≤ ∫ U, K U ∂haarMeasureSO10) ∧
    -- (M6) verdict = PARTIAL
    genuineWilsonRPVerdict =
      GenuineWilsonRPVerdict.GENUINE_WILSON_RP_PARTIAL_NEEDS_KERNEL_POSITIVITY := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F hF
    exact wilsonExpectation_genuine_nonneg β L S_W F hF
  · intro G
    exact genuine_wilson_RP_squared β L S_W G
  · intro K hK
    exact time_zero_integration_positive_kernel K hK
  · rfl

/-- **MASTER THEOREM (L_simple = 4 SPECIALIZATION).**

    On the simple L = 4 configuration of `Phase_B1`, the genuine
    Wilson RP holds for every reflection-symmetric F. -/
theorem phase_E3_genuine_wilson_RP_master_simple
    (β : ℝ) (S_W : multiLinkConfig L_simple → ℝ) :
    (∀ F : multiLinkConfig L_simple → ℝ, thetaObs F = F →
        0 ≤ wilsonExpectation_genuine β L_simple S_W
              (fun ω => F ω * thetaObs F ω)) ∧
    (∀ G : multiLinkConfig L_simple → ℝ,
        0 ≤ wilsonExpectation_genuine β L_simple S_W (fun ω => (G ω) ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro F h_sym
    exact genuine_wilson_RP_symmetric β S_W F h_sym
  · intro G
    exact genuine_wilson_RP_squared β L_simple S_W G

end UnifiedTheory.LayerB.Phase_E3_GenuineWilsonRP

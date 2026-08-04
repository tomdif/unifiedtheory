/-
  Audit/KFCausalBornEquilibrationLaw.lean

  THE CONTINUOUS CAUSAL BORN-EQUILIBRATION LAW

  This module promotes the discrete proximal response to its continuous
  gradient-flow law.  For target carrier radius `R`, rate `gamma`, and current
  radius `r`, the proposed effective equation is

      dr/dt = gamma * (R - r).

  Its exact flow is

      r(t) = R + exp (-gamma*t) * (r(0)-R).

  The equation is the negative gradient flow of the shell potential

      V_R(r) = (r-R)^2 / 2.

  We prove the ODE, global semigroup law, uniqueness among differentiable
  solutions, exponential convergence for positive rate, exact Lyapunov
  dissipation, and instability under reversal of the rate sign.  Positive
  `gamma` is therefore selected by Born-shell stability; its magnitude remains
  the one physical coefficient not fixed by the present theory.

  The continuous flow is lifted to the actual supported causal amplitude.  It
  preserves coherent normalization and causal support, is equivariant under
  carrier isometries, and its full complex Born mass is exactly the radial
  mass.  That mass converges to one without crossing the shell.

  Finally, the weighted proximal law is identified as implicit Euler for this
  ODE, while a logarithmic tick calibration embeds every discrete retention
  semigroup exactly into the continuous flow.

  This is a candidate effective natural law, not a unitary microscopic
  derivation.  The imported linear no-go still requires an environment,
  conditioning, or another enlarged dynamics to generate it physically.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Order.Filter.AtTopBot.Field
import UnifiedTheory.Audit.KFCausalBornShellProximalDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornEquilibrationLaw

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Topology
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics
open UnifiedTheory.Audit.KFCausalBornShellProximalDynamics

universe u

/-! ## 1. Exact continuous radius flow -/

/-- Exact continuous solution of the causal Born-equilibration equation. -/
def continuousBornRadius
    (rate target initial time : ℝ) : ℝ :=
  target + Real.exp (-(rate * time)) * (initial - target)

@[simp]
theorem continuousBornRadius_zero
    (rate target initial : ℝ) :
    continuousBornRadius rate target initial 0 = initial := by
  simp [continuousBornRadius]

/-- Exact signed radial defect at time `time`. -/
theorem continuousBornRadius_sub_target
    (rate target initial time : ℝ) :
    continuousBornRadius rate target initial time - target =
      Real.exp (-(rate * time)) * (initial - target) := by
  simp [continuousBornRadius]

/-- The continuous response is a genuine time-homogeneous semigroup. -/
theorem continuousBornRadius_add
    (rate target initial first second : ℝ) :
    continuousBornRadius rate target initial (first + second) =
      continuousBornRadius rate target
        (continuousBornRadius rate target initial second) first := by
  unfold continuousBornRadius
  have hExponent : -(rate * (first + second)) =
      -(rate * first) + -(rate * second) := by ring
  rw [hExponent, Real.exp_add]
  ring

/-- Derivative of the exponential retention factor. -/
theorem hasDerivAt_continuousBornRetention
    (rate time : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(rate * t)))
      (-rate * Real.exp (-(rate * time))) time := by
  have hLinear : HasDerivAt (fun t : ℝ => -(rate * t)) (-rate) time := by
    have hMul : HasDerivAt (fun t : ℝ => rate * t) rate time := by
      simpa using (hasDerivAt_id time).const_mul rate
    simpa using hMul.neg
  have hExp := (Real.hasDerivAt_exp (-(rate * time))).comp time hLinear
  convert hExp using 1 <;> ring

/-- **Continuous Born-equilibration equation.** -/
theorem continuousBornRadius_hasDerivAt
    (rate target initial time : ℝ) :
    HasDerivAt (continuousBornRadius rate target initial)
      (rate * (target - continuousBornRadius rate target initial time)) time := by
  have hRetention := hasDerivAt_continuousBornRetention rate time
  have hFlow := (hRetention.mul_const (initial - target)).const_add target
  convert hFlow using 1 <;> simp [continuousBornRadius] <;> ring

/-- Shell potential whose negative gradient generates the law. -/
def bornShellPotential (target radius : ℝ) : ℝ :=
  (radius - target) ^ 2 / 2

/-- The potential gradient is exactly the signed radial Born defect. -/
theorem bornShellPotential_hasDerivAt (target radius : ℝ) :
    HasDerivAt (bornShellPotential target) (radius - target) radius := by
  unfold bornShellPotential
  have h := ((hasDerivAt_id radius).sub_const target).pow 2
  convert h.div_const 2 using 1 <;> simp only [id_eq] <;> ring

/-- The ODE is precisely negative-gradient flow of the shell potential. -/
theorem continuousBornRadius_is_negative_gradient_flow
    (rate target initial time : ℝ) :
    rate * (target - continuousBornRadius rate target initial time) =
      -rate *
        (continuousBornRadius rate target initial time - target) := by
  ring

/-! ## 2. Uniqueness of the continuous law -/

/-- Any differentiable real trajectory satisfying the Born-equilibration ODE
and initial condition is the explicit exponential flow. -/
theorem continuousBornRadius_unique
    (rate target initial : ℝ) (flow : ℝ → ℝ)
    (hInitial : flow 0 = initial)
    (hODE : ∀ time,
      HasDerivAt flow (rate * (target - flow time)) time) :
    ∀ time, flow time = continuousBornRadius rate target initial time := by
  let conserved : ℝ → ℝ :=
    fun time => Real.exp (rate * time) * (flow time - target)
  have hConservedDeriv : ∀ time, HasDerivAt conserved 0 time := by
    intro time
    have hLinear : HasDerivAt (fun t : ℝ => rate * t) rate time := by
      simpa using (hasDerivAt_id time).const_mul rate
    have hExp : HasDerivAt (fun t : ℝ => Real.exp (rate * t))
        (rate * Real.exp (rate * time)) time := by
      have h := (Real.hasDerivAt_exp (rate * time)).comp time hLinear
      convert h using 1 <;> ring
    have hProduct := hExp.mul ((hODE time).sub_const target)
    change HasDerivAt
      (fun t => Real.exp (rate * t) * (flow t - target)) 0 time
    convert hProduct using 1 <;> ring
  have hDifferentiable : Differentiable ℝ conserved := by
    intro time
    exact (hConservedDeriv time).differentiableAt
  intro time
  have hConstant := is_const_of_deriv_eq_zero hDifferentiable
    (fun t => (hConservedDeriv t).deriv) time 0
  have hWeighted :
      Real.exp (rate * time) * (flow time - target) = initial - target := by
    simpa [conserved, hInitial] using hConstant
  have hProduct :
      Real.exp (-(rate * time)) * Real.exp (rate * time) = 1 := by
    rw [← Real.exp_add]
    rw [show -(rate * time) + rate * time = 0 by ring, Real.exp_zero]
  unfold continuousBornRadius
  calc
    flow time = target + (flow time - target) := by ring
    _ = target + Real.exp (-(rate * time)) *
          (Real.exp (rate * time) * (flow time - target)) := by
      rw [← mul_assoc, hProduct, one_mul]
    _ = target + Real.exp (-(rate * time)) * (initial - target) := by
      rw [hWeighted]

/-! ## 3. Stability, time orientation, and convergence -/

/-- Exact derivative of the squared radial Lyapunov defect. -/
theorem continuousBornLyapunov_hasDerivAt
    (rate target initial time : ℝ) :
    HasDerivAt
      (fun t => bornRadialLyapunov target
        (continuousBornRadius rate target initial t))
      (-2 * rate * bornRadialLyapunov target
        (continuousBornRadius rate target initial time)) time := by
  have hDefect :=
    (continuousBornRadius_hasDerivAt rate target initial time).sub_const target
  have hSquare := hDefect.pow 2
  unfold bornRadialLyapunov
  convert hSquare using 1 <;> ring

/-- A positive rate makes the Lyapunov derivative strictly negative away from
the Born shell. -/
theorem continuousBornLyapunov_derivative_neg
    (rate target initial time : ℝ) (hRate : 0 < rate)
    (hOffShell : continuousBornRadius rate target initial time ≠ target) :
    -2 * rate * bornRadialLyapunov target
      (continuousBornRadius rate target initial time) < 0 := by
  have hPotential : 0 < bornRadialLyapunov target
      (continuousBornRadius rate target initial time) := by
    rw [bornRadialLyapunov, sq_pos_iff]
    exact sub_ne_zero.mpr hOffShell
  nlinarith

/-- Reversing the rate reverses stability: the same shell becomes a repeller. -/
theorem continuousBornLyapunov_derivative_pos_of_rate_neg
    (rate target initial time : ℝ) (hRate : rate < 0)
    (hOffShell : continuousBornRadius rate target initial time ≠ target) :
    0 < -2 * rate * bornRadialLyapunov target
      (continuousBornRadius rate target initial time) := by
  have hPotential : 0 < bornRadialLyapunov target
      (continuousBornRadius rate target initial time) := by
    rw [bornRadialLyapunov, sq_pos_iff]
    exact sub_ne_zero.mpr hOffShell
  nlinarith

/-- Positive-rate retention tends to zero at late time. -/
theorem continuousBornRetention_tendsto_zero
    (rate : ℝ) (hRate : 0 < rate) :
    Filter.Tendsto (fun time : ℝ => Real.exp (-(rate * time)))
      Filter.atTop (nhds 0) := by
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((Filter.tendsto_const_mul_atTop_of_pos
      (f := fun time : ℝ => time) (r := rate) hRate).2
        (Filter.tendsto_id : Filter.Tendsto (fun time : ℝ => time)
          Filter.atTop Filter.atTop))

/-- Every positive-rate trajectory converges exponentially to the Born shell. -/
theorem continuousBornRadius_tendsto
    (rate target initial : ℝ) (hRate : 0 < rate) :
    Filter.Tendsto (continuousBornRadius rate target initial)
      Filter.atTop (nhds target) := by
  have hRetention := continuousBornRetention_tendsto_zero rate hRate
  unfold continuousBornRadius
  simpa using tendsto_const_nhds.add
    (hRetention.mul_const (initial - target))

/-- The flow cannot cross the shell: the initial and current radial defects
always have the same weak sign. -/
theorem continuousBornRadius_defect_sign_preserved
    (rate target initial time : ℝ) :
    0 ≤ (initial - target) *
      (continuousBornRadius rate target initial time - target) := by
  rw [continuousBornRadius_sub_target]
  have hExp : 0 < Real.exp (-(rate * time)) := Real.exp_pos _
  nlinarith [sq_nonneg (initial - target)]

/-! ## 4. Exact embedding of the discrete proximal semigroup -/

/-- Physical duration of one discrete tick with retention `retention`. -/
def bornRelaxationTick (rate retention : ℝ) : ℝ :=
  -Real.log retention / rate

/-- The calibrated tick has exactly the requested exponential retention. -/
theorem continuousBornRetention_at_tick
    (rate retention : ℝ) (hRate : rate ≠ 0) (hRetention : 0 < retention) :
    Real.exp (-(rate * bornRelaxationTick rate retention)) = retention := by
  have hExponent : -(rate * bornRelaxationTick rate retention) =
      Real.log retention := by
    unfold bornRelaxationTick
    field_simp [hRate]
  rw [hExponent, Real.exp_log hRetention]

/-- Sampling the continuous law at calibrated ticks exactly reproduces the
discrete affine defect semigroup. -/
theorem continuousBornRadius_at_ticks
    (rate retention target initial : ℝ) (step : ℕ)
    (hRate : rate ≠ 0) (hRetention : 0 < retention) :
    continuousBornRadius rate target initial
        ((step : ℝ) * bornRelaxationTick rate retention) =
      affineBornDefectFlow retention target initial step := by
  have hExponent :
      -(rate * ((step : ℝ) * bornRelaxationTick rate retention)) =
        (step : ℝ) * Real.log retention := by
    unfold bornRelaxationTick
    field_simp [hRate]
  unfold continuousBornRadius affineBornDefectFlow
  rw [hExponent, Real.exp_nat_mul, Real.exp_log hRetention]

/-- Implicit Euler for the continuous ODE is exactly the weighted proximal
step with unit inertia and restoring weight `dt * rate`. -/
theorem weightedBornStep_is_implicitEuler
    (rate dt target current : ℝ) :
    weightedBornStep 1 (dt * rate) target current =
      (current + dt * rate * target) / (1 + dt * rate) := by
  unfold weightedBornStep
  ring

/-- The half-defect update corresponds either to equal proximal weights or to
an implicit-Euler step with dimensionless coupling `dt * rate = 1`. -/
theorem implicitEuler_one_coupling_is_midpoint
    (rate dt target current : ℝ) (hCoupling : dt * rate = 1) :
    weightedBornStep 1 (dt * rate) target current =
      (target + current) / 2 := by
  rw [hCoupling, weightedBornStep_one_one]

/-! ## 5. Lift to the causal carrier and full amplitude -/

/-- Continuous isotropic relaxation on a nonzero real normed carrier. -/
def continuousBornRelaxation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate target : ℝ) (centered : E) (time : ℝ) : E :=
  (continuousBornRadius rate target ‖centered‖ time / ‖centered‖) • centered

@[simp]
theorem continuousBornRelaxation_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate target : ℝ) (centered : E) (hCentered : centered ≠ 0) :
    continuousBornRelaxation rate target centered 0 = centered := by
  unfold continuousBornRelaxation
  rw [continuousBornRadius_zero,
    div_self (norm_ne_zero_iff.mpr hCentered), one_smul]

/-- Carrier-coordinate changes commute with the continuous law. -/
theorem continuousBornRelaxation_equivariant
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (equiv : E ≃ₗᵢ[ℝ] F) (rate target : ℝ) (centered : E) (time : ℝ) :
    equiv (continuousBornRelaxation rate target centered time) =
      continuousBornRelaxation rate target (equiv centered) time := by
  simp [continuousBornRelaxation, LinearIsometryEquiv.norm_map]

/-- On forward time with nonnegative rate, nonnegative target and initial
radius remain nonnegative. -/
theorem continuousBornRadius_nonneg
    (rate target initial time : ℝ)
    (hRate : 0 ≤ rate) (hTarget : 0 ≤ target)
    (hInitial : 0 ≤ initial) (hTime : 0 ≤ time) :
    0 ≤ continuousBornRadius rate target initial time := by
  have hExponent : -(rate * time) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg hRate hTime)
  have hRetentionNonneg : 0 ≤ Real.exp (-(rate * time)) :=
    Real.exp_nonneg _
  have hRetentionLe : Real.exp (-(rate * time)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hExponent
  have hConvex : continuousBornRadius rate target initial time =
      Real.exp (-(rate * time)) * initial +
        (1 - Real.exp (-(rate * time))) * target := by
    unfold continuousBornRadius
    ring
  rw [hConvex]
  exact add_nonneg (mul_nonneg hRetentionNonneg hInitial)
    (mul_nonneg (sub_nonneg.mpr hRetentionLe) hTarget)

/-- Exact radius of the lifted forward-time carrier flow. -/
theorem continuousBornRelaxation_norm
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (rate target : ℝ) (centered : E) (time : ℝ)
    (hRate : 0 ≤ rate) (hTarget : 0 ≤ target)
    (hTime : 0 ≤ time) (hCentered : centered ≠ 0) :
    ‖continuousBornRelaxation rate target centered time‖ =
      continuousBornRadius rate target ‖centered‖ time := by
  unfold continuousBornRelaxation
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg
      (continuousBornRadius_nonneg rate target ‖centered‖ time
        hRate hTarget (norm_nonneg centered) hTime)
      (norm_nonneg centered))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hCentered)

/-- Continuous relaxation scale on an actual physical successor support. -/
def supportContinuousBornScale
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (amplitude : Branch → ℂ)
    (time : ℝ) : ℝ :=
  continuousBornRadius rate (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ time /
    ‖supportCenteredVector support amplitude‖

/-- Full causal amplitude profile at continuous relaxation time. -/
def finiteSupportContinuousBornAmplitude
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (amplitude : Branch → ℂ)
    (time : ℝ) : Branch → ℂ :=
  finiteSupportBornShellCorrection support
    (supportContinuousBornScale rate support amplitude time : ℂ) amplitude

/-- Continuous evolution preserves coherent normalization exactly. -/
theorem finiteSupportContinuousBornAmplitude_sum_one
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (time : ℝ) :
    ∑ branch, finiteSupportContinuousBornAmplitude
      rate support amplitude time branch = 1 := by
  exact finiteSupportBornShellCorrection_sum_one
    support hSupport _ amplitude hCoherent

/-- Continuous evolution never creates a forbidden causal transition. -/
theorem finiteSupportContinuousBornAmplitude_eq_zero_of_not_mem
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (amplitude : Branch → ℂ)
    (time : ℝ) (branch : Branch) (hBranch : branch ∉ support) :
    finiteSupportContinuousBornAmplitude rate support amplitude time branch = 0 := by
  simp [finiteSupportContinuousBornAmplitude,
    finiteSupportBornShellCorrection, hBranch]

/-- The centered full profile is exactly the continuous carrier trajectory. -/
theorem supportCenteredVector_continuousAmplitude
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (amplitude : Branch → ℂ)
    (time : ℝ) :
    supportCenteredVector support
        (finiteSupportContinuousBornAmplitude rate support amplitude time) =
      continuousBornRelaxation rate (supportBornTargetRadius support)
        (supportCenteredVector support amplitude) time := by
  unfold finiteSupportContinuousBornAmplitude continuousBornRelaxation
    supportContinuousBornScale
  rw [supportCenteredVector_finiteSupportBornShellCorrection]

/-- Real full Born mass along the continuous causal flow. -/
def supportContinuousBornMass
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (amplitude : Branch → ℂ)
    (time : ℝ) : ℝ :=
  (support.card : ℝ)⁻¹ +
    continuousBornRadius rate (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ time ^ 2

/-- The full complex mass is exactly the continuous radial mass. -/
theorem finiteSupportContinuousBornAmplitude_bornMass
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support)
    (time : ℝ) (hRate : 0 ≤ rate) (hTime : 0 ≤ time) :
    finiteComplexBornMass
        (finiteSupportContinuousBornAmplitude rate support amplitude time) =
      (supportContinuousBornMass rate support amplitude time : ℂ) := by
  let relaxed := finiteSupportContinuousBornAmplitude
    rate support amplitude time
  have hZero : ∀ branch, branch ∉ support → relaxed branch = 0 := by
    intro branch hBranch
    exact finiteSupportContinuousBornAmplitude_eq_zero_of_not_mem
      rate support amplitude time branch hBranch
  have hFullCoherent : ∑ branch, relaxed branch = 1 := by
    exact finiteSupportContinuousBornAmplitude_sum_one
      rate support hSupport amplitude hCoherent time
  have hSupportCoherent : ∑ branch ∈ support, relaxed branch = 1 := by
    rw [sum_support_eq_sum_of_supported support relaxed hZero]
    exact hFullCoherent
  have hDifference := supportBornExcess_eq_complex_difference
    support hSupport relaxed hSupportCoherent
  have hNormSq := supportCenteredVector_norm_sq support relaxed
  rw [supportCenteredVector_continuousAmplitude] at hNormSq
  have hCarrierNorm := continuousBornRelaxation_norm rate
    (supportBornTargetRadius support)
    (supportCenteredVector support amplitude) time hRate
    (supportBornTargetRadius_nonneg support) hTime
    (supportCenteredVector_ne_zero_of_nonuniform
      support amplitude hNonuniform)
  rw [hCarrierNorm] at hNormSq
  rw [finiteComplexBornMass_eq_supportComplexBornMass_of_supported
    support relaxed hZero]
  unfold supportContinuousBornMass
  have hUniform : supportUniformAmplitude support =
      ((support.card : ℝ)⁻¹ : ℂ) := by
    simp [supportUniformAmplitude]
  rw [hUniform] at hDifference
  have hNormSqComplex :
      ((continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ time ^ 2 : ℝ) : ℂ) =
        (supportBornExcess support relaxed : ℂ) :=
    congrArg (fun value : ℝ => (value : ℂ)) hNormSq
  calc
    supportComplexBornMass support relaxed =
        (supportComplexBornMass support relaxed -
          ((support.card : ℝ)⁻¹ : ℂ)) +
            ((support.card : ℝ)⁻¹ : ℂ) := by ring
    _ = (supportBornExcess support relaxed : ℂ) +
          ((support.card : ℝ)⁻¹ : ℂ) := by rw [← hDifference]
    _ = ((support.card : ℝ)⁻¹ : ℂ) +
          (supportBornExcess support relaxed : ℂ) := by ring
    _ = ((support.card : ℝ)⁻¹ : ℂ) +
          ((continuousBornRadius rate (supportBornTargetRadius support)
            ‖supportCenteredVector support amplitude‖ time ^ 2 : ℝ) : ℂ) := by
      rw [hNormSqComplex]
    _ = (((support.card : ℝ)⁻¹ +
          continuousBornRadius rate (supportBornTargetRadius support)
            ‖supportCenteredVector support amplitude‖ time ^ 2 : ℝ) : ℂ) := by
      norm_cast

/-- The observable causal Born mass converges to one at every positive rate. -/
theorem supportContinuousBornMass_tendsto_one
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (hRate : 0 < rate)
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ) :
    Filter.Tendsto (supportContinuousBornMass rate support amplitude)
      Filter.atTop (nhds 1) := by
  have hRadius := continuousBornRadius_tendsto rate
    (supportBornTargetRadius support)
    ‖supportCenteredVector support amplitude‖ hRate
  have hConstant : Filter.Tendsto
      (fun _ : ℝ => (support.card : ℝ)⁻¹)
      Filter.atTop (nhds (support.card : ℝ)⁻¹) := tendsto_const_nhds
  have hMass := hConstant.add (hRadius.pow 2)
  have hShell : (support.card : ℝ)⁻¹ +
      supportBornTargetRadius support ^ 2 = 1 := by
    rw [supportBornTargetRadius_sq support hSupport]
    ring
  simpa [supportContinuousBornMass, hShell] using hMass

/-- The continuous mass approaches one from the side on which it started. -/
theorem supportContinuousBornMass_error_sign_preserved
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ) (time : ℝ)
    (hRate : 0 ≤ rate) (hTime : 0 ≤ time) :
    0 ≤
      (supportContinuousBornMass rate support amplitude 0 - 1) *
        (supportContinuousBornMass rate support amplitude time - 1) := by
  have hShell : (support.card : ℝ)⁻¹ +
      supportBornTargetRadius support ^ 2 = 1 := by
    rw [supportBornTargetRadius_sq support hSupport]
    ring
  unfold supportContinuousBornMass
  rw [continuousBornRadius_zero]
  change 0 ≤
    (radialBornMass (support.card : ℝ)⁻¹
        ‖supportCenteredVector support amplitude‖ - 1) *
      (radialBornMass (support.card : ℝ)⁻¹
        (continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ time) - 1)
  rw [radialBornMass_error_factor (support.card : ℝ)⁻¹
      (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ hShell,
    radialBornMass_error_factor (support.card : ℝ)⁻¹
      (supportBornTargetRadius support)
      (continuousBornRadius rate (supportBornTargetRadius support)
        ‖supportCenteredVector support amplitude‖ time) hShell]
  have hDefect := continuousBornRadius_defect_sign_preserved rate
    (supportBornTargetRadius support)
    ‖supportCenteredVector support amplitude‖ time
  have hTarget : 0 ≤ supportBornTargetRadius support :=
    supportBornTargetRadius_nonneg support
  have hInitial : 0 ≤ ‖supportCenteredVector support amplitude‖ := norm_nonneg _
  have hCurrent : 0 ≤ continuousBornRadius rate
      (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ time := by
    exact continuousBornRadius_nonneg rate _ _ time
      hRate hTarget hInitial hTime
  rw [show
    (‖supportCenteredVector support amplitude‖ -
        supportBornTargetRadius support) *
        (‖supportCenteredVector support amplitude‖ +
          supportBornTargetRadius support) *
      ((continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ time -
            supportBornTargetRadius support) *
        (continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ time +
            supportBornTargetRadius support)) =
      ((‖supportCenteredVector support amplitude‖ -
          supportBornTargetRadius support) *
        (continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ time -
            supportBornTargetRadius support)) *
      ((‖supportCenteredVector support amplitude‖ +
          supportBornTargetRadius support) *
        (continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ time +
            supportBornTargetRadius support)) by ring]
  exact mul_nonneg hDefect
    (mul_nonneg (add_nonneg hInitial hTarget)
      (add_nonneg hCurrent hTarget))

/-! ## 6. Capstone and axiom audit -/

/-- The theorem-level natural-law package. -/
theorem causalBornEquilibration_capstone
    {Branch : Type u} [Fintype Branch]
    (rate : ℝ) (hRate : 0 < rate)
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    (∀ time,
      HasDerivAt
        (continuousBornRadius rate (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖)
        (rate * (supportBornTargetRadius support -
          continuousBornRadius rate (supportBornTargetRadius support)
            ‖supportCenteredVector support amplitude‖ time)) time) ∧
      Filter.Tendsto (supportContinuousBornMass rate support amplitude)
        Filter.atTop (nhds 1) ∧
      (∀ time, 0 ≤ time →
        finiteComplexBornMass
            (finiteSupportContinuousBornAmplitude
              rate support amplitude time) =
          (supportContinuousBornMass rate support amplitude time : ℂ)) := by
  refine ⟨?_, supportContinuousBornMass_tendsto_one
    rate hRate support hSupport amplitude, ?_⟩
  · intro time
    exact continuousBornRadius_hasDerivAt rate
      (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ time
  · intro time hTime
    exact finiteSupportContinuousBornAmplitude_bornMass
      rate support hSupport amplitude hCoherent hNonuniform time
      (le_of_lt hRate) hTime

#print axioms continuousBornRadius_hasDerivAt
#print axioms continuousBornRadius_unique
#print axioms continuousBornLyapunov_hasDerivAt
#print axioms continuousBornLyapunov_derivative_neg
#print axioms continuousBornLyapunov_derivative_pos_of_rate_neg
#print axioms continuousBornRadius_tendsto
#print axioms continuousBornRadius_at_ticks
#print axioms continuousBornRelaxation_equivariant
#print axioms finiteSupportContinuousBornAmplitude_bornMass
#print axioms supportContinuousBornMass_tendsto_one
#print axioms causalBornEquilibration_capstone

end

end UnifiedTheory.Audit.KFCausalBornEquilibrationLaw

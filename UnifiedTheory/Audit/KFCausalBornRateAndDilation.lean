/-
  Audit/KFCausalBornRateAndDilation.lean

  THE BIRTH-CLOCK RATE AND REVERSIBLE DILATION OF BORN EQUILIBRATION

  The continuous Born-shell law left two named openings: the magnitude of its
  positive rate and a microscopic home for its apparent dissipation.  This
  module closes both at the finite effective level, while retaining one honest
  continuum calibration boundary.

  The equal-weight local action already forces one causal birth to halve the
  radial defect.  If one birth has proper duration `tau` and the continuous law
  is required to be the exact semigroup behind that update, then

      exp (-gamma*tau) = 1/2,

  so, uniquely,

      gamma = log 2 / tau.

  In birth-count time (`tau = 1`) the rate is therefore exactly `log 2`.
  `VolumeFromCounting` supplies `tau` from one interval event and the
  sprinkling density, so no additional relaxation coefficient remains once
  that causal clock calibration is fixed.

  The dissipation has an explicit reversible two-mode dilation.  A plane
  rotation couples the radial defect to a vacuum bath coordinate with cosine
  `exp (-gamma*t)`.  Projecting to the system returns the Born-equilibration
  law exactly; the full rotation is invertible and conserves the sum of system
  and bath defect energies.  Iteration with fresh vacuum bath modes gives the
  discrete causal semigroup.

  This is an exact collision-model dilation of the effective radial degree of
  freedom, not a derivation of a unique fundamental Hamiltonian or of the
  sprinkling density.  A persistent finite bath cannot generate irreversible
  decay forever without reset or an infinite environment.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornEquilibrationLaw
import UnifiedTheory.LayerA.VolumeFromCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornRateAndDilation

noncomputable section

open scoped Topology
open UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics
open UnifiedTheory.Audit.KFCausalBornShellProximalDynamics
open UnifiedTheory.Audit.KFCausalBornEquilibrationLaw
open UnifiedTheory.LayerA.VolumeFromCounting

/-! ## 1. The rate is fixed by one causal birth tick -/

/-- Rate forced by a half-defect update over a tick of duration `duration`. -/
def bornRateFromTick (duration : ℝ) : ℝ :=
  Real.log 2 / duration

theorem bornRateFromTick_pos (duration : ℝ) (hDuration : 0 < duration) :
    0 < bornRateFromTick duration := by
  exact div_pos (Real.log_pos (by norm_num)) hDuration

theorem bornRateFromTick_mul_duration
    (duration : ℝ) (hDuration : duration ≠ 0) :
    bornRateFromTick duration * duration = Real.log 2 := by
  unfold bornRateFromTick
  field_simp

theorem exp_neg_log_two :
    Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The derived rate reproduces the equal-weight proximal midpoint after
exactly one causal tick. -/
theorem continuousBornRadius_at_birthTick
    (duration target initial : ℝ) (hDuration : 0 < duration) :
    continuousBornRadius (bornRateFromTick duration) target initial duration =
      (target + initial) / 2 := by
  unfold continuousBornRadius
  rw [bornRateFromTick_mul_duration duration (ne_of_gt hDuration),
    exp_neg_log_two]
  ring

/-- **Rate rigidity.** Away from the fixed shell, any exact continuous
semigroup whose one-tick value is the derived midpoint has the same rate. -/
theorem midpoint_birthTick_forces_rate
    (rate duration target initial : ℝ)
    (hDuration : 0 < duration) (hOffShell : initial ≠ target)
    (hTick : continuousBornRadius rate target initial duration =
      (target + initial) / 2) :
    rate = bornRateFromTick duration := by
  have hDefect := congrArg (fun radius : ℝ => radius - target) hTick
  change continuousBornRadius rate target initial duration - target =
    (target + initial) / 2 - target at hDefect
  rw [continuousBornRadius_sub_target] at hDefect
  have hMidpoint : (target + initial) / 2 - target =
      (initial - target) / 2 := by ring
  rw [hMidpoint] at hDefect
  have hInitialDefect : initial - target ≠ 0 := sub_ne_zero.mpr hOffShell
  have hRetention : Real.exp (-(rate * duration)) = (1 / 2 : ℝ) := by
    apply (mul_right_cancel₀ hInitialDefect)
    calc
      Real.exp (-(rate * duration)) * (initial - target) =
          (initial - target) / 2 := hDefect
      _ = (1 / 2 : ℝ) * (initial - target) := by ring
  have hLog := congrArg Real.log hRetention
  have hLogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  rw [Real.log_exp, hLogHalf] at hLog
  unfold bornRateFromTick
  field_simp [ne_of_gt hDuration]
  nlinarith

/-- In the intrinsic birth-count clock, one birth is one unit and the unique
dimensionless equilibration rate is `log 2`. -/
theorem unitBirthClock_forces_log_two
    (rate target initial : ℝ) (hOffShell : initial ≠ target)
    (hTick : continuousBornRadius rate target initial 1 =
      (target + initial) / 2) :
    rate = Real.log 2 := by
  have h := midpoint_birthTick_forces_rate rate 1 target initial
    (by norm_num) hOffShell hTick
  simpa [bornRateFromTick] using h

/-! ### Exact-flow versus implicit-Euler calibration

The same midpoint update can be read either as an exact sample of the
continuous semigroup or as one implicit-Euler approximation.  Those readings
do not assign the same generator rate.  The exact-flow reading used above
gives `rate * duration = log 2`; implicit Euler gives
`rate * duration = 1`.  The discrete law alone therefore fixes the retention
but not a dimensionful continuous generator until its clock interpretation is
named. -/

/-- An off-shell midpoint interpreted as implicit Euler uniquely fixes the
dimensionless coupling to one. -/
theorem midpoint_implicitEuler_forces_coupling
    (rate duration target current : ℝ)
    (hRate : 0 ≤ rate) (hDuration : 0 < duration)
    (hOffShell : current ≠ target)
    (hMidpoint : weightedBornStep 1 (duration * rate) target current =
      (target + current) / 2) :
    duration * rate = 1 := by
  have hDenominator : 1 + duration * rate ≠ 0 := by
    positivity
  unfold weightedBornStep at hMidpoint
  field_simp [hDenominator] at hMidpoint
  have hFactor :
      (1 - duration * rate) * (current - target) = 0 := by
    nlinarith
  have hCurrentDefect : current - target ≠ 0 :=
    sub_ne_zero.mpr hOffShell
  have hCoupling :=
    (mul_eq_zero.mp hFactor).resolve_right hCurrentDefect
  linarith

theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at h ⊢
  exact h

/-- The exact-semigroup and implicit-Euler readings are provably distinct.
This is the precise residual calibration choice, not a hidden algebraic
freedom in either reading. -/
theorem exactFlow_rate_ne_implicitEuler_rate :
    Real.log 2 ≠ (1 : ℝ) := ne_of_lt log_two_lt_one

/-! ## 2. Causal counting supplies the physical tick duration -/

/-- Proper duration assigned to one counted causal interval event in four
spacetime dimensions. -/
def oneBirthProperTime (density : ℝ) : ℝ :=
  proper_time_from_counting 4 1 density

theorem oneBirthProperTime_pos (density : ℝ) (hDensity : 0 < density) :
    0 < oneBirthProperTime density := by
  unfold oneBirthProperTime proper_time_from_counting alexandrov_constant
  simp only [OfNat.ofNat]
  apply Real.rpow_pos_of_pos
  exact div_pos one_pos (mul_pos hDensity (div_pos Real.pi_pos (by norm_num)))

/-- Dimensionful causal Born-equilibration rate fixed by density-calibrated
proper time. -/
def causalBornRate (density : ℝ) : ℝ :=
  bornRateFromTick (oneBirthProperTime density)

theorem causalBornRate_pos (density : ℝ) (hDensity : 0 < density) :
    0 < causalBornRate density := by
  exact bornRateFromTick_pos _ (oneBirthProperTime_pos density hDensity)

/-- One density-calibrated causal birth still implements exactly the midpoint
law; changing density changes physical seconds per birth, not the response per
birth. -/
theorem continuousBornRadius_at_counted_birth
    (density target initial : ℝ) (hDensity : 0 < density) :
    continuousBornRadius (causalBornRate density) target initial
        (oneBirthProperTime density) =
      (target + initial) / 2 := by
  exact continuousBornRadius_at_birthTick _ _ _
    (oneBirthProperTime_pos density hDensity)

/-- The rate-times-duration product is parameter-free. -/
theorem causalBornRate_times_birthTime
    (density : ℝ) (hDensity : 0 < density) :
    causalBornRate density * oneBirthProperTime density = Real.log 2 := by
  exact bornRateFromTick_mul_duration _
    (ne_of_gt (oneBirthProperTime_pos density hDensity))

/-! ## 3. A reversible system-bath dilation -/

/-- Real plane rotation acting on system and bath radial defects. -/
def bornBathRotation
    (cosine sine : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  (cosine * state.1 + sine * state.2,
    -sine * state.1 + cosine * state.2)

/-- The complementary bath coefficient associated with a contractive system
retention. -/
def bornBathLeakage (retention : ℝ) : ℝ :=
  Real.sqrt (1 - retention ^ 2)

theorem bornBathLeakage_sq
    (retention : ℝ) (hRetentionZero : 0 ≤ retention)
    (hRetentionOne : retention ≤ 1) :
    bornBathLeakage retention ^ 2 = 1 - retention ^ 2 := by
  unfold bornBathLeakage
  exact Real.sq_sqrt (sub_nonneg.mpr (by nlinarith))

theorem bornBath_circle
    (retention : ℝ) (hRetentionZero : 0 ≤ retention)
    (hRetentionOne : retention ≤ 1) :
    retention ^ 2 + bornBathLeakage retention ^ 2 = 1 := by
  rw [bornBathLeakage_sq retention hRetentionZero hRetentionOne]
  ring

/-- The two-mode dilation conserves total radial defect energy. -/
theorem bornBathRotation_energy
    (cosine sine : ℝ) (hCircle : cosine ^ 2 + sine ^ 2 = 1)
    (state : ℝ × ℝ) :
    (bornBathRotation cosine sine state).1 ^ 2 +
        (bornBathRotation cosine sine state).2 ^ 2 =
      state.1 ^ 2 + state.2 ^ 2 := by
  unfold bornBathRotation
  nlinarith

/-- Reversing the bath angle exactly inverts the microscopic coupling. -/
theorem bornBathRotation_inverse
    (cosine sine : ℝ) (hCircle : cosine ^ 2 + sine ^ 2 = 1)
    (state : ℝ × ℝ) :
    bornBathRotation cosine (-sine)
        (bornBathRotation cosine sine state) = state := by
  apply Prod.ext
  · change cosine * (cosine * state.1 + sine * state.2) +
        (-sine) * (-sine * state.1 + cosine * state.2) = state.1
    calc
      _ = (cosine ^ 2 + sine ^ 2) * state.1 := by ring
      _ = state.1 := by rw [hCircle, one_mul]
  · change -(-sine) * (cosine * state.1 + sine * state.2) +
        cosine * (-sine * state.1 + cosine * state.2) = state.2
    calc
      _ = (cosine ^ 2 + sine ^ 2) * state.2 := by ring
      _ = state.2 := by rw [hCircle, one_mul]

/-- Retention of the positive-time flow lies in the closed unit interval. -/
theorem continuousBornRetention_mem_Icc
    (rate time : ℝ) (hRate : 0 ≤ rate) (hTime : 0 ≤ time) :
    Real.exp (-(rate * time)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Real.exp_nonneg _
  · exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hRate hTime))

/-- Microscopic system-bath state for an initial radial defect and a vacuum
bath. -/
def continuousBornBathState
    (rate target initial time : ℝ) : ℝ × ℝ :=
  let retention := Real.exp (-(rate * time))
  bornBathRotation retention (bornBathLeakage retention)
    (initial - target, 0)

/-- Projecting the reversible dilation to the system gives exactly the
continuous Born-equilibration law. -/
theorem continuousBornBathState_system
    (rate target initial time : ℝ) :
    target + (continuousBornBathState rate target initial time).1 =
      continuousBornRadius rate target initial time := by
  simp [continuousBornBathState, bornBathRotation, continuousBornRadius]

/-- At positive causal time, the full system-bath state conserves the initial
defect energy exactly. -/
theorem continuousBornBathState_energy
    (rate target initial time : ℝ)
    (hRate : 0 ≤ rate) (hTime : 0 ≤ time) :
    (continuousBornBathState rate target initial time).1 ^ 2 +
        (continuousBornBathState rate target initial time).2 ^ 2 =
      (initial - target) ^ 2 := by
  let retention := Real.exp (-(rate * time))
  have hRetention := continuousBornRetention_mem_Icc rate time hRate hTime
  have hCircle : retention ^ 2 + bornBathLeakage retention ^ 2 = 1 :=
    bornBath_circle retention hRetention.1 hRetention.2
  have hEnergy := bornBathRotation_energy retention
    (bornBathLeakage retention) hCircle (initial - target, 0)
  simpa [continuousBornBathState, retention] using hEnergy

/-- The apparently lost system defect is stored exactly in the bath mode. -/
theorem continuousBornBathState_bath_energy
    (rate target initial time : ℝ)
    (hRate : 0 ≤ rate) (hTime : 0 ≤ time) :
    (continuousBornBathState rate target initial time).2 ^ 2 =
      (1 - Real.exp (-(rate * time)) ^ 2) * (initial - target) ^ 2 := by
  let retention := Real.exp (-(rate * time))
  have hRetention := continuousBornRetention_mem_Icc rate time hRate hTime
  have hLeakage := bornBathLeakage_sq retention hRetention.1 hRetention.2
  unfold continuousBornBathState bornBathRotation
  change (-bornBathLeakage retention * (initial - target) + retention * 0) ^ 2 =
    (1 - retention ^ 2) * (initial - target) ^ 2
  rw [mul_zero, add_zero, mul_pow, neg_sq, hLeakage]

/-- The continuous microscopic coupling is reversible before the bath is
discarded. -/
theorem continuousBornBathState_recoverable
    (rate target initial time : ℝ)
    (hRate : 0 ≤ rate) (hTime : 0 ≤ time) :
    bornBathRotation (Real.exp (-(rate * time)))
        (-bornBathLeakage (Real.exp (-(rate * time))))
        (continuousBornBathState rate target initial time) =
      (initial - target, 0) := by
  have hRetention := continuousBornRetention_mem_Icc rate time hRate hTime
  exact bornBathRotation_inverse _ _
    (bornBath_circle _ hRetention.1 hRetention.2) _

/-! ## 4. Fresh-bath collisions reproduce sequential growth -/

/-- Reduced defect after coupling once to a fresh vacuum bath mode. -/
def bornBathReducedDefect (retention defect : ℝ) : ℝ :=
  (bornBathRotation retention (bornBathLeakage retention) (defect, 0)).1

@[simp]
theorem bornBathReducedDefect_eq (retention defect : ℝ) :
    bornBathReducedDefect retention defect = retention * defect := by
  simp [bornBathReducedDefect, bornBathRotation]

/-- Iterated collision model, with one fresh vacuum bath mode per causal
birth. -/
def iteratedBornBathDefect (retention initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | step + 1 =>
      bornBathReducedDefect retention
        (iteratedBornBathDefect retention initial step)

theorem iteratedBornBathDefect_closed
    (retention initial : ℝ) (step : ℕ) :
    iteratedBornBathDefect retention initial step =
      retention ^ step * initial := by
  induction step with
  | zero => simp [iteratedBornBathDefect]
  | succ step ih =>
      rw [iteratedBornBathDefect, bornBathReducedDefect_eq, ih, pow_succ]
      ring

/-- Equal-weight causal births are exactly repeated half-retention vacuum-bath
collisions. -/
theorem bornRadialRadius_eq_freshBathCollisions
    (target initial : ℝ) (step : ℕ) :
    bornRadialRadius target initial step =
      target + iteratedBornBathDefect (1 / 2) (initial - target) step := by
  rw [bornRadialRadius_closed, iteratedBornBathDefect_closed]

/-! ## 5. Capstone and axiom audit -/

/-- The complete finite derivation: the causal birth tick fixes the rate and
the reduced trajectory is the projection of reversible, energy-conserving
system-bath dynamics. -/
theorem causalBornRateAndDilation_capstone
    (density target initial : ℝ) (hDensity : 0 < density) :
    causalBornRate density > 0 ∧
      continuousBornRadius (causalBornRate density) target initial
          (oneBirthProperTime density) = (target + initial) / 2 ∧
      (continuousBornBathState (causalBornRate density) target initial
          (oneBirthProperTime density)).1 ^ 2 +
          (continuousBornBathState (causalBornRate density) target initial
            (oneBirthProperTime density)).2 ^ 2 =
        (initial - target) ^ 2 := by
  refine ⟨causalBornRate_pos density hDensity,
    continuousBornRadius_at_counted_birth density target initial hDensity,
    ?_⟩
  exact continuousBornBathState_energy _ _ _ _
    (le_of_lt (causalBornRate_pos density hDensity))
    (le_of_lt (oneBirthProperTime_pos density hDensity))

#print axioms midpoint_birthTick_forces_rate
#print axioms unitBirthClock_forces_log_two
#print axioms midpoint_implicitEuler_forces_coupling
#print axioms exactFlow_rate_ne_implicitEuler_rate
#print axioms continuousBornRadius_at_counted_birth
#print axioms bornBathRotation_energy
#print axioms bornBathRotation_inverse
#print axioms continuousBornBathState_system
#print axioms continuousBornBathState_energy
#print axioms continuousBornBathState_recoverable
#print axioms bornRadialRadius_eq_freshBathCollisions
#print axioms causalBornRateAndDilation_capstone

end

end UnifiedTheory.Audit.KFCausalBornRateAndDilation

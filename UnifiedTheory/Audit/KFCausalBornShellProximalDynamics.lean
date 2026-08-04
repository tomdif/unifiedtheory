/-
  Audit/KFCausalBornShellProximalDynamics.lean

  LOCAL ACTION AND PHYSICAL MASS LAW FOR BORN-SHELL RELAXATION

  The radial relaxation module introduced the effective update

      r' = (R + r) / 2.

  This file derives that update from a one-step local variational principle.
  The local action is the sum of the squared microscopic displacement and the
  squared residual Born defect,

      A_R(r;s) = (s-r)^2 + (s-R)^2.

  Completing the square proves that its unique minimizer is `s = (R+r)/2`.
  Equivalently, the update is the implicit-Euler equation

      s-r = R-s,

  so the displacement made in one tick equals the defect left after the tick.
  This identifies the half-defect law as the canonical equal-weight proximal
  step, while the previous affine-family theorem retains the freedom to change
  the microscopic clock by changing the relative weights.

  The second half translates the radial dynamics back to the observable Born
  mass of the full supported causal amplitude.  It proves that the actual mass
  equals the uniform mass plus the squared carrier radius, converges to one,
  never crosses the Born shell, and reduces its absolute error to at most
  `3/4` of its previous value per microscopic tick.  These statements concern the full causal
  profile, not only an auxiliary carrier norm.

  The local action is still an effective dissipative input.  This module does
  not claim that it follows from closed unitary dynamics; the linear no-go in
  the imported module proves that it cannot do so on the same carrier.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornShellProximalDynamics

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Topology
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics

universe u

/-! ## 1. The local proximal action -/

/-- One-tick dissipative action.  The two terms penalize, respectively,
microscopic motion and the Born defect remaining after the tick. -/
def bornLocalAction (target current candidate : ℝ) : ℝ :=
  (candidate - current) ^ 2 + (candidate - target) ^ 2

/-- Exact completion of the square for the local action. -/
theorem bornLocalAction_completeSquare (target current candidate : ℝ) :
    bornLocalAction target current candidate =
      2 * (candidate - (target + current) / 2) ^ 2 +
        (target - current) ^ 2 / 2 := by
  unfold bornLocalAction
  ring

/-- The midpoint has the irreducible one-step action cost. -/
theorem bornLocalAction_midpoint (target current : ℝ) :
    bornLocalAction target current ((target + current) / 2) =
      (target - current) ^ 2 / 2 := by
  rw [bornLocalAction_completeSquare]
  ring

/-- The Born midpoint minimizes the local action globally. -/
theorem bornLocalAction_midpoint_le
    (target current candidate : ℝ) :
    bornLocalAction target current ((target + current) / 2) ≤
      bornLocalAction target current candidate := by
  rw [bornLocalAction_midpoint, bornLocalAction_completeSquare]
  nlinarith [sq_nonneg (candidate - (target + current) / 2)]

/-- The local minimizer is unique. -/
theorem bornLocalAction_eq_midpoint_iff
    (target current candidate : ℝ) :
    bornLocalAction target current candidate =
        bornLocalAction target current ((target + current) / 2) ↔
      candidate = (target + current) / 2 := by
  rw [bornLocalAction_completeSquare, bornLocalAction_midpoint]
  constructor
  · intro h
    have hSq : (candidate - (target + current) / 2) ^ 2 = 0 := by
      linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hSq)
  · intro h
    subst candidate
    ring

/-- The dynamical update is exactly the unique proximal minimizer at every
microscopic time. -/
theorem bornRadialRadius_succ_unique_local_minimizer
    (target initial : ℝ) (step : ℕ) :
    (∀ candidate,
      bornLocalAction target (bornRadialRadius target initial step)
          (bornRadialRadius target initial (step + 1)) ≤
        bornLocalAction target (bornRadialRadius target initial step)
          candidate) ∧
    (∀ candidate,
      bornLocalAction target (bornRadialRadius target initial step) candidate =
          bornLocalAction target (bornRadialRadius target initial step)
            (bornRadialRadius target initial (step + 1)) ↔
        candidate = bornRadialRadius target initial (step + 1)) := by
  rw [bornRadialRadius_succ]
  constructor
  · exact bornLocalAction_midpoint_le target
      (bornRadialRadius target initial step)
  · exact bornLocalAction_eq_midpoint_iff target
      (bornRadialRadius target initial step)

/-! ## 1a. Weighted rigidity and the origin of the retention coefficient -/

/-- General local action with independent microscopic inertia and Born
restoring strength. -/
def weightedBornLocalAction
    (inertia restoring target current candidate : ℝ) : ℝ :=
  inertia * (candidate - current) ^ 2 +
    restoring * (candidate - target) ^ 2

/-- Candidate selected by the weighted local action. -/
def weightedBornStep
    (inertia restoring target current : ℝ) : ℝ :=
  (inertia * current + restoring * target) / (inertia + restoring)

/-- Completion of the square for the general weighted action. -/
theorem weightedBornLocalAction_completeSquare
    (inertia restoring target current candidate : ℝ)
    (hTotal : inertia + restoring ≠ 0) :
    weightedBornLocalAction inertia restoring target current candidate =
      (inertia + restoring) *
          (candidate - weightedBornStep inertia restoring target current) ^ 2 +
        (inertia * restoring / (inertia + restoring)) *
          (current - target) ^ 2 := by
  unfold weightedBornLocalAction weightedBornStep
  field_simp [hTotal]
  ring

/-- Exact irreducible cost at the weighted step. -/
theorem weightedBornLocalAction_at_step
    (inertia restoring target current : ℝ)
    (hTotal : inertia + restoring ≠ 0) :
    weightedBornLocalAction inertia restoring target current
        (weightedBornStep inertia restoring target current) =
      (inertia * restoring / (inertia + restoring)) *
        (current - target) ^ 2 := by
  rw [weightedBornLocalAction_completeSquare _ _ _ _ _ hTotal]
  ring

/-- Positive inertia and restoring strength force a unique local minimizer. -/
theorem weightedBornLocalAction_unique_minimizer
    (inertia restoring target current candidate : ℝ)
    (hInertia : 0 < inertia) (hRestoring : 0 < restoring) :
    weightedBornLocalAction inertia restoring target current candidate =
        weightedBornLocalAction inertia restoring target current
          (weightedBornStep inertia restoring target current) ↔
      candidate = weightedBornStep inertia restoring target current := by
  have hTotalPos : 0 < inertia + restoring := add_pos hInertia hRestoring
  have hTotal : inertia + restoring ≠ 0 := ne_of_gt hTotalPos
  rw [weightedBornLocalAction_completeSquare _ _ _ _ _ hTotal,
    weightedBornLocalAction_at_step _ _ _ _ hTotal]
  constructor
  · intro h
    have hSq :
        (candidate - weightedBornStep inertia restoring target current) ^ 2 = 0 := by
      nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hSq)
  · intro h
    subst candidate
    ring

/-- The weighted minimizer retains exactly the inertia fraction of the old
radial defect. -/
theorem weightedBornStep_sub_target
    (inertia restoring target current : ℝ)
    (hTotal : inertia + restoring ≠ 0) :
    weightedBornStep inertia restoring target current - target =
      (inertia / (inertia + restoring)) * (current - target) := by
  unfold weightedBornStep
  field_simp [hTotal]
  ring

/-- Equal microscopic penalties are precisely the half-defect law used by the
causal relaxation module. -/
theorem weightedBornStep_one_one (target current : ℝ) :
    weightedBornStep 1 1 target current = (target + current) / 2 := by
  unfold weightedBornStep
  ring

/-- For positive coefficients the induced retention lies strictly between
zero and one, so the weighted proximal dynamics has the same universal Born
attractor established for the affine defect semigroup. -/
theorem weightedBornRetention_mem_Ioo
    (inertia restoring : ℝ)
    (hInertia : 0 < inertia) (hRestoring : 0 < restoring) :
    inertia / (inertia + restoring) ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos hInertia (add_pos hInertia hRestoring)
  · exact (div_lt_one (add_pos hInertia hRestoring)).mpr (by linarith)

/-! ## 2. Force balance and implicit Euler uniqueness -/

/-- One step moves by exactly the Born defect that remains after the step.
This is the implicit-Euler equation for the restoring force `R-r`. -/
theorem bornRadialRadius_implicitEuler
    (target initial : ℝ) (step : ℕ) :
    bornRadialRadius target initial (step + 1) -
        bornRadialRadius target initial step =
      target - bornRadialRadius target initial (step + 1) := by
  rw [bornRadialRadius_succ]
  ring

/-- The implicit force-balance equation uniquely forces the midpoint. -/
theorem implicitBornBalance_iff
    (target current candidate : ℝ) :
    candidate - current = target - candidate ↔
      candidate = (target + current) / 2 := by
  constructor <;> intro h <;> linarith

/-- Any update law satisfying the local implicit balance is the already
formalized radial dynamics. -/
theorem bornRadialRadius_unique_of_implicit_balance
    (target initial : ℝ) (flow : ℕ → ℝ)
    (hZero : flow 0 = initial)
    (hBalance : ∀ step,
      flow (step + 1) - flow step = target - flow (step + 1)) :
    ∀ step, flow step = bornRadialRadius target initial step := by
  intro step
  induction step with
  | zero => simpa using hZero
  | succ step ih =>
      rw [bornRadialRadius_succ, ← ih]
      exact (implicitBornBalance_iff target (flow step)
        (flow (step + 1))).mp (hBalance step)

/-! ## 3. The scalar observable Born-mass dynamics -/

/-- Born mass in the orthogonal decomposition into a fixed uniform component
and a zero-sum carrier of the stated radius. -/
def radialBornMass (uniform radius : ℝ) : ℝ :=
  uniform + radius ^ 2

theorem radialBornMass_target_eq_one
    (uniform target : ℝ) (hShell : uniform + target ^ 2 = 1) :
    radialBornMass uniform target = 1 := by
  simpa [radialBornMass] using hShell

/-- Exact one-step mass-error law.  Unlike the squared radial Lyapunov defect,
the physical Born-mass error has a state-dependent contraction factor. -/
theorem radialBornMass_error_succ
    (uniform target initial : ℝ) (step : ℕ)
    (hShell : uniform + target ^ 2 = 1) :
    radialBornMass uniform
          (bornRadialRadius target initial (step + 1)) - 1 =
      (bornRadialRadius target initial step - target) *
        (bornRadialRadius target initial step + 3 * target) / 4 := by
  rw [bornRadialRadius_succ]
  unfold radialBornMass
  nlinarith

/-- Current mass error factors into radial defect times the positive radial
sum. -/
theorem radialBornMass_error_factor
    (uniform target radius : ℝ)
    (hShell : uniform + target ^ 2 = 1) :
    radialBornMass uniform radius - 1 =
      (radius - target) * (radius + target) := by
  unfold radialBornMass
  nlinarith

/-- For nonnegative radii the physical mass error contracts to at most
`3/4` of its previous value at every tick. -/
theorem radialBornMass_abs_error_succ_le
    (uniform target initial : ℝ) (step : ℕ)
    (hShell : uniform + target ^ 2 = 1)
    (hTarget : 0 ≤ target) (hInitial : 0 ≤ initial) :
    |radialBornMass uniform
          (bornRadialRadius target initial (step + 1)) - 1| ≤
      (3 / 4 : ℝ) *
        |radialBornMass uniform
          (bornRadialRadius target initial step) - 1| := by
  let radius := bornRadialRadius target initial step
  have hRadius : 0 ≤ radius :=
    bornRadialRadius_nonneg target initial hTarget hInitial step
  rw [radialBornMass_error_succ uniform target initial step hShell,
    radialBornMass_error_factor uniform target radius hShell]
  change |(radius - target) * (radius + 3 * target) / 4| ≤
    (3 / 4 : ℝ) * |(radius - target) * (radius + target)|
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ radius + 3 * target),
    abs_of_nonneg (by positivity : 0 ≤ radius + target)]
  nlinarith [abs_nonneg (radius - target)]

/-- The scalar physical Born mass converges to one. -/
theorem radialBornMass_tendsto_one
    (uniform target initial : ℝ)
    (hShell : uniform + target ^ 2 = 1) :
    Filter.Tendsto
      (fun step => radialBornMass uniform
        (bornRadialRadius target initial step))
      Filter.atTop (nhds 1) := by
  have hRadius := bornRadialRadius_tendsto target initial
  have hUniform : Filter.Tendsto (fun _ : ℕ => uniform)
      Filter.atTop (nhds uniform) := tendsto_const_nhds
  have hMass := hUniform.add (hRadius.pow 2)
  simpa [radialBornMass, hShell] using hMass

/-- The sign of the mass error is conserved: relaxation approaches the shell
without crossing it. -/
theorem radialBornMass_error_sign_preserved
    (uniform target initial : ℝ) (step : ℕ)
    (hShell : uniform + target ^ 2 = 1)
    (hTarget : 0 ≤ target) (hInitial : 0 ≤ initial) :
    0 ≤
      (radialBornMass uniform initial - 1) *
        (radialBornMass uniform
          (bornRadialRadius target initial step) - 1) := by
  rw [radialBornMass_error_factor uniform target initial hShell,
    radialBornMass_error_factor uniform target
      (bornRadialRadius target initial step) hShell]
  have hPow : 0 ≤ (1 / 2 : ℝ) ^ step := by positivity
  have hRadius : 0 ≤ bornRadialRadius target initial step :=
    bornRadialRadius_nonneg target initial hTarget hInitial step
  have hSumInitial : 0 ≤ initial + target := by positivity
  have hSumStep : 0 ≤ bornRadialRadius target initial step + target := by
    positivity
  have hDefect :
      bornRadialRadius target initial step - target =
        (1 / 2 : ℝ) ^ step * (initial - target) := by
    rw [bornRadialRadius_closed]
    ring
  rw [hDefect]
  have hFactor :
      (initial - target) * (initial + target) *
          ((1 / 2 : ℝ) ^ step * (initial - target) *
            (bornRadialRadius target initial step + target)) =
        (1 / 2 : ℝ) ^ step * (initial - target) ^ 2 *
          (initial + target) *
            (bornRadialRadius target initial step + target) := by
    ring
  rw [hFactor]
  positivity

/-! ## 4. Identification with the actual supported causal amplitude -/

/-- The real radial expression for the full supported causal Born mass. -/
def supportBornRelaxedMass
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) : ℝ :=
  (support.card : ℝ)⁻¹ +
    ‖supportBornRelaxation support amplitude step‖ ^ 2

/-- The target carrier radius is exactly the radius required to make the full
supported Born mass equal one. -/
theorem supportBornTargetRadius_sq
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty) :
    supportBornTargetRadius support ^ 2 =
      1 - (support.card : ℝ)⁻¹ := by
  unfold supportBornTargetRadius
  apply Real.sq_sqrt
  have hCardPositive : (0 : ℝ) < support.card := by
    exact_mod_cast (Finset.card_pos.mpr hSupport)
  have hCardOne : (1 : ℝ) ≤ support.card := by
    exact_mod_cast (Finset.one_le_card.mpr hSupport)
  exact sub_nonneg.mpr ((inv_le_one₀ hCardPositive).mpr hCardOne)

/-- A function supported on `support` has the same full and support-restricted
Born masses. -/
theorem finiteComplexBornMass_eq_supportComplexBornMass_of_supported
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hZero : ∀ branch, branch ∉ support → amplitude branch = 0) :
    finiteComplexBornMass amplitude =
      supportComplexBornMass support amplitude := by
  classical
  unfold finiteComplexBornMass supportComplexBornMass
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro branch _hUniv hBranch
  rw [hZero branch hBranch]
  simp

/-- The sum over the physical support equals the full coherent sum for a
supported amplitude. -/
theorem sum_support_eq_sum_of_supported
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hZero : ∀ branch, branch ∉ support → amplitude branch = 0) :
    (∑ branch ∈ support, amplitude branch) = ∑ branch, amplitude branch := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro branch _hUniv hBranch
  exact hZero branch hBranch

/-- The radial mass is not a proxy: it is exactly the real value of the Born
mass of the full, finite-time causal amplitude profile. -/
theorem finiteSupportBornRelaxedAmplitude_bornMass
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (step : ℕ) :
    finiteComplexBornMass
        (finiteSupportBornRelaxedAmplitude support amplitude step) =
      (supportBornRelaxedMass support amplitude step : ℂ) := by
  let relaxed := finiteSupportBornRelaxedAmplitude support amplitude step
  have hZero : ∀ branch, branch ∉ support → relaxed branch = 0 := by
    intro branch hBranch
    exact finiteSupportBornRelaxedAmplitude_eq_zero_of_not_mem
      support amplitude step branch hBranch
  have hFullCoherent : ∑ branch, relaxed branch = 1 := by
    exact finiteSupportBornRelaxedAmplitude_sum_one
      support hSupport amplitude hCoherent step
  have hSupportCoherent : ∑ branch ∈ support, relaxed branch = 1 := by
    rw [sum_support_eq_sum_of_supported support relaxed hZero]
    exact hFullCoherent
  have hDifference := supportBornExcess_eq_complex_difference
    support hSupport relaxed hSupportCoherent
  have hNormSq := supportCenteredVector_norm_sq support relaxed
  rw [supportCenteredVector_relaxedAmplitude] at hNormSq
  rw [finiteComplexBornMass_eq_supportComplexBornMass_of_supported
    support relaxed hZero]
  unfold supportBornRelaxedMass
  have hUniform : supportUniformAmplitude support =
      ((support.card : ℝ)⁻¹ : ℂ) := by
    simp [supportUniformAmplitude]
  rw [hUniform] at hDifference
  have hNormSqComplex :
      ((‖supportBornRelaxation support amplitude step‖ ^ 2 : ℝ) : ℂ) =
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
          ((‖supportBornRelaxation support amplitude step‖ ^ 2 : ℝ) : ℂ) := by
      rw [hNormSqComplex]
    _ = (((support.card : ℝ)⁻¹ +
          ‖supportBornRelaxation support amplitude step‖ ^ 2 : ℝ) : ℂ) := by
      norm_cast

/-- The actual finite-time mass is the scalar radial mass from Section 3. -/
theorem supportBornRelaxedMass_eq_radialBornMass
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support)
    (step : ℕ) :
    supportBornRelaxedMass support amplitude step =
      radialBornMass (support.card : ℝ)⁻¹
        (bornRadialRadius (supportBornTargetRadius support)
          ‖supportCenteredVector support amplitude‖ step) := by
  unfold supportBornRelaxedMass radialBornMass supportBornRelaxation
  rw [bornRadialRelaxation_norm _ _ step
    (supportBornTargetRadius_nonneg support)
    (supportCenteredVector_ne_zero_of_nonuniform
      support amplitude hNonuniform)]

/-- Observable Born mass converges to one for every coherent nonuniform
multi-successor causal profile. -/
theorem supportBornRelaxedMass_tendsto_one
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    Filter.Tendsto (supportBornRelaxedMass support amplitude)
      Filter.atTop (nhds 1) := by
  have hShell : (support.card : ℝ)⁻¹ +
      supportBornTargetRadius support ^ 2 = 1 := by
    rw [supportBornTargetRadius_sq support hSupport]
    ring
  have hScalar := radialBornMass_tendsto_one
    (support.card : ℝ)⁻¹ (supportBornTargetRadius support)
    ‖supportCenteredVector support amplitude‖ hShell
  apply hScalar.congr'
  filter_upwards [] with step
  exact (supportBornRelaxedMass_eq_radialBornMass
    support amplitude hNonuniform step).symm

/-- The actual Born-mass error contracts to at most `3/4` of its previous
value per microscopic tick.  The sharper `1/4` law belongs to the squared
radial Lyapunov defect. -/
theorem supportBornRelaxedMass_abs_error_succ_le
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support)
    (step : ℕ) :
    |supportBornRelaxedMass support amplitude (step + 1) - 1| ≤
      (3 / 4 : ℝ) *
        |supportBornRelaxedMass support amplitude step - 1| := by
  have hShell : (support.card : ℝ)⁻¹ +
      supportBornTargetRadius support ^ 2 = 1 := by
    rw [supportBornTargetRadius_sq support hSupport]
    ring
  rw [supportBornRelaxedMass_eq_radialBornMass
      support amplitude hNonuniform (step + 1),
    supportBornRelaxedMass_eq_radialBornMass
      support amplitude hNonuniform step]
  exact radialBornMass_abs_error_succ_le
    (support.card : ℝ)⁻¹ (supportBornTargetRadius support)
    ‖supportCenteredVector support amplitude‖ step hShell
    (supportBornTargetRadius_nonneg support) (norm_nonneg _)

/-- Capstone: the same causal trajectory is simultaneously the unique local
proximal evolution and an observable normalization flow whose exact finite
profiles converge to Born mass one. -/
theorem causalBornProximalDynamics_capstone
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    (∀ step candidate,
      bornLocalAction (supportBornTargetRadius support)
          (bornRadialRadius (supportBornTargetRadius support)
            ‖supportCenteredVector support amplitude‖ step)
          (bornRadialRadius (supportBornTargetRadius support)
            ‖supportCenteredVector support amplitude‖ (step + 1)) ≤
        bornLocalAction (supportBornTargetRadius support)
          (bornRadialRadius (supportBornTargetRadius support)
            ‖supportCenteredVector support amplitude‖ step) candidate) ∧
      Filter.Tendsto (supportBornRelaxedMass support amplitude)
        Filter.atTop (nhds 1) ∧
      (∀ step,
        finiteComplexBornMass
            (finiteSupportBornRelaxedAmplitude support amplitude step) =
          (supportBornRelaxedMass support amplitude step : ℂ)) := by
  refine ⟨?_, supportBornRelaxedMass_tendsto_one
    support hSupport amplitude hNonuniform, ?_⟩
  · intro step candidate
    exact (bornRadialRadius_succ_unique_local_minimizer
      (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ step).1 candidate
  · intro step
    exact finiteSupportBornRelaxedAmplitude_bornMass
      support hSupport amplitude hCoherent step

#print axioms bornLocalAction_eq_midpoint_iff
#print axioms weightedBornLocalAction_unique_minimizer
#print axioms weightedBornStep_sub_target
#print axioms weightedBornRetention_mem_Ioo
#print axioms bornRadialRadius_unique_of_implicit_balance
#print axioms radialBornMass_abs_error_succ_le
#print axioms radialBornMass_error_sign_preserved
#print axioms finiteSupportBornRelaxedAmplitude_bornMass
#print axioms supportBornRelaxedMass_tendsto_one
#print axioms supportBornRelaxedMass_abs_error_succ_le
#print axioms causalBornProximalDynamics_capstone

end

end UnifiedTheory.Audit.KFCausalBornShellProximalDynamics

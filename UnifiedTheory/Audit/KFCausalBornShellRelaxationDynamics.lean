/-
  Audit/KFCausalBornShellRelaxationDynamics.lean

  DISSIPATIVE MICRODYNAMICS FOR THE CAUSAL BORN SHELL

  The preceding Born-shell module characterized the physical square-root
  correction as the unique least-changing coherent Born completion.  That is
  a variational characterization, not yet a dynamics.  This file supplies a
  local dissipative law on the zero-sum carrier and proves that the same
  correction is its unique nonzero attractor.

  The microscopic law is radial and isotropic.  If `r` is the present carrier
  norm and `R` the Born-one radius, one tick obeys

      r' = r + (R - r) / 2 = (R + r) / 2.

  The factor `1/2` fixes only the unit of discrete relaxation time.  The
  physical fixed point is independent of that convention.  The squared
  radial defect is a strict Lyapunov function: it contracts by exactly `1/4`
  per tick.  Lifting the scalar law without rotating the carrier gives a
  norm-convergent dynamics whose endpoint is the canonical radial shell point.
  On an actual causal successor support, that endpoint is definitionally the
  explicit Born-shell correction already used by the all-rank growth law.

  Thus least Hilbert disturbance and ray preservation are no longer separate
  microscopic postulates once this restoring dynamics is adopted: both are
  consequences of its attractor theorem.  What remains proposed, rather than
  derived from continuum experiment, is the isotropic dissipative response
  law itself.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Topology
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

universe u

/-! ## 1. The scalar microscopic relaxation law -/

/-- Radius after `step` microscopic relaxation ticks.  Each tick replaces the
current radius by its arithmetic mean with the Born target radius. -/
def bornRadialRadius (target initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | step + 1 => (target + bornRadialRadius target initial step) / 2

@[simp]
theorem bornRadialRadius_zero (target initial : ℝ) :
    bornRadialRadius target initial 0 = initial := rfl

@[simp]
theorem bornRadialRadius_succ (target initial : ℝ) (step : ℕ) :
    bornRadialRadius target initial (step + 1) =
      (target + bornRadialRadius target initial step) / 2 := rfl

/-- The radial defect is halved exactly at every microscopic tick. -/
theorem bornRadialRadius_sub_target_succ
    (target initial : ℝ) (step : ℕ) :
    bornRadialRadius target initial (step + 1) - target =
      (bornRadialRadius target initial step - target) / 2 := by
  simp only [bornRadialRadius_succ]
  ring

/-- Closed form of the discrete restoring dynamics. -/
theorem bornRadialRadius_closed
    (target initial : ℝ) (step : ℕ) :
    bornRadialRadius target initial step =
      target + (1 / 2 : ℝ) ^ step * (initial - target) := by
  induction step with
  | zero => simp
  | succ step ih =>
      rw [bornRadialRadius_succ, ih, pow_succ]
      ring

/-- Nonnegative target and initial radii remain nonnegative. -/
theorem bornRadialRadius_nonneg
    (target initial : ℝ) (hTarget : 0 ≤ target) (hInitial : 0 ≤ initial) :
    ∀ step, 0 ≤ bornRadialRadius target initial step := by
  intro step
  induction step with
  | zero => simpa using hInitial
  | succ step ih =>
      rw [bornRadialRadius_succ]
      positivity

/-- A positive target makes every positive-time radius strictly positive. -/
theorem bornRadialRadius_pos
    (target initial : ℝ) (hTarget : 0 < target) (hInitial : 0 ≤ initial) :
    ∀ step, 0 < bornRadialRadius target initial (step + 1) := by
  intro step
  rw [bornRadialRadius_succ]
  have hNonneg := bornRadialRadius_nonneg target initial
    (le_of_lt hTarget) hInitial step
  positivity

/-- The target radius is the unique fixed point of one relaxation tick. -/
theorem bornRadialRadius_fixed_iff (target initial : ℝ) :
    bornRadialRadius target initial 1 = initial ↔ initial = target := by
  simp only [bornRadialRadius_succ, bornRadialRadius_zero]
  constructor <;> intro h
  · linarith
  · subst initial
    ring

/-- Squared radial Born defect, the exact Lyapunov function for the law. -/
def bornRadialLyapunov (target radius : ℝ) : ℝ :=
  (radius - target) ^ 2

theorem bornRadialLyapunov_nonneg (target radius : ℝ) :
    0 ≤ bornRadialLyapunov target radius := by
  exact sq_nonneg _

theorem bornRadialLyapunov_eq_zero_iff (target radius : ℝ) :
    bornRadialLyapunov target radius = 0 ↔ radius = target := by
  simp [bornRadialLyapunov, sub_eq_zero]

/-- The Lyapunov function contracts by exactly one quarter per tick. -/
theorem bornRadialLyapunov_succ
    (target initial : ℝ) (step : ℕ) :
    bornRadialLyapunov target
        (bornRadialRadius target initial (step + 1)) =
      (1 / 4 : ℝ) *
        bornRadialLyapunov target
          (bornRadialRadius target initial step) := by
  unfold bornRadialLyapunov
  rw [bornRadialRadius_sub_target_succ]
  ring

/-- Away from the Born shell, every microscopic tick strictly decreases the
radial Lyapunov function. -/
theorem bornRadialLyapunov_strict_decrease
    (target initial : ℝ) (step : ℕ)
    (hOffShell : bornRadialRadius target initial step ≠ target) :
    bornRadialLyapunov target
        (bornRadialRadius target initial (step + 1)) <
      bornRadialLyapunov target
        (bornRadialRadius target initial step) := by
  rw [bornRadialLyapunov_succ]
  have hPositive : 0 < bornRadialLyapunov target
      (bornRadialRadius target initial step) := by
    rw [bornRadialLyapunov, sq_pos_iff]
    exact sub_ne_zero.mpr hOffShell
  nlinarith

/-- The scalar microscopic dynamics converges to the Born radius from every
initial radius. -/
theorem bornRadialRadius_tendsto (target initial : ℝ) :
    Filter.Tendsto (bornRadialRadius target initial)
      Filter.atTop (nhds target) := by
  have hPow : Filter.Tendsto (fun step : ℕ => (1 / 2 : ℝ) ^ step)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hClosed : bornRadialRadius target initial =
      fun step => target + (1 / 2 : ℝ) ^ step * (initial - target) := by
    funext step
    exact bornRadialRadius_closed target initial step
  rw [hClosed]
  simpa using tendsto_const_nhds.add (hPow.mul_const (initial - target))

/-! ## 1a. Rigidity of local linear shell relaxation -/

/-- General time-homogeneous linear relaxation of the radial Born defect.
`retention` is the fraction of the previous defect retained in one tick. -/
def affineBornDefectFlow
    (retention target initial : ℝ) (step : ℕ) : ℝ :=
  target + retention ^ step * (initial - target)

@[simp]
theorem affineBornDefectFlow_zero
    (retention target initial : ℝ) :
    affineBornDefectFlow retention target initial 0 = initial := by
  simp [affineBornDefectFlow]

/-- Exact local response law for the general affine flow. -/
theorem affineBornDefectFlow_succ_sub_target
    (retention target initial : ℝ) (step : ℕ) :
    affineBornDefectFlow retention target initial (step + 1) - target =
      retention *
        (affineBornDefectFlow retention target initial step - target) := by
  simp [affineBornDefectFlow, pow_succ]
  ring

/-- The affine defect law is a genuine discrete semigroup. -/
theorem affineBornDefectFlow_add
    (retention target initial : ℝ) (first second : ℕ) :
    affineBornDefectFlow retention target initial (first + second) =
      affineBornDefectFlow retention target
        (affineBornDefectFlow retention target initial second) first := by
  simp [affineBornDefectFlow, pow_add]
  ring

/-- **Rigidity theorem for the deeper scalar law.**  Any time-homogeneous
flow whose one-step local response retains a fixed fraction of the radial
defect is forced at every depth to be `affineBornDefectFlow`.  No projection
or least-distance condition occurs in the hypotheses. -/
theorem affineBornDefectFlow_unique
    (retention target : ℝ) (flow : ℕ → ℝ → ℝ)
    (hZero : ∀ initial, flow 0 initial = initial)
    (hStep : ∀ step initial,
      flow (step + 1) initial - target =
        retention * (flow step initial - target)) :
    ∀ step initial,
      flow step initial =
        affineBornDefectFlow retention target initial step := by
  intro step
  induction step with
  | zero =>
      intro initial
      rw [hZero]
      exact (affineBornDefectFlow_zero retention target initial).symm
  | succ step ih =>
      intro initial
      have hLocal := hStep step initial
      rw [ih initial] at hLocal
      have hCanonical := affineBornDefectFlow_succ_sub_target
        retention target initial step
      linarith

/-- Every stable member of the rigid family converges to the same Born shell;
the retention coefficient changes only the relaxation rate. -/
theorem affineBornDefectFlow_tendsto
    (retention target initial : ℝ)
    (hRetentionNonnegative : 0 ≤ retention)
    (hRetentionContractive : retention < 1) :
    Filter.Tendsto (affineBornDefectFlow retention target initial)
      Filter.atTop (nhds target) := by
  have hPow : Filter.Tendsto (fun step : ℕ => retention ^ step)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      hRetentionNonnegative hRetentionContractive
  unfold affineBornDefectFlow
  simpa using tendsto_const_nhds.add (hPow.mul_const (initial - target))

/-- The half-defect dynamics used below is the `retention = 1/2` member of
the unique stable affine family.  Its numerical rate is a time calibration,
not an additional selection of the Born endpoint. -/
theorem bornRadialRadius_eq_affineBornDefectFlow
    (target initial : ℝ) (step : ℕ) :
    bornRadialRadius target initial step =
      affineBornDefectFlow (1 / 2) target initial step := by
  rw [bornRadialRadius_closed]
  rfl

/-! ## 2. Lift to an isotropic carrier dynamics -/

/-- Lift the scalar relaxation to a nonzero real normed carrier without
rotating it.  The dynamics is therefore equivariant under every linear
isometry and preserves the physical zero-sum ray. -/
def bornRadialRelaxation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ) : E :=
  (bornRadialRadius target ‖centered‖ step / ‖centered‖) • centered

@[simp]
theorem bornRadialRelaxation_zero
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (hCentered : centered ≠ 0) :
    bornRadialRelaxation target centered 0 = centered := by
  unfold bornRadialRelaxation
  rw [bornRadialRadius_zero, div_self (norm_ne_zero_iff.mpr hCentered), one_smul]

/-- The lifted carrier has exactly the scalar radius prescribed by the local
microscopic law. -/
theorem bornRadialRelaxation_norm
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ)
    (hTarget : 0 ≤ target) (hCentered : centered ≠ 0) :
    ‖bornRadialRelaxation target centered step‖ =
      bornRadialRadius target ‖centered‖ step := by
  unfold bornRadialRelaxation
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg
      (bornRadialRadius_nonneg target ‖centered‖ hTarget
        (norm_nonneg centered) step)
      (norm_nonneg centered))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hCentered)

/-- Every finite-time carrier state lies on the same nonnegative ray as the
initial state. -/
theorem bornRadialRelaxation_sameRay
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ) (hTarget : 0 ≤ target) :
    SameRay ℝ (bornRadialRelaxation target centered step) centered := by
  exact (SameRay.sameRay_nonneg_smul_right centered
    (div_nonneg
      (bornRadialRadius_nonneg target ‖centered‖ hTarget
        (norm_nonneg centered) step)
      (norm_nonneg centered))).symm

/-- The microscopic law is exactly isotropic: changing carrier coordinates by
any real linear isometry commutes with every relaxation tick. -/
theorem bornRadialRelaxation_equivariant
    {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (equiv : E ≃ₗᵢ[ℝ] F) (target : ℝ) (centered : E) (step : ℕ) :
    equiv (bornRadialRelaxation target centered step) =
      bornRadialRelaxation target (equiv centered) step := by
  simp [bornRadialRelaxation, LinearIsometryEquiv.norm_map]

/-- Exact carrier-space error relative to the Born-shell equilibrium. -/
theorem bornRadialRelaxation_distance_to_equilibrium
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ)
    (hCentered : centered ≠ 0) :
    ‖bornRadialRelaxation target centered step -
        canonicalRadialShellPoint target centered‖ =
      (1 / 2 : ℝ) ^ step * |‖centered‖ - target| := by
  have hNormNe : ‖centered‖ ≠ 0 := norm_ne_zero_iff.mpr hCentered
  have hPowNonneg : 0 ≤ (1 / 2 : ℝ) ^ step := by positivity
  unfold bornRadialRelaxation canonicalRadialShellPoint
  rw [← sub_smul]
  have hScalar :
      bornRadialRadius target ‖centered‖ step / ‖centered‖ -
          target / ‖centered‖ =
        (bornRadialRadius target ‖centered‖ step - target) /
          ‖centered‖ := by
    field_simp
  rw [hScalar, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (norm_nonneg centered), div_mul_cancel₀ _ hNormNe]
  rw [bornRadialRadius_closed]
  simp only [add_sub_cancel_left, abs_mul, abs_pow]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Carrier-space error is halved exactly at every tick. -/
theorem bornRadialRelaxation_distance_succ
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (step : ℕ)
    (hCentered : centered ≠ 0) :
    ‖bornRadialRelaxation target centered (step + 1) -
        canonicalRadialShellPoint target centered‖ =
      (1 / 2 : ℝ) *
        ‖bornRadialRelaxation target centered step -
          canonicalRadialShellPoint target centered‖ := by
  rw [bornRadialRelaxation_distance_to_equilibrium target centered
      (step + 1) hCentered,
    bornRadialRelaxation_distance_to_equilibrium target centered
      step hCentered,
    pow_succ]
  ring

/-- The lifted microscopic dynamics converges in carrier norm to the canonical
Born-shell point. -/
theorem bornRadialRelaxation_tendsto
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : ℝ) (centered : E) (hCentered : centered ≠ 0) :
    Filter.Tendsto (bornRadialRelaxation target centered)
      Filter.atTop (nhds (canonicalRadialShellPoint target centered)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hPow : Filter.Tendsto (fun step : ℕ => (1 / 2 : ℝ) ^ step)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hDistance :
      (fun step => ‖bornRadialRelaxation target centered step -
          canonicalRadialShellPoint target centered‖) =
        fun step => (1 / 2 : ℝ) ^ step * |‖centered‖ - target| := by
    funext step
    exact bornRadialRelaxation_distance_to_equilibrium
      target centered step hCentered
  rw [hDistance]
  simpa using hPow.mul_const |‖centered‖ - target|

/-! ## 2a. Closed linear dynamics cannot implement the relaxation -/

theorem bornRadialRelaxation_real_one_step_one (target : ℝ) :
    bornRadialRelaxation target (1 : ℝ) 1 = (target + 1) / 2 := by
  norm_num [bornRadialRelaxation, bornRadialRadius]

theorem bornRadialRelaxation_real_one_step_two (target : ℝ) :
    bornRadialRelaxation target (2 : ℝ) 1 = (target + 2) / 2 := by
  norm_num [bornRadialRelaxation, bornRadialRadius]

/-- A nonzero Born target makes the first relaxation tick nonhomogeneous.
This is the finite tripwire separating the proposed dissipative completion
from closed linear or unitary quantum evolution. -/
theorem bornRadialRelaxation_real_one_step_not_two_homogeneous
    (target : ℝ) (hTarget : target ≠ 0) :
    bornRadialRelaxation target (2 : ℝ) 1 ≠
      (2 : ℝ) • bornRadialRelaxation target (1 : ℝ) 1 := by
  rw [bornRadialRelaxation_real_one_step_one,
    bornRadialRelaxation_real_one_step_two]
  norm_num
  intro h
  apply hTarget
  linarith

/-- **Linear-dynamics no-go.**  No real linear operator implements even one
universal nonzero-target relaxation tick on all nonzero amplitudes.  Hence the
Born completion cannot be hidden inside a closed linear evolution on the same
carrier.  A physical implementation must be effective/conditional or arise
after coupling to discarded degrees of freedom. -/
theorem no_linear_operator_realizes_universal_Born_relaxation
    (target : ℝ) (hTarget : target ≠ 0) :
    ¬ ∃ evolution : ℝ →ₗ[ℝ] ℝ,
      ∀ centered : ℝ, centered ≠ 0 →
        evolution centered = bornRadialRelaxation target centered 1 := by
  rintro ⟨evolution, hEvolution⟩
  have hOne := hEvolution 1 (by norm_num)
  have hTwo := hEvolution 2 (by norm_num)
  have hLinear : evolution (2 : ℝ) =
      (2 : ℝ) • evolution (1 : ℝ) := by
    simpa using evolution.map_smul (2 : ℝ) (1 : ℝ)
  rw [hOne, hTwo] at hLinear
  exact bornRadialRelaxation_real_one_step_not_two_homogeneous
    target hTarget hLinear

/-! ## 3. The dynamics on an actual causal successor support -/

/-- Microscopic Born relaxation of the physical zero-sum successor carrier. -/
def supportBornRelaxation
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) :
    EuclideanSpace ℂ {branch : Branch // branch ∈ support} :=
  bornRadialRelaxation (supportBornTargetRadius support)
    (supportCenteredVector support amplitude) step

/-- Real scale that lifts the carrier relaxation back to a supported causal
amplitude profile at each finite microscopic time. -/
def supportBornRelaxationScale
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) : ℝ :=
  bornRadialRadius (supportBornTargetRadius support)
      ‖supportCenteredVector support amplitude‖ step /
    ‖supportCenteredVector support amplitude‖

/-- Full causal amplitude during relaxation: the invariant coherent component
is fixed and only the physical zero-sum carrier evolves. -/
def finiteSupportBornRelaxedAmplitude
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) :
    Branch → ℂ :=
  finiteSupportBornShellCorrection support
    (supportBornRelaxationScale support amplitude step : ℂ) amplitude

/-- The full finite-time profile realizes exactly the abstract carrier
dynamics, not merely the same sequence of norms. -/
theorem supportCenteredVector_relaxedAmplitude
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) :
    supportCenteredVector support
        (finiteSupportBornRelaxedAmplitude support amplitude step) =
      supportBornRelaxation support amplitude step := by
  unfold finiteSupportBornRelaxedAmplitude
  rw [supportCenteredVector_finiteSupportBornShellCorrection]
  rfl

/-- Coherent normalization is conserved at every finite microscopic time. -/
theorem finiteSupportBornRelaxedAmplitude_sum_one
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (step : ℕ) :
    ∑ branch, finiteSupportBornRelaxedAmplitude support amplitude step branch = 1 := by
  exact finiteSupportBornShellCorrection_sum_one support hSupport _ amplitude
    hCoherent

/-- The finite-time dynamics never creates a forbidden causal transition. -/
theorem finiteSupportBornRelaxedAmplitude_eq_zero_of_not_mem
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ)
    (branch : Branch) (hBranch : branch ∉ support) :
    finiteSupportBornRelaxedAmplitude support amplitude step branch = 0 := by
  simp [finiteSupportBornRelaxedAmplitude,
    finiteSupportBornShellCorrection, hBranch]

/-- At time zero the full profile agrees with the raw amplitude on every
physical successor. -/
theorem finiteSupportBornRelaxedAmplitude_zero_apply
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support)
    (branch : Branch) (hBranch : branch ∈ support) :
    finiteSupportBornRelaxedAmplitude support amplitude 0 branch =
      amplitude branch := by
  have hRawNe : ‖supportCenteredVector support amplitude‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (supportCenteredVector_ne_zero_of_nonuniform
      support amplitude hNonuniform)
  simp [finiteSupportBornRelaxedAmplitude, supportBornRelaxationScale,
    finiteSupportBornShellCorrection, hBranch, hRawNe,
    supportCenteredAmplitude]

/-- Actual causal Lyapunov function evaluated on the finite-time successor
carrier. -/
def supportBornRelaxationLyapunov
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) (step : ℕ) : ℝ :=
  bornRadialLyapunov (supportBornTargetRadius support)
    ‖supportBornRelaxation support amplitude step‖

/-- The causal Lyapunov function contracts by exactly one quarter at every
tick for every nonuniform physical successor law. -/
theorem supportBornRelaxationLyapunov_succ
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support)
    (step : ℕ) :
    supportBornRelaxationLyapunov support amplitude (step + 1) =
      (1 / 4 : ℝ) *
        supportBornRelaxationLyapunov support amplitude step := by
  have hRawNe := supportCenteredVector_ne_zero_of_nonuniform
    support amplitude hNonuniform
  unfold supportBornRelaxationLyapunov supportBornRelaxation
  rw [bornRadialRelaxation_norm _ _ (step + 1)
      (supportBornTargetRadius_nonneg support) hRawNe,
    bornRadialRelaxation_norm _ _ step
      (supportBornTargetRadius_nonneg support) hRawNe]
  exact bornRadialLyapunov_succ _ _ step

/-- At microscopic time zero the dynamics is the uncorrected physical
zero-sum amplitude. -/
theorem supportBornRelaxation_zero
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    supportBornRelaxation support amplitude 0 =
      supportCenteredVector support amplitude := by
  exact bornRadialRelaxation_zero _ _
    (supportCenteredVector_ne_zero_of_nonuniform
      support amplitude hNonuniform)

/-- **Dynamical derivation of the physical Born correction.**  The actual
support-relative correction is the norm-limit of the local isotropic
restoring dynamics. -/
theorem supportBornRelaxation_tendsto_physical_correction
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hMultiple : 1 < support.card)
    (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    Filter.Tendsto (supportBornRelaxation support amplitude)
      Filter.atTop
      (nhds (supportCenteredVector support
        (finiteSupportBornShellCorrection support
          (supportBornShellScale support
            (supportBornExcess support amplitude)) amplitude))) := by
  have hRawNe := supportCenteredVector_ne_zero_of_nonuniform
    support amplitude hNonuniform
  have hTendsto := bornRadialRelaxation_tendsto
    (supportBornTargetRadius support)
    (supportCenteredVector support amplitude)
    hRawNe
  rw [supportBornShellCorrection_centered_eq_canonicalRadial
    support hMultiple amplitude hNonuniform]
  exact hTendsto

/-- Exact finite-time error to the implemented causal Born correction. -/
theorem supportBornRelaxation_exact_error
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hMultiple : 1 < support.card)
    (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support)
    (step : ℕ) :
    ‖supportBornRelaxation support amplitude step -
        supportCenteredVector support
          (finiteSupportBornShellCorrection support
            (supportBornShellScale support
              (supportBornExcess support amplitude)) amplitude)‖ =
      (1 / 2 : ℝ) ^ step *
        |‖supportCenteredVector support amplitude‖ -
          supportBornTargetRadius support| := by
  rw [supportBornShellCorrection_centered_eq_canonicalRadial
    support hMultiple amplitude hNonuniform]
  exact bornRadialRelaxation_distance_to_equilibrium
    (supportBornTargetRadius support)
    (supportCenteredVector support amplitude) step
    (supportCenteredVector_ne_zero_of_nonuniform
      support amplitude hNonuniform)

/-- The physical microscopic correction is stationary exactly when the raw
zero-sum carrier already has the Born-one radius. -/
theorem supportBornRelaxation_fixed_iff
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) :
    bornRadialRadius (supportBornTargetRadius support)
        ‖supportCenteredVector support amplitude‖ 1 =
        ‖supportCenteredVector support amplitude‖ ↔
      ‖supportCenteredVector support amplitude‖ =
        supportBornTargetRadius support := by
  exact bornRadialRadius_fixed_iff _ _

/-- The theorem-level physics ledger: a nonuniform causal amplitude starts at
the raw carrier, its exact Lyapunov defect contracts by `1/4` per tick, and it
converges to the unique least-changing coherent Born completion. -/
theorem causalBornRelaxation_capstone
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (hMultiple : 1 < support.card)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    supportBornRelaxation support amplitude 0 =
        supportCenteredVector support amplitude ∧
      Filter.Tendsto (supportBornRelaxation support amplitude)
        Filter.atTop
        (nhds (supportCenteredVector support
          (finiteSupportBornShellCorrection support
            (supportBornShellScale support
              (supportBornExcess support amplitude)) amplitude))) ∧
      (∑ branch,
        finiteSupportBornShellCorrection support
          (supportBornShellScale support
            (supportBornExcess support amplitude)) amplitude branch = 1) ∧
      finiteComplexBornMass
        (finiteSupportBornShellCorrection support
          (supportBornShellScale support
            (supportBornExcess support amplitude)) amplitude) = 1 := by
  refine ⟨supportBornRelaxation_zero support amplitude hNonuniform,
    supportBornRelaxation_tendsto_physical_correction
      support hMultiple amplitude hNonuniform, ?_, ?_⟩
  · exact finiteSupportBornShellCorrection_sum_one support hSupport _ amplitude
      hCoherent
  · apply finiteSupportBornShellCorrection_bornMass_one
      support hSupport _ amplitude hCoherent
    apply supportBornShellScale_solves_of_strict_excess
      support hMultiple amplitude (supportBornExcess support amplitude)
      (supportBornExcess_pos_of_nonuniform support amplitude hNonuniform)
    exact (supportBornExcess_eq_complex_difference
      support hSupport amplitude hCoherent).symm

#print axioms bornRadialLyapunov_strict_decrease
#print axioms affineBornDefectFlow_unique
#print axioms affineBornDefectFlow_tendsto
#print axioms bornRadialRelaxation_equivariant
#print axioms bornRadialRelaxation_tendsto
#print axioms no_linear_operator_realizes_universal_Born_relaxation
#print axioms finiteSupportBornRelaxedAmplitude_sum_one
#print axioms supportBornRelaxationLyapunov_succ
#print axioms supportBornRelaxation_tendsto_physical_correction
#print axioms causalBornRelaxation_capstone

end

end UnifiedTheory.Audit.KFCausalBornShellRelaxationDynamics

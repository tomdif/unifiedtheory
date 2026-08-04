/-
  Audit/KFCausalBornAutonomousDilationNoGo.lean

  THE FINITE-BATH AUTONOMY OBSTRUCTION

  The reversible plane rotation in `KFCausalBornRateAndDilation` dilates one
  chosen Born-relaxation step.  This file proves that reusing the same bath
  mode does not compose as the reduced exponential semigroup.

  If the system retention is `c` and the complementary bath coefficient is
  `s = sqrt (1-c^2)`, two rotations of the same system-bath pair have system
  coefficient `c^2-s^2`.  Two fresh-vacuum collisions have coefficient
  `c^2`.  They disagree for every strict contraction and every nonzero
  defect.  In continuous time this says that the pointwise rotations with
  `c(t)=exp(-gamma*t)` do not form a one-parameter group when `gamma,t>0`.

  Thus exact irreversible Born equilibration cannot be generated forever by
  repeatedly reusing this one finite bath coordinate.  The construction needs
  a reset, fresh modes, or an infinite environment.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornRateAndDilation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornAutonomousDilationNoGo

noncomputable section

open UnifiedTheory.Audit.KFCausalBornEquilibrationLaw
open UnifiedTheory.Audit.KFCausalBornRateAndDilation

/-- Reusing one bath mode for two identical rotations feeds the first leaked
defect back into the system. -/
theorem reusedBath_system_coefficient
    (retention leakage defect : ℝ) :
    (bornBathRotation retention leakage
      (bornBathRotation retention leakage (defect, 0))).1 =
        (retention ^ 2 - leakage ^ 2) * defect := by
  unfold bornBathRotation
  ring

/-- With the canonical complementary coefficient, same-bath reuse has system
coefficient `2*c^2-1`. -/
theorem reusedCanonicalBath_system_coefficient
    (retention defect : ℝ)
    (hRetentionZero : 0 ≤ retention) (hRetentionOne : retention ≤ 1) :
    (bornBathRotation retention (bornBathLeakage retention)
      (bornBathRotation retention (bornBathLeakage retention)
        (defect, 0))).1 =
      (2 * retention ^ 2 - 1) * defect := by
  rw [reusedBath_system_coefficient,
    bornBathLeakage_sq retention hRetentionZero hRetentionOne]
  ring

/-- Two collisions with independent vacuum modes retain `c^2` of the initial
defect. -/
theorem twoFreshBathCollisions_system_coefficient
    (retention defect : ℝ) :
    iteratedBornBathDefect retention defect 2 = retention ^ 2 * defect := by
  rw [iteratedBornBathDefect_closed]

/-- **Same-bath no-go.** For a strict contraction and a nonzero defect, reuse
of the same bath mode cannot reproduce two fresh-vacuum collisions. -/
theorem reusedBath_ne_twoFreshBathCollisions
    (retention defect : ℝ)
    (hRetentionZero : 0 ≤ retention) (hRetentionStrict : retention < 1)
    (hDefect : defect ≠ 0) :
    (bornBathRotation retention (bornBathLeakage retention)
      (bornBathRotation retention (bornBathLeakage retention)
        (defect, 0))).1 ≠
      iteratedBornBathDefect retention defect 2 := by
  rw [reusedCanonicalBath_system_coefficient retention defect
      hRetentionZero (le_of_lt hRetentionStrict),
    twoFreshBathCollisions_system_coefficient]
  intro hEqual
  have hFactor : (retention ^ 2 - 1) * defect = 0 := by
    linarith
  have hRetentionSq : retention ^ 2 ≠ 1 := by
    nlinarith
  exact (mul_ne_zero (sub_ne_zero.mpr hRetentionSq) hDefect) hFactor

/-- At the causal half-retention value, same-bath reuse sends a defect to
`-defect/2`, whereas fresh collisions send it to `defect/4`. -/
theorem halfRetention_reusedBath_system (defect : ℝ) :
    (bornBathRotation (1 / 2) (bornBathLeakage (1 / 2))
      (bornBathRotation (1 / 2) (bornBathLeakage (1 / 2))
        (defect, 0))).1 = -defect / 2 := by
  rw [reusedCanonicalBath_system_coefficient (1 / 2) defect]
  · ring
  · norm_num
  · norm_num

theorem halfRetention_twoFreshBaths_system (defect : ℝ) :
    iteratedBornBathDefect (1 / 2) defect 2 = defect / 4 := by
  rw [iteratedBornBathDefect_closed]
  norm_num
  ring

theorem halfRetention_reusedBath_ne_fresh
    (defect : ℝ) (hDefect : defect ≠ 0) :
    (bornBathRotation (1 / 2) (bornBathLeakage (1 / 2))
      (bornBathRotation (1 / 2) (bornBathLeakage (1 / 2))
        (defect, 0))).1 ≠
      iteratedBornBathDefect (1 / 2) defect 2 := by
  exact reusedBath_ne_twoFreshBathCollisions (1 / 2) defect
    (by norm_num) (by norm_num) hDefect

/-- Time-indexed member of the pointwise reversible dilation family. -/
def continuousBornBathRotation (rate time : ℝ) (state : ℝ × ℝ) : ℝ × ℝ :=
  let retention := Real.exp (-(rate * time))
  bornBathRotation retention (bornBathLeakage retention) state

/-- On a vacuum bath, the time-indexed rotation has the intended exponential
system projection. -/
theorem continuousBornBathRotation_system
    (rate time defect : ℝ) :
    (continuousBornBathRotation rate time (defect, 0)).1 =
      Real.exp (-(rate * time)) * defect := by
  simp [continuousBornBathRotation, bornBathRotation]

/-- The exact exponential coefficient at twice a time is the square of the
one-time coefficient. -/
theorem continuousBornRetention_two_mul
    (rate time : ℝ) :
    Real.exp (-(rate * (time + time))) =
      Real.exp (-(rate * time)) ^ 2 := by
  rw [show -(rate * (time + time)) =
      -(rate * time) + -(rate * time) by ring,
    Real.exp_add]
  ring

/-- **Autonomous two-mode no-go.** Although each member of the displayed
family is reversible, positive-rate rotations do not obey the time-addition
law on a nonzero vacuum-bath defect. -/
theorem continuousBornBathRotation_not_semigroup
    (rate time defect : ℝ)
    (hRate : 0 < rate) (hTime : 0 < time) (hDefect : defect ≠ 0) :
    continuousBornBathRotation rate (time + time) (defect, 0) ≠
      continuousBornBathRotation rate time
        (continuousBornBathRotation rate time (defect, 0)) := by
  intro hEqual
  have hFirst := congrArg Prod.fst hEqual
  let retention := Real.exp (-(rate * time))
  have hRetentionZero : 0 ≤ retention := le_of_lt (Real.exp_pos _)
  have hRetentionStrict : retention < 1 := by
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hRate hTime))
  have hLeft :
      (continuousBornBathRotation rate (time + time) (defect, 0)).1 =
        retention ^ 2 * defect := by
    rw [continuousBornBathRotation_system,
      continuousBornRetention_two_mul]
  have hRight :
      (continuousBornBathRotation rate time
        (continuousBornBathRotation rate time (defect, 0))).1 =
          (2 * retention ^ 2 - 1) * defect := by
    unfold continuousBornBathRotation
    exact reusedCanonicalBath_system_coefficient retention defect
      hRetentionZero (le_of_lt hRetentionStrict)
  rw [hLeft, hRight] at hFirst
  have hFactor : (retention ^ 2 - 1) * defect = 0 := by
    linarith
  have hRetentionSq : retention ^ 2 ≠ 1 := by
    nlinarith
  exact (mul_ne_zero (sub_ne_zero.mpr hRetentionSq) hDefect) hFactor

/-! ## Axiom audit -/

#print axioms reusedBath_ne_twoFreshBathCollisions
#print axioms halfRetention_reusedBath_ne_fresh
#print axioms continuousBornBathRotation_not_semigroup

end

end UnifiedTheory.Audit.KFCausalBornAutonomousDilationNoGo

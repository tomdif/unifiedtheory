/-
  Audit/KFCausalBornFreshModeCompatibility.lean

  FRESH-MODE COMPATIBILITY: AGED COLLISIONS AND THE FACTORIZATION BOUNDARY

  The growth-derived bath has one new orthogonal record slot at every birth.
  This file removes a possible overreading of the first construction.

  First, a constant local two-mode block is not required.  A retention and
  leakage pair may depend on birth rank.  The resulting dependent collision
  tower has exact closed forms:

    system at depth n = (product of retentions below n) * initial,
    record k = -leakage(k) * (product below k) * initial.

  If every rankwise pair lies on the unit circle, full system-plus-record
  energy is conserved at every finite depth.  The old constant-c law is the
  constant schedule specialization.

  Second, even the constant schedule is globally rank dependent: its carrier
  changes from `E × (Fin n → E)` to `E × (Fin (n+1) → E)`.  This is not one
  autonomous endomorphism of a fixed state space.

  These theorems make the interface to the Paper-3 aging result precise.  That
  result constrains stationary per-precursor amplitudes in the microscopic
  Markov/action-phase law.  The coefficient here is only a record-retention
  coefficient.  Identifying the two would require the schedule-dependent
  version; without that bridge, the constant record block does not contradict
  the aging theorem and does not derive microscopic coupling aging.

  No system/environment tensor product, density matrix, partial trace, or
  CPTP instrument is introduced here.  The carrier is a finite direct product
  (a direct-sum Hilbert carrier when E is Hilbert).  Consequently the causal
  cluster/factorization no-gos and this kinematic dilation have disjoint formal
  hypotheses.  Promoting record slots to independent factorizing causal
  subsystems is a separate bridge and remains open.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornGrowthFreshModes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornFreshModeCompatibility

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalBornGrowthFreshModes
open UnifiedTheory.Audit.KFCausalBornRateAndDilation

universe u

/-! ## 1. Rank-dependent fresh-mode collisions -/

/-- A collision schedule may age with causal birth rank. -/
structure CausalBirthCollisionSchedule where
  retention : ℕ → ℝ
  leakage : ℕ → ℝ

/-- Rankwise losslessness of an aged collision schedule. -/
def CausalBirthCollisionSchedule.IsLossless
    (schedule : CausalBirthCollisionSchedule) : Prop :=
  ∀ depth, schedule.retention depth ^ 2 + schedule.leakage depth ^ 2 = 1

/-- The constant collision law is a special schedule, not the only one. -/
def constantCausalBirthCollisionSchedule (retention leakage : ℝ) :
    CausalBirthCollisionSchedule where
  retention := fun _ => retention
  leakage := fun _ => leakage

/-- Product of all retention factors before a given birth rank. -/
def cumulativeCausalRetention
    (schedule : CausalBirthCollisionSchedule) (depth : ℕ) : ℝ :=
  ∏ rank ∈ Finset.range depth, schedule.retention rank

@[simp]
theorem cumulativeCausalRetention_zero
    (schedule : CausalBirthCollisionSchedule) :
    cumulativeCausalRetention schedule 0 = 1 := by
  simp [cumulativeCausalRetention]

theorem cumulativeCausalRetention_succ
    (schedule : CausalBirthCollisionSchedule) (depth : ℕ) :
    cumulativeCausalRetention schedule (depth + 1) =
      cumulativeCausalRetention schedule depth * schedule.retention depth := by
  simp [cumulativeCausalRetention, Finset.prod_range_succ]

/-- System plus all records under a rank-dependent collision schedule. -/
def scheduledCausalGrowthFreshModeTrajectory
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (schedule : CausalBirthCollisionSchedule) (initial : E) :
    ∀ depth : ℕ, E × CausalGrowthBath E depth
  | 0 => (initial, fun mode => Fin.elim0 mode)
  | depth + 1 =>
      causalGrowthFreshModeCollision
        (schedule.retention depth) (schedule.leakage depth)
        (scheduledCausalGrowthFreshModeTrajectory schedule initial depth)

@[simp]
theorem scheduledCausalGrowthFreshModeTrajectory_zero
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (schedule : CausalBirthCollisionSchedule) (initial : E) :
    scheduledCausalGrowthFreshModeTrajectory schedule initial 0 =
      (initial, fun mode => Fin.elim0 mode) := rfl

@[simp]
theorem scheduledCausalGrowthFreshModeTrajectory_succ
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (schedule : CausalBirthCollisionSchedule) (initial : E) (depth : ℕ) :
    scheduledCausalGrowthFreshModeTrajectory schedule initial (depth + 1) =
      causalGrowthFreshModeCollision
        (schedule.retention depth) (schedule.leakage depth)
        (scheduledCausalGrowthFreshModeTrajectory schedule initial depth) := rfl

/-- The reduced defect is controlled by the product of all earlier retention
coefficients, so an aged microscopic identification naturally produces an
aged, rather than geometric, relaxation law. -/
theorem scheduledCausalGrowthFreshModeTrajectory_system
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (schedule : CausalBirthCollisionSchedule) (initial : E) :
    ∀ depth : ℕ,
      (scheduledCausalGrowthFreshModeTrajectory schedule initial depth).1 =
        cumulativeCausalRetention schedule depth • initial
  | 0 => by simp
  | depth + 1 => by
      rw [scheduledCausalGrowthFreshModeTrajectory_succ,
        causalGrowthFreshModeCollision_system,
        scheduledCausalGrowthFreshModeTrajectory_system,
        cumulativeCausalRetention_succ]
      simp [smul_smul, mul_comm]

/-- Birth slot `k` stores the leakage at that rank multiplied by every prior
retention.  Later collisions never rewrite it. -/
theorem scheduledCausalGrowthFreshModeTrajectory_record
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (schedule : CausalBirthCollisionSchedule) (initial : E) :
    ∀ (depth : ℕ) (mode : CausalBirthMode depth),
      (scheduledCausalGrowthFreshModeTrajectory schedule initial depth).2 mode =
        ((-schedule.leakage mode.val) *
          cumulativeCausalRetention schedule mode.val) • initial
  | 0, mode => Fin.elim0 mode
  | depth + 1, mode => by
      refine Fin.lastCases ?_ (fun old => ?_) mode
      · change
          (causalGrowthFreshModeCollision
            (schedule.retention depth) (schedule.leakage depth)
            (scheduledCausalGrowthFreshModeTrajectory schedule initial depth)).2
              (newbornCausalBirthMode depth) =
            ((-schedule.leakage depth) *
              cumulativeCausalRetention schedule depth) • initial
        rw [causalGrowthFreshModeCollision_new_record,
          scheduledCausalGrowthFreshModeTrajectory_system]
        simp [smul_smul]
      · rw [scheduledCausalGrowthFreshModeTrajectory_succ,
          causalGrowthFreshModeCollision_old_record,
          scheduledCausalGrowthFreshModeTrajectory_record]
        rfl

/-- Exact norm conservation survives arbitrary rank dependence provided each
local collision is lossless. -/
theorem scheduledCausalGrowthFreshModeTrajectory_total_energy
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (schedule : CausalBirthCollisionSchedule)
    (hLossless : schedule.IsLossless) (initial : E) :
    ∀ depth : ℕ,
      ‖(scheduledCausalGrowthFreshModeTrajectory schedule initial depth).1‖ ^ 2 +
          causalGrowthBathEnergy depth
            (scheduledCausalGrowthFreshModeTrajectory schedule initial depth).2 =
        ‖initial‖ ^ 2
  | 0 => by simp [causalGrowthBathEnergy]
  | depth + 1 => by
      rw [scheduledCausalGrowthFreshModeTrajectory_succ,
        causalGrowthFreshModeCollision_total_energy
          (schedule.retention depth) (schedule.leakage depth)
          (hLossless depth)]
      exact scheduledCausalGrowthFreshModeTrajectory_total_energy
        schedule hLossless initial depth

/-! ## 2. Constant schedule and global rank dependence -/

/-- The original constant-retention trajectory is exactly the constant
schedule specialization. -/
theorem scheduledConstantTrajectory_eq_constantTrajectory
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (retention leakage : ℝ) (initial : E) : ∀ depth : ℕ,
    scheduledCausalGrowthFreshModeTrajectory
        (constantCausalBirthCollisionSchedule retention leakage)
        initial depth =
      causalGrowthFreshModeTrajectory retention leakage initial depth
  | 0 => rfl
  | depth + 1 => by
      rw [scheduledCausalGrowthFreshModeTrajectory_succ,
        causalGrowthFreshModeTrajectory_succ,
        scheduledConstantTrajectory_eq_constantTrajectory]
      rfl

/-- Even when the local rotation coefficient is constant, every causal step
increases the record-mode count.  Thus the global dependent evolution knows
the epoch through its changing carrier. -/
theorem constantCollision_global_recordCarrier_ages (depth : ℕ) :
    Fintype.card (CausalBirthMode (depth + 1)) =
      Fintype.card (CausalBirthMode depth) + 1 := by
  simp [CausalBirthMode]

/-- The half-retention Born law is only the constant member of the schedule
family; the kinematics itself does not force stationarity. -/
theorem halfRetentionTrajectory_is_constantSchedule
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (initial : E) (depth : ℕ) :
    scheduledCausalGrowthFreshModeTrajectory
        (constantCausalBirthCollisionSchedule
          (1 / 2) (bornBathLeakage (1 / 2))) initial depth =
      causalGrowthFreshModeTrajectory
        (1 / 2) (bornBathLeakage (1 / 2)) initial depth :=
  scheduledConstantTrajectory_eq_constantTrajectory
    (1 / 2) (bornBathLeakage (1 / 2)) initial depth

/-! ## Axiom audit -/

#print axioms scheduledCausalGrowthFreshModeTrajectory_system
#print axioms scheduledCausalGrowthFreshModeTrajectory_record
#print axioms scheduledCausalGrowthFreshModeTrajectory_total_energy
#print axioms scheduledConstantTrajectory_eq_constantTrajectory
#print axioms constantCollision_global_recordCarrier_ages
#print axioms halfRetentionTrajectory_is_constantSchedule

end

end UnifiedTheory.Audit.KFCausalBornFreshModeCompatibility

/- An explicit smooth cutoff supplies tensor approximation for every smooth
compact spacetime test supported in the middle half of the unit time window. -/
import UnifiedTheory.Audit.KFCausalSmoothTestApproximation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSmoothUnitWindow
noncomputable section
open Set Metric BoundedContinuousFunction
open scoped Topology ContDiff CompactlySupported
open UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests (Test)
open UnifiedTheory.Audit.KFCausalCompactTimeLocalization (Cutoff)
open UnifiedTheory.Audit.KFCausalTensorTestClosure (Approximable)
open UnifiedTheory.Audit.KFCausalSmoothTestApproximation

def bump : ContDiffBump (1/2 : ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoffValue : ℝ →ᵇ ℝ :=
  (⟨⟨bump,bump.continuous⟩,bump.hasCompactSupport⟩ : C_c(ℝ,ℝ)).toBoundedContinuousFunction

def cutoffDerivative : ℝ →ᵇ ℝ :=
  (⟨⟨deriv bump,(contDiff_infty_iff_deriv.mp
    (show ContDiff ℝ ∞ bump from bump.contDiff)).2.continuous⟩,
    bump.hasCompactSupport.deriv⟩ : C_c(ℝ,ℝ)).toBoundedContinuousFunction

def cutoff : Cutoff where
  value := cutoffValue
  derivative := cutoffDerivative
  hasDeriv t := ((show ContDiff ℝ 1 bump from bump.contDiff).differentiable (by norm_num) t).hasDerivAt
  support := by
    change tsupport bump ⊆ Icc 0 1
    rw [bump.tsupport_eq]
    intro t ht
    have hh : |t-1/2| ≤ (1/2 : ℝ) := by simpa [Real.dist_eq,bump] using ht
    rw [abs_le] at hh
    constructor <;> linarith [hh.1,hh.2]

theorem cutoff_one (t : ℝ) (ht : t ∈ Icc (1/4 : ℝ) (3/4)) :
    cutoff.value t = 1 := by
  change bump t = 1
  apply bump.one_of_mem_closedBall
  change dist t (1/2 : ℝ) ≤ (1/4 : ℝ)
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [ht.1,ht.2]

theorem approximable_unit_window (φ : Test)
    (hs : ∀ z, φ.value z ≠ 0 → z.1 ∈ Icc (1/4 : ℝ) (3/4)) :
    Approximable φ.toBCF φ.dt.toBCF φ.dp.toBCF :=
  approximable_of_cutoff_one cutoff φ (fun z hz => cutoff_one z.1 (hs z hz))

#print axioms cutoff
#print axioms cutoff_one
#print axioms approximable_unit_window
end
end UnifiedTheory.Audit.KFCausalSmoothUnitWindow

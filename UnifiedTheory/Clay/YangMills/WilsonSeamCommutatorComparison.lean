/- Full physical seam likelihood bounds at every input, with an explicit
noncommutation penalty. The original ground and temporal Haar integral
are retained. No ground-law smallness of the penalty is asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorComparison
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist WilsonGroundLocalComparison
open WilsonJointRotation WilsonDistributedSeam WilsonSeamCommutatorGeometry
open WilsonSingleLinkStaples (character character_continuous character_classFunction
  character_inverse_re)

variable (n : ℕ) [NeZero n]

/-- The two actual opposite inputs are gauge representatives of the same seam partner. -/
theorem kernel_lower (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (q u v : Slice n)
    (h : SliceGauge n Q) :
    Real.exp (-(β * (cost n q + mismatch n i q h u))) * kernelMap n β (u,v) ≤
      kernelMap n β (twist n i u,v) := by
  have hc (w : Slice n) :
      Continuous (fun k : SliceGauge n Q => slabAction character β 2 w v k) := by
    have hχ := character_continuous
    unfold slabAction temporalAction temporalHolonomy
    fun_prop
  have hk (k : SliceGauge n Q) : kernelMap n β (gaugeSlice k (twist n i u),v) =
      kernelMap n β (twist n i u,v) :=
    WilsonSlabGauge.kernel_gauge_left character character_classFunction
      character_inverse_re β 2 (twist n i u) v k
  have hh := CompactExponentialMidpoint.equal_midpoint (temporalHaar (n := n) (G := Q))
    (fun k => slabAction character β 2 u v k)
    (fun k => slabAction character β 2 (gaugeSlice h (twist n i u)) v k)
    (fun k => slabAction character β 2 (gaugeSlice h⁻¹ (twist n i u)) v k)
    (hc u) (hc _) (hc _) (2 * β * (cost n q + mismatch n i q h u))
    (slab_second n i β hβ q u v h) ((hk h).trans (hk h⁻¹).symm)
  have hs : -(2 * β * (cost n q + mismatch n i q h u))/2 =
      -(β * (cost n q + mismatch n i q h u)) := by ring
  change Real.exp _ * kernelMap n β (u,v) ≤
    kernelMap n β (gaugeSlice h (twist n i u),v) at hh
  simpa only [hs, hk h] using hh

theorem kernel_upper (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (q u v : Slice n)
    (h : SliceGauge n Q) :
    kernelMap n β (twist n i u,v) ≤
      Real.exp (β * (cost n q + mismatch n i q h u)) * kernelMap n β (u,v) := by
  have hh := kernel_lower n i β hβ q (twist n i u) v h
  rw [twist_involution, mismatch_twist] at hh
  have ht := mul_le_mul_of_nonneg_left hh
    (Real.exp_pos (β * (cost n q + mismatch n i q h u))).le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at ht

theorem root_kernel_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-(β * (Real.pi^2 * n + rootMismatch n i u))) * kernelMap n β (u,v) ≤
      kernelMap n β (twist n i u,v) ∧
    kernelMap n β (twist n i u,v) ≤
      Real.exp (β * (Real.pi^2 * n + rootMismatch n i u)) * kernelMap n β (u,v) := by
  have hc : β * (cost n (uniform n i (WilsonSeamRoot.root n)) + rootMismatch n i u) ≤
      β * (Real.pi^2 * n + rootMismatch n i u) := by
    apply mul_le_mul_of_nonneg_left _ hβ
    linarith only [WilsonSeamRoot.root_cost n i]
  have hp := (kernel_positive character character_continuous β 2 u v).le
  constructor
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hc)) hp).trans
      (kernel_lower n i β hβ (uniform n i (WilsonSeamRoot.root n)) u v
        (distributingGauge n i (WilsonSeamRoot.root n)))
  · exact (kernel_upper n i β hβ (uniform n i (WilsonSeamRoot.root n)) u v
      (distributingGauge n i (WilsonSeamRoot.root n))).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc) hp)

/-- Center symmetry cancels the actual ground values for every input. -/
theorem transition_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-(β * (Real.pi^2 * n + rootMismatch n i u))) * transition n β hβ u v ≤
      transition n β hβ (twist n i u) v ∧
    transition n β hβ (twist n i u) v ≤
      Real.exp (β * (Real.pi^2 * n + rootMismatch n i u)) * transition n β hβ u v := by
  have hp : 0 ≤ ground n β hβ v / (‖transfer n β‖ * ground n β hβ u) :=
    div_nonneg (ground_pos n β hβ v).le
      (mul_nonneg (norm_nonneg _) (ground_pos n β hβ u).le)
  have hh := root_kernel_bounds n i β hβ u v
  have hl := mul_le_mul_of_nonneg_right hh.1 hp
  have hu := mul_le_mul_of_nonneg_right hh.2 hp
  unfold transition GroundStateDirichlet.transition
  rw [ground_twist]
  constructor
  · simpa only [mul_div_assoc, mul_assoc] using hl
  · simpa only [mul_div_assoc, mul_assoc] using hu

theorem physical_likelihood_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    transition n β hβ (twist n i u) v / transition n β hβ u v ∈
      Set.Icc (Real.exp (-(β * (Real.pi^2 * n + rootMismatch n i u))))
        (Real.exp (β * (Real.pi^2 * n + rootMismatch n i u))) := by
  have hh := transition_bounds n i β hβ u v
  exact ⟨(le_div_iff₀ (transition_pos n β hβ u v)).mpr hh.1,
    (div_le_iff₀ (transition_pos n β hβ u v)).mpr hh.2⟩

/-- This includes nonflat common-axis fields and places no restriction on the output. -/
theorem commuting_input_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n)
    (hu : ∀ e, Commute (WilsonSeamRoot.root n) (u e)) :
    transition n β hβ (twist n i u) v / transition n β hβ u v ∈
      Set.Icc (Real.exp (-(β * Real.pi^2 * n))) (Real.exp (β * Real.pi^2 * n)) := by
  simpa only [rootMismatch_zero n i u hu, add_zero, mul_assoc] using
    physical_likelihood_bounds n i β hβ u v

end
end UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorComparison

/- A squared-displacement comparison for the full gauge-averaged kernel.
The opposite input rotations must have equal full kernels; no analogous
identity is silently imposed on the raw temporal-gauge kernel. -/
import UnifiedTheory.Clay.YangMills.CompactExponentialMidpoint
import UnifiedTheory.Clay.YangMills.WilsonJointRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGaugeKernelCurvature
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonJointRotation
open WilsonSingleLinkStaples (character character_continuous character_classFunction)

variable (n : ℕ) [NeZero n]

theorem slab_second (β : ℝ) (hβ : 0 ≤ β) (q u v : Slice n)
    (hp : potential character 2 (q * u) = potential character 2 u)
    (hm : potential character 2 (q⁻¹ * u) = potential character 2 u)
    (h : SliceGauge n Q) :
    slabAction character β 2 (q * u) v h + slabAction character β 2 (q⁻¹ * u) v h -
      2 * slabAction character β 2 u v h ≤ 2 * β * cost n q := by
  have hh := mul_le_mul_of_nonneg_left (kinetic_second_bound n q u (gaugeSlice h v)) hβ
  simp only [slabAction, temporalAction_eq character character_classFunction, hp, hm]
  nlinarith only [hh]

/-- Temporal Haar integration retains the symmetric second-difference gain. -/
theorem kernel_equal_lower (β : ℝ) (hβ : 0 ≤ β) (q u v : Slice n)
    (hp : potential character 2 (q * u) = potential character 2 u)
    (hm : potential character 2 (q⁻¹ * u) = potential character 2 u)
    (he : kernelMap n β (q * u, v) = kernelMap n β (q⁻¹ * u, v)) :
    Real.exp (-(β * cost n q)) * kernelMap n β (u, v) ≤ kernelMap n β (q * u, v) := by
  have hc (w : Slice n) :
      Continuous (fun h : SliceGauge n Q => slabAction character β 2 w v h) := by
    have hχ := character_continuous
    unfold slabAction temporalAction temporalHolonomy
    fun_prop
  have hh := CompactExponentialMidpoint.equal_midpoint (temporalHaar (n := n) (G := Q))
    (fun h => slabAction character β 2 u v h) (fun h => slabAction character β 2 (q * u) v h)
    (fun h => slabAction character β 2 (q⁻¹ * u) v h) (hc u) (hc (q * u)) (hc (q⁻¹ * u))
    (2 * β * cost n q) (slab_second n β hβ q u v hp hm) he
  have hs : -(2 * β * cost n q)/2 = -(β * cost n q) := by ring
  simpa only [hs] using hh

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeKernelCurvature

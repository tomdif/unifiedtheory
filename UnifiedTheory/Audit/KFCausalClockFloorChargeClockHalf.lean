/- The actual unbounded half-clock graph is invariant under charge rotation.
This follows from the bounded inverse, with its normalization and pointwise
multiplier identified explicitly. No charge-invariance condition on states. -/
import UnifiedTheory.Audit.KFCausalClockChargeMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockChargeMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)

def normalizedInverse (ε s : ℝ) : ℂ := (Real.sqrt ε : ℂ)*(Real.sqrt (Real.exp s+ε) : ℂ)⁻¹

theorem normalizedInverse_measurable (ε : ℝ) : Measurable (normalizedInverse ε) := by
  unfold normalizedInverse
  fun_prop

theorem normalizedInverse_bound (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    ‖normalizedInverse ε s‖ ≤ 1 := by
  rw [normalizedInverse,norm_mul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hb := inverseWeight_bound ε hε (s,0)
  have hn := (Real.sqrt_pos.mpr hε).ne'
  calc
    _ ≤ Real.sqrt ε*(Real.sqrt ε)⁻¹ :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = 1 := mul_inv_cancel₀ hn

theorem normalizedInverse_operator (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    clockMultiplier (normalizedInverse ε) (normalizedInverse_measurable ε)
      (normalizedInverse_bound ε hε) f = (Real.sqrt ε : ℂ) • inverseL ε hε f := by
  apply Lp.ext
  filter_upwards [clockMultiplier_coe (normalizedInverse ε) (normalizedInverse_measurable ε)
    (normalizedInverse_bound ε hε) f,inverseAction_coe ε hε f,
    Lp.coeFn_smul (Real.sqrt ε : ℂ) (inverseL ε hε f)] with x hm hi hs
  change (inverseL ε hε f) x = _ at hi
  rw [hm,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hi,normalizedInverse,mul_assoc]

theorem inverseL_action (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (f : Hilbert) :
    inverseL ε hε (action h hh θ f) = action h hh θ (inverseL ε hε f) := by
  have hc : (Real.sqrt ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε).ne'
  have he := multiplier_action (normalizedInverse ε) (normalizedInverse_measurable ε)
    (normalizedInverse_bound ε hε) h hh θ f
  rw [normalizedInverse_operator ε hε,normalizedInverse_operator ε hε,map_smul] at he
  exact (smul_right_injective _ hc) he

theorem clockHalf_graph_action (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (action h hh θ f,action h hh θ g) ∈ (clockHalf ε).graph := by
  rw [half_inverse_graph ε hε,inverseL_graph ε hε] at hfg ⊢
  rw [hfg,inverseL_action ε hε]

#print axioms normalizedInverse_measurable
#print axioms normalizedInverse_bound
#print axioms normalizedInverse_operator
#print axioms inverseL_action
#print axioms clockHalf_graph_action

end
end UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf

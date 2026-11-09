/- The actual complex displacement error vanishes after division by
sqrt(abs(hbar)). This works for both signs of hbar and keeps the neutral
shear. It supplies the Gaussian fluctuation coordinates, not just phases. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit
import UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (relativeScale shiftedPosition)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit

def sqrtRatio (h : ℝ) : ℝ := h/scale h

theorem sqrtRatio_norm (h : ℝ) : ‖sqrtRatio h‖ = scale h := by
  simp only [sqrtRatio,scale,Real.norm_eq_abs,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),Real.div_sqrt]

theorem sqrtRatio_tendsto : Tendsto sqrtRatio (𝓝 (0:ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [sqrtRatio_norm]
  have hi : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
  simpa only [scale,abs_zero,Real.sqrt_zero] using hi.abs.sqrt

def scaledDeviation (ε q h : ℝ) : ℂ := (relativeScale ε q h-1)/(scale h:ℂ)

theorem scaledDeviation_factor (ε q h : ℝ) (hh : h ≠ 0) :
    scaledDeviation ε q h = (sqrtRatio h:ℂ)*((h:ℂ)⁻¹*(relativeScale ε q h-1)) := by
  unfold scaledDeviation sqrtRatio
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hh]

theorem scaledDeviation_tendsto (ε q : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => scaledDeviation ε q (h n)) atTop (𝓝 0) := by
  have hn : Tendsto h atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun n => hh n)⟩
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (sqrtRatio_tendsto.comp hz)
  have ht := hr.mul ((relativeScale_slope ε q hε).comp hn)
  simp_rw [scaledDeviation_factor ε q _ (hh _)]
  simpa only [Complex.ofReal_zero,zero_mul] using ht

def shearVector (X : Transverse) (i : Fin 5) : ℝ :=
  if i = 4 then 2*(X 2+X 3) else X i

def fluctuation (ε q h : ℝ) (Q ξ : Transverse) (i : Fin 5) : ℂ :=
  (shiftedPosition ε q h (rescaledPosition h Q ξ) i-(Q i:ℂ))/(scale h:ℂ)

theorem fluctuation_eq (ε q h : ℝ) (hh : h ≠ 0) (Q ξ : Transverse) (i : Fin 5) :
    fluctuation ε q h Q ξ i = (ξ i:ℂ)+scaledDeviation ε q h*(shearVector (rescaledPosition h Q ξ) i:ℂ) := by
  have hs : (Real.sqrt |h| : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_positive h hh).ne'
  fin_cases i <;> simp [fluctuation,shiftedPosition,shearVector,rescaledPosition,scaledDeviation,scale]
  all_goals (field_simp [hs]; ring)

theorem fluctuation_tendsto (ε q : ℝ) (hε : 0 < ε) (Q ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) (i : Fin 5) :
    Tendsto (fun n => fluctuation ε q (h n) Q ξ i) atTop (𝓝 (ξ i:ℂ)) := by
  have hc : Continuous (fun X : Transverse => (shearVector X i:ℂ)) := by
    unfold shearVector
    split_ifs <;> fun_prop
  have hx := hc.continuousAt.tendsto.comp ((rescaledPosition_tendsto Q ξ).comp hz)
  have ht := ((scaledDeviation_tendsto ε q hε h hh hz).mul hx).const_add (ξ i:ℂ)
  simp_rw [fluctuation_eq ε q _ (hh _)]
  simpa only [zero_mul,add_zero] using ht

#print axioms sqrtRatio_norm
#print axioms sqrtRatio_tendsto
#print axioms scaledDeviation_factor
#print axioms scaledDeviation_tendsto
#print axioms fluctuation_eq
#print axioms fluctuation_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement

/- Quantitative propagation of the actual state's squeeze-orbit modulus.
The estimate uses the full physical energy, not a propagated generator
domain or a bounded replacement of the Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalSqueezeRateBound
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance
import UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance
import UnifiedTheory.Audit.KFCausalClockFloorCombinedDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeOrbitEstimate
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_compose)
open UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary (combined combined_apply)
open UnifiedTheory.Audit.KFCausalSqueezeChartCommutation (gauge_commutes)
open UnifiedTheory.Audit.KFCausalSqueezeRateBound
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeBalance
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEhrenfest (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (timeOutput differenceOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance (energy energy_monotone energy_comparison)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_norm)

def orbitGap (a : ℝ) (f : Hilbert) : ℝ := ‖transport a f-f‖^2
def budget (h T E : ℝ) : ℝ := (2*slopeBound/|h|)*T*Real.exp (2*T)*E

theorem orbitGap_characteristic (a : ℝ) (f : Hilbert) :
    orbitGap a f = 2*‖f‖^2-2*(inner ℂ f (transport a f)).re := by
  rw [orbitGap,norm_sub_rev,norm_sub_sq (𝕜 := ℂ),LinearIsometryEquiv.norm_map]
  simp only [RCLike.re_eq_complex_re]
  ring

theorem orbitGap_combined (ε h v t a : ℝ) (f : Hilbert) :
    orbitGap a (combined ε h v t f) = orbitGap a f := by
  have hc : transport a (combined ε h v t f) = combined ε h v t (transport a f) := by
    simp only [combined_apply,gauge_commutes,transport_compose,add_comm]
  unfold orbitGap
  rw [hc,← map_sub,LinearIsometryEquiv.norm_map]

theorem budget_nonnegative (h T E : ℝ) (hT : 0 ≤ T) (hE : 0 ≤ E) : 0 ≤ budget h T E := by
  unfold budget
  exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by have hc := slopeBound_positive; positivity)
    (abs_nonneg _)) hT) (Real.exp_pos _).le) hE

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "E" => energy ε hε h hne hh m g k
local notation "χ" => characteristic ε hε h hne hh m g k

theorem outputRate_bound (a s t : ℝ) (ha : |a| ≤ 1) (w : V) :
    ‖outputRate ε hε h hne hh m g k a s t w‖ ≤ (slopeBound/|h|)*|a| *E s t w := by
  let x := timeOutput ε hε h hne hh m g k t (F s t w)
  have he : ‖x‖^2 = E s t w := timeEnergy_actual ε hε h hne hh m g k t (F s t w)
  have hb : ‖inner ℂ x (differenceOutputLp a x)‖ ≤ (slopeBound*|a|)*‖x‖^2 := by
    calc
      _ ≤ ‖x‖*‖differenceOutputLp a x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖*((slopeBound*|a|)*‖x‖) :=
        mul_le_mul_of_nonneg_left (differenceOutputLp_bound a ha x) (norm_nonneg x)
      _ = _ := by ring
  change ‖coefficient h*inner ℂ x (differenceOutputLp a x)‖ ≤ _
  rw [norm_mul,coefficient_norm]
  calc
    _ ≤ (1/|h|)*((slopeBound*|a|)*‖x‖^2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (slopeBound/|h|)*|a| *E s t w := by rw [he]; ring

theorem characteristic_increment_bound (a s r t : ℝ) (ha : |a| ≤ 1) (hrt : r ≤ t) (w : V) :
    ‖χ a s t w-χ a s r w‖ ≤ (slopeBound/|h|)*|a| *E s t w*(t-r) := by
  have hb (z : ℝ) (hz : z ∈ Icc r t) :
      ‖outputRate ε hε h hne hh m g k a s z w‖ ≤ (slopeBound/|h|)*|a| *E s t w :=
    (outputRate_bound ε hε h hne hh m g k a s z ha w).trans
      (mul_le_mul_of_nonneg_left (energy_monotone ε hε h hne hh m g k s w hz.2)
        (by have hc := slopeBound_positive; positivity))
  have hd := (convex_Icc r t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc r t) => (bounded_squeeze_derivative ε hε h hne hh m g k a s z w).hasDerivWithinAt)
    hb (left_mem_Icc.mpr hrt) (right_mem_Icc.mpr hrt)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hrt)] using hd

theorem orbitGap_increment_bound (a s r t : ℝ) (ha : |a| ≤ 1) (hrt : r ≤ t) (w : V) :
    |orbitGap a (U s t (J w))-orbitGap a (U s r (J w))| ≤ budget h (t-r) (E s r w)*|a| := by
  have he : orbitGap a (U s t (J w))-orbitGap a (U s r (J w)) =
      -2*(χ a s t w-χ a s r w).re := by
    simp only [orbitGap_characteristic,evolution_norm,characteristic,Complex.sub_re]
    ring
  rw [he,abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hb := (Complex.abs_re_le_norm (χ a s t w-χ a s r w)).trans
    (characteristic_increment_bound ε hε h hne hh m g k a s r t ha hrt w)
  have heE := (energy_comparison ε hε h hne hh m g k s r t hrt w).2
  calc
    _ ≤ 2*((slopeBound/|h|)*|a| *E s t w*(t-r)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2*((slopeBound/|h|)*|a| *(Real.exp (2*(t-r))*E s r w)*(t-r)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hrt)
      exact mul_le_mul_of_nonneg_left heE (by have hc := slopeBound_positive; positivity)
    _ = budget h (t-r) (E s r w)*|a| := by unfold budget; ring

theorem orbitGap_propagation (a s r t : ℝ) (ha : |a| ≤ 1) (hrt : r ≤ t) (w : V) :
    orbitGap a (U s t (J w)) ≤ orbitGap a (U s r (J w))+budget h (t-r) (E s r w)*|a| := by
  have hb := (abs_le.mp (orbitGap_increment_bound ε hε h hne hh m g k a s r t ha hrt w)).2
  linarith only [hb]

#print axioms orbitGap_characteristic
#print axioms orbitGap_combined
#print axioms budget_nonnegative
#print axioms outputRate_bound
#print axioms characteristic_increment_bound
#print axioms orbitGap_increment_bound
#print axioms orbitGap_propagation
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeOrbitEstimate

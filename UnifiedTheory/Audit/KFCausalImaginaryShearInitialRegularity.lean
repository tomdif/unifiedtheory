/- Smooth mixed-coordinate representatives of the actual initial endpoint,
including every finite complex superposition. The clock multiplier is
identified with the state, rather than supplying a regularity premise. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state weight mixedState_coe state_coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (clockFrequency)
open UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness (modulate)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (dilate momentumScale)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint

theorem weight_smooth (ε a h : ℝ) : ContDiff ℝ 1 (weight ε a h) := by
  have hg : ContDiff ℝ 1 (KFCausalClockFloorInvariantTrial.clockFunction ε a) := by
    unfold KFCausalClockFloorInvariantTrial.clockFunction
    apply Complex.ofRealCLM.contDiff.comp
    unfold KFCausalRegularizedLongitudinalChart.chart
    exact (contDiff_const.add (contDiff_const.mul contDiff_id.neg.exp)).mul
      (contDiff_const.mul ((contDiff_id.exp.add (contDiff_const.mul contDiff_id)).pow 2)).exp
  have hq : ContDiff ℝ 1 (fun x : Joint 2 4 =>
      KFCausalChargeGaussianGeometry.groundWidth h*KFCausalChargeGaussianGeometry.radius (momentumScale h) x+
        KFCausalClockFloorInvariantTrial.neutralWidth h*(x (.inr 3))^2) := by
    simp only [KFCausalChargeGaussianGeometry.radius_coordinates]
    fun_prop
  exact contDiff_const.mul ((hg.comp (by fun_prop)).mul
    (Complex.ofRealCLM.contDiff.comp hq).neg.cexp)

theorem modulated_weight_smooth (ε a h : ℝ) (k : Joint 2 4) :
    ContDiff ℝ 1 (modulate (dilate (momentumScale h) k) (weight ε a h)) := by
  have hi : ContDiff ℝ 1 (fun x : Joint 2 4 => 2*Real.pi*inner ℝ x (dilate (momentumScale h) k)) :=
    contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)
  simpa only [modulate,Real.fourierChar_apply] using
    ((Complex.ofRealCLM.contDiff.comp hi).mul contDiff_const).cexp.mul (weight_smooth ε a h)

def mixed (ε a h : ℝ) (k : Joint 2 4) (x : Joint 2 4) : ℂ :=
  symbol ε a (clockFrequency k) h (x (.inr 0))*modulate (dilate (momentumScale h) k) (weight ε a h) x

theorem mixed_smooth (ε a h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    ContDiff ℝ 1 (mixed ε a h k) :=
  ((symbol_smooth ε a (clockFrequency k) h hε hb).comp (by fun_prop)).mul (modulated_weight_smooth ε a h k)

theorem mixed_coe (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    chargeCoordinates (initialOperator ε a (clockFrequency k) h hε hb (state ε a h hε ha hh k)) =ᵐ[volume]
      mixed ε a h k := by
  filter_upwards [initialOperator_coordinates ε a (clockFrequency k) h hε hb (state ε a h hε ha hh k),
    mixedState_coe ε a h hε ha hh k] with x hi hf
  rw [hi,state_coordinates,hf]
  rfl

theorem finite_representatives {ι : Type*} (s : Finset ι) (f : ι → JointHilbert 2 4)
    (φ : ι → Joint 2 4 → ℂ) (hf : ∀ i, f i =ᵐ[volume] φ i) :
    (∑ i ∈ s, f i : JointHilbert 2 4) =ᵐ[volume] fun x => ∑ i ∈ s, φ i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℂ 2 (volume : Measure (Joint 2 4))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j),hf i,ih] with x ha hb hc
    simp only [ha,Pi.add_apply,hb,hc]

def mixedSum (ε a h : ℝ) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) (x : Joint 2 4) : ℂ :=
  ∑ i, z i*mixed ε a h (k i) x

theorem mixedSum_smooth (ε a h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
    {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) : ContDiff ℝ 1 (mixedSum ε a h k z) :=
  ContDiff.sum (fun i _ => contDiff_const.mul (mixed_smooth ε a h hε hb (k i)))

theorem initial_coordinates (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) :
    chargeCoordinates (KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb k z 0) =ᵐ[volume]
      mixedSum ε a h k z := by
  rw [input_zero_sum,map_sum]
  apply finite_representatives
  intro i
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (z i)
      (chargeCoordinates (initialOperator ε a (clockFrequency (k i)) h hε hb (state ε a h hε ha hh (k i)))),
    mixed_coe ε a h hε ha hh hb (k i)] with x hs hf
  simp only [hs,Pi.smul_apply,smul_eq_mul,hf]

#print axioms weight_smooth
#print axioms modulated_weight_smooth
#print axioms mixed_smooth
#print axioms mixed_coe
#print axioms finite_representatives
#print axioms mixedSum_smooth
#print axioms initial_coordinates
end
end UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity

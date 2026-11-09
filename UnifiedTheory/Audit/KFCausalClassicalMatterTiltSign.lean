/- The vacuum nonnegative-tilt lemma does not survive a field-dependent matter
weight. This is an exact scalar counterexample to that lemma, not a failure
of recovery or of the quantum model. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterSymbols

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterTiltSign
noncomputable section
open Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalWeightedLaplace
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)

def witnessPhase : Phase :=
  (WithLp.toLp 2 (fun
    | .inl _ => 0
    | .inr i => ![0,0,scale,1] i),
   WithLp.toLp 2 (fun
    | .inl _ => 0
    | .inr i => ![0,0,0,-1] i))

theorem witness_shear (θ : ℝ) : shear (rotate θ witnessPhase) = -Real.cos θ := by
  simp [shear_rotate,diagonalPairing,crossPairing,witnessPhase]
  ring_nf
  rw [scale_square]
  ring

theorem witness_field (θ : ℝ) : fieldValue (rotate θ witnessPhase) = 1+Real.cos θ := by
  simp [fieldValue_rotate,witnessPhase]
  ring_nf
  rw [scale_square]
  ring

theorem witness_potential (θ : ℝ) : potential 2 0 1 (rotate θ witnessPhase) = 1+(1+Real.cos θ)^2 := by
  simp [potential,witness_field]

theorem witness_weighted_first_moment :
    mean (fun θ => potential 2 0 1 (rotate θ witnessPhase)*shear (rotate θ witnessPhase)) = -1 := by
  have h3 : mean (fun θ => Real.cos θ^3) = 0 := by
    simp [mean,integral_cos_pow_three,Real.sin_two_pi]
  have he : (fun θ => potential 2 0 1 (rotate θ witnessPhase)*shear (rotate θ witnessPhase)) =
      fun θ => Real.cos θ*(-2)+(Real.cos θ^2)*(-2)+(Real.cos θ^3)*(-1) := by
    funext θ
    rw [witness_potential,witness_shear]
    ring
  rw [he,mean_add _ _ (by fun_prop) (by fun_prop),mean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [mean_mul_const,mean_trig.2.1,mean_trig.2.2.2.1,h3]
  norm_num

theorem exists_negative_weighted_tilt : ∃ C : ℝ, 0 < C ∧ weightedTilt 2 0 1 C witnessPhase < 0 := by
  let w : ℝ → ℝ := fun θ => potential 2 0 1 (rotate θ witnessPhase)
  let f : ℝ → ℝ := fun θ => shear (rotate θ witnessPhase)
  let J : ℝ → ℝ := fun a => mean (fun θ => w θ*f θ*Real.exp (a*f θ))
  have hw : Continuous w := potential_continuous 2 0 1 witnessPhase
  have hf : Continuous f := shear_continuous witnessPhase
  have hd := mean_weighted_exp_derivative (fun θ => w θ*f θ) f (hw.mul hf) hf 0
  have h0 : J 0 = -1 := by
    simpa only [J,w,f,zero_mul,Real.exp_zero,mul_one] using witness_weighted_first_moment
  have hcont : ContinuousAt J 0 := hd.continuousAt
  have hev : ∀ᶠ a in 𝓝 (0:ℝ), J a < 0 := hcont (Iio_mem_nhds (by rw [h0]; norm_num))
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hev
  have ha : 0 < δ/2 := by positivity
  have hj : J (δ/2) < 0 := hb (by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos ha]
    linarith)
  refine ⟨(δ/2)⁻¹,inv_pos.mpr ha,?_⟩
  have he : weightedTilt 2 0 1 (δ/2)⁻¹ witnessPhase = J (δ/2)*(δ/2) := by
    dsimp only [J]
    rw [← mean_mul_const]
    unfold weightedTilt
    congr 1
    funext θ
    simp only [div_inv_eq_mul,w,f]
    rw [mul_comm (δ/2) (shear (rotate θ witnessPhase))]
    ring
  rw [he]
  exact mul_neg_of_neg_of_pos hj ha

theorem exists_negative_tilt_at_positive_floor :
    ∃ ε s : ℝ, 0 < ε ∧
      weightedTilt 2 0 1 (KFCausalClockFloorFlow.clock ε s) witnessPhase < 0 := by
  obtain ⟨C,hC,hneg⟩ := exists_negative_weighted_tilt
  refine ⟨C/2,Real.log (C/2),by positivity,?_⟩
  have hc : KFCausalClockFloorFlow.clock (C/2) (Real.log (C/2)) = C := by
    rw [KFCausalClockFloorFlow.clock,Real.exp_log (by positivity : 0 < C/2)]
    ring
  rw [hc]
  exact hneg

#print axioms witness_shear
#print axioms witness_field
#print axioms witness_potential
#print axioms witness_weighted_first_moment
#print axioms exists_negative_weighted_tilt
#print axioms exists_negative_tilt_at_positive_floor

end
end UnifiedTheory.Audit.KFCausalClassicalMatterTiltSign

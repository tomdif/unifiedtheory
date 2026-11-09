/- The actual coherent marginal score, angular loss, and Hardy bound
combine with the quartic field Young inequality. All integral premises
are derived from the Gaussian margin. The remaining scalar condition
is a coefficient inequality, to be discharged by the physical clock. -/
import UnifiedTheory.Audit.KFCausalChargedQuarticHardy
import UnifiedTheory.Audit.KFCausalChargedQuarticUniversalAngularLoss
import UnifiedTheory.Audit.KFCausalQuarticFieldSlopeBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedQuarticCorrectedBound
noncomputable section
open MeasureTheory
open KFCausalChargedQuarticScoreIBP
open KFCausalChargedCoolingMarginalScore (marginal)
open KFCausalChargedCoolingBoundaryScore (scoreRate)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalAngularQuarticGaussianSmoothing (weight weightSlope)

def scoreHalf (r : ℂ) : ℝ := scoreRate r/2

theorem scoreHalf_positive (r : ℂ) (hr : |r.im|<r.re) : 0<scoreHalf r := by
  have ha : 0<r.re := lt_of_le_of_lt (abs_nonneg _) hr
  have hA : 0<r.re^2-r.im^2 := by
    nlinarith [sq_abs r.im,mul_pos (sub_pos.mpr hr) (by linarith [abs_nonneg r.im] : 0<r.re+|r.im|)]
  have hN : 0<3*r.re^2-r.im^2 := by nlinarith [sq_nonneg r.re]
  unfold scoreHalf scoreRate
  positivity

private theorem scalar_young (sigma a R B v x : ℝ) (hs : 0<sigma) (ha : 0≤a)
    (hB : 0≤B) (hR : R^2≤a*sigma*B) :
    -a*v^2*weight sigma x-B*weight sigma x≤R*v*weightSlope sigma x := by
  by_cases h0 : a=0
  · have hR0 : R=0 := by rw [h0] at hR; nlinarith [sq_nonneg R]
    rw [h0,hR0]
    have hW : 0≤weight sigma x := by unfold weight; positivity
    nlinarith [mul_nonneg hB hW]
  · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm h0)
    have hb : R^2/(a*sigma)≤B := (div_le_iff₀ (mul_pos hap hs)).mpr (by nlinarith only [hR])
    have hW : 0≤weight sigma x := by unfold weight; positivity
    have hm := mul_le_mul_of_nonneg_right hb hW
    linarith only [hm,KFCausalQuarticFieldSlopeBound.field_young sigma a R v x hs hap]

variable (n : ℕ) (α : ℝ) (r : ℂ) (sigma d q mu L : ℝ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
    (hd : ∀i,d<2*(gamma α r).re*w i)
include hα hr hw hd

theorem second_moment_integrable :
    Integrable (fun v : ℝ => v^2*energyDensity sigma d q mu L n α r w c v) := by
  let P : Polynomial ℝ := Polynomial.X^2*((Polynomial.C mu+Polynomial.C L*Polynomial.X)^4+
    Polynomial.C (6*sigma)*(Polynomial.C mu+Polynomial.C L*Polynomial.X)^2+Polynomial.C (3*sigma^2))
  have hi := (KFCausalChargedQuarticScoreIntegrability.polynomial_integrable
    n α r d q w c hα hr hw hd P).1
  convert hi using 1
  funext v
  simp only [P,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_add,
    Polynomial.eval_C,energyDensity,weight]
  ring

theorem integrated_young (a R B : ℝ) (hs : 0<sigma) (ha : 0≤a) (hB : 0≤B)
    (hR : R^2≤a*sigma*B) :
    -a*(∫v : ℝ,v^2*energyDensity sigma d q mu L n α r w c v)-
      B*(∫v,energyDensity sigma d q mu L n α r w c v)≤
        R*(∫v,fieldDensity sigma d q mu L n α r w c v) := by
  have hi := densities_integrable n α r d q w c hα hr hw hd sigma mu L
  have hv := second_moment_integrable n α r sigma d q mu L w c hα hr hw hd
  have hp (v : ℝ) : 0≤Real.exp (d*v^2-q*v)*marginal n α r w c v := by
    apply mul_nonneg (Real.exp_pos _).le
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hm := integral_mono ((hv.const_mul (-a)).sub (hi.1.const_mul B))
    (hi.2.1.const_mul R) (fun v => ?_)
  · simp only [Pi.sub_apply] at hm
    rw [integral_sub (hv.const_mul (-a)) (hi.1.const_mul B)] at hm
    simp only [integral_const_mul] at hm
    simpa only [neg_mul] using hm
  · have h := mul_le_mul_of_nonneg_right (scalar_young sigma a R B v (mu+L*v) hs ha hB hR) (hp v)
    dsimp only [Pi.sub_apply,energyDensity,fieldDensity]
    nlinarith only [h]

omit hα hr hw hd in
theorem global_corrected_bound : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (α : ℝ) (r : ℂ) (sigma d q mu L : ℝ) (w : Fin n→ℝ) (c : Fin n→ℂ)
      (δ κ B : ℝ),0<α→|r.im|<r.re→(∀i,0<w i)→(∀i,d<2*(gamma α r).re*w i)→
      0<sigma→0≤d→0≤δ→0≤B→
      ((4/3:ℝ)*δ*scoreHalf r*L-κ)^2≤(δ*scoreHalf r*d/3)*sigma*B→
      -δ*(∫v,coolingDensity sigma d q mu L n α r w c v)+
        κ*(∫v,fieldDensity sigma d q mu L n α r w c v)≤
        (δ*(scoreHalf r*(C-2)/3-1/r.re)+B)*
          (∫v,energyDensity sigma d q mu L n α r w c v) := by
  obtain ⟨C,hC,hbound⟩ := KFCausalChargedQuarticUniversalAngularLoss.global_loss
  refine ⟨C,hC,?_⟩
  intro n α r sigma d q mu L w c δ κ B hα hr hw hd hs hd0 hδ hB hR
  have hg := scoreHalf_positive r hr
  have he := KFCausalChargedQuarticScoreAttachment.energy_field_tilt n α r d q w c hα hr hw hd sigma mu L
  have ha := hbound n sigma d q mu L (gamma α r) w c hs.le hd0
    (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr) hw hd
  rw [he.1,he.2.1,he.2.2] at ha
  have hh := KFCausalChargedQuarticHardy.marginal_bound n α r sigma d q mu L w c hs.le hd0 hα hr hw hd
  have hscore := quartic_score n α r d q w c hα hr hw hd sigma mu L hs.le
  have hscore' :
      (2*scoreHalf r+1/r.re)*(∫v,energyDensity sigma d q mu L n α r w c v)+
      scoreHalf r*L*(∫v,fieldDensity sigma d q mu L n α r w c v)+
      scoreHalf r*(∫v,tiltDensity sigma d q mu L n α r w c v)≤
        ∫v,coolingDensity sigma d q mu L n α r w c v := by
    convert hscore using 1
    unfold scoreHalf
    ring
  have hc := mul_le_mul_of_nonneg_left hscore' hδ
  have hmix :
      L*(∫v,fieldDensity sigma d q mu L n α r w c v)+
        d*(∫v : ℝ,v^2*energyDensity sigma d q mu L n α r w c v)-
        (C+4)*(∫v,energyDensity sigma d q mu L n α r w c v)≤
        3*(∫v,tiltDensity sigma d q mu L n α r w c v) := by linarith only [ha,hh]
  have hm := mul_le_mul_of_nonneg_left hmix (mul_nonneg hδ hg.le)
  have hy := integrated_young n α r sigma d q mu L w c hα hr hw hd
    (δ*scoreHalf r*d/3) ((4/3:ℝ)*δ*scoreHalf r*L-κ) B hs (by positivity) hB hR
  nlinarith only [hc,hm,hy]

#print axioms scoreHalf_positive
#print axioms second_moment_integrable
#print axioms integrated_young
#print axioms global_corrected_bound
end
end UnifiedTheory.Audit.KFCausalChargedQuarticCorrectedBound

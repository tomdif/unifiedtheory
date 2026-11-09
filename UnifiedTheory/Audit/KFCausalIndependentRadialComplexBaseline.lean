/- The broad baseline quadratic at every complex shear parameter.
Both independent normalization widths cancel exactly, retaining the
physical neutral shear. This is algebra on explicit profiles. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialShearIdentity
import UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialComplexBaseline
noncomputable section
open KFCausalEuclideanProductCoordinates (Block split)
open KFCausalComplexShearPerturbation (flow)
open KFCausalComplexQuadraticPerturbation (weightedQuadratic)
open KFCausalIndependentRadialNormalization (normalize weights)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalShiftedNarrowFourierGeometry (radius neutral)
open KFCausalIndependentRadialHolomorphicQuotient (baseline baselineVector)
open KFCausalComplexClockInverse (complexInverse)

theorem weighted_flow_quadratic (α W wL wR c : ℝ) (hα : 0<α) (hW : 0<W)
    (hL : 0<wL) (hR : 0<wR) (hmatch : Real.pi^2/α=α*c^2)
    (z : ℂ) (x : Block 2 × Block 4) :
    weightedQuadratic (weights W wL wR)
      (fun i => flow (coupling α wR) z (normalize α wL wR c ((split 2 4).symm x)) i) =
      ((1/(4*W):ℝ):ℂ)*radius ((α:ℂ)*(Complex.exp (z/2))^2) x.1 x.2+
        ((α/(512*W):ℝ):ℂ)*(neutral (Complex.exp (z/2)) x.2)^2 := by
  have h₁ : (Real.sqrt (α/wL):ℂ)^2=((α/wL:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hα.le hL.le)
  have h₂ : (Real.sqrt (α*wR):ℂ)^2=((α*wR:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have h₃ : (Real.sqrt (α/32):ℂ)^2=((α/32:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤α/32 by positivity)
  have he : Complex.exp (-z/2)=(Complex.exp (z/2))⁻¹ := by
    rw [show -z/2=-(z/2) by ring,Complex.exp_neg]
  have hn : (‖x.1‖:ℂ)^2=(x.1 0:ℂ)^2+(x.1 1:ℂ)^2 := by
    exact_mod_cast KFCausalShiftedNarrowFourierGeometry.narrow_norm_square x.1
  have hm : (Real.pi:ℂ)^2=(α:ℂ)^2*(c:ℂ)^2 := by
    have ht : Real.pi^2=α^2*c^2 := by
      have ht := (div_eq_iff hα.ne').mp hmatch
      nlinarith
    exact_mod_cast ht
  have hc := KFCausalIndependentRadialShearIdentity.neutral_flow_normalize
    α wL wR c hα hR z x
  have hl (i : Fin 2) : ((split 2 4).symm x) (.inl i)=x.1 i := rfl
  have hv (i : Fin 4) : ((split 2 4).symm x) (.inr i)=x.2 i := rfl
  simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  simp only [show ((Fin.succ 0).succ.succ.succ : Fin 5)=4 from rfl]
  rw [hc]
  simp only [flow,KFCausalIndependentRadialNormalization.normalize,weights,
    Matrix.cons_val_zero,Matrix.cons_val_succ,he,hl,hv]
  simp only [Complex.ofReal_mul,mul_pow,h₁,h₃,radius,
    KFCausalShiftedNarrowFourierGeometry.broadRadius,hn,hm]
  push_cast
  simp only [mul_pow,h₁,h₂]
  push_cast
  have hαc : (α:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hWc : (W:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hW.ne'
  have hLc : (wL:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hRc : (wR:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hR.ne'
  field_simp [hαc,hWc,hLc,hRc,Complex.exp_ne_zero]
  ring

theorem baseline_formula (ε a α W wL wR c : ℝ) (hα : 0<α) (hW : 0<W)
    (hL : 0<wL) (hR : 0<wR) (hmatch : Real.pi^2/α=α*c^2)
    (q : ℂ) (x : Block 2 × Block 4) :
    baseline ε a α W wL wR c q ((split 2 4).symm x) =
      ((Real.pi/(4*W*α):ℝ):ℂ)*Complex.exp (-complexInverse ε q)*
        Complex.exp (-((a/2:ℝ):ℂ)*q^2)*
        Complex.exp (-((1/(4*W):ℝ):ℂ)*
          radius ((α:ℂ)*(Complex.exp (complexInverse ε q/2))^2) x.1 x.2-
          ((α/(512*W):ℝ):ℂ)*(neutral (Complex.exp (complexInverse ε q/2)) x.2)^2) := by
  unfold baseline baselineVector
  rw [weighted_flow_quadratic α W wL wR c hα hW hL hR hmatch]
  congr 1
  congr 1
  ring

#print axioms weighted_flow_quadratic
#print axioms baseline_formula
end
end UnifiedTheory.Audit.KFCausalIndependentRadialComplexBaseline

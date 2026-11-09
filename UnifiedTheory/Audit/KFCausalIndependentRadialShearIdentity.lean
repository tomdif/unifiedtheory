/- Exact complex-shear quadratics for independently variable charged
radial widths, including the physical neutral displacement. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialNormalization
import UnifiedTheory.Audit.KFCausalShiftedPhysicalFourierSlices

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialShearIdentity
noncomputable section
open KFCausalEuclideanProductCoordinates (Block Joint split)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalComplexQuadraticPerturbation (quadratic)
open KFCausalNormalizedComplexRotation (rotationIsometry rotate)
open KFCausalIndependentRadialNormalization (normalize)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalShiftedNarrowFourierGeometry (neutral)
open KFCausalShiftedNarrowFourierSlices (neutralPacket)

def radius (A : ℂ) (wL wR : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  (Real.pi:ℂ)^2/A*((u 0:ℂ)^2/(wL:ℂ)+(wR:ℂ)*(u 1:ℂ)^2)+
    A*((v 1:ℂ)^2/(wL:ℂ)+(wR:ℂ)*(v 2:ℂ)^2)

theorem neutral_flow_normalize (α wL wR c : ℝ) (hα : 0 < α) (hR : 0 < wR)
    (z : ℂ) (x : Block 2 × Block 4) :
    flow (coupling α wR) z (normalize α wL wR c ((split 2 4).symm x)) 4 =
      (Real.sqrt (α/32):ℂ)*neutral (Complex.exp (z/2)) x.2 := by
  have hs : (Real.sqrt (α*wR):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos hα hR)).ne'
  have hv (i : Fin 4) : ((split 2 4).symm x) (.inr i)=x.2 i := rfl
  simp only [flow,coupling,KFCausalIndependentRadialNormalization.normalize,neutral,
    Matrix.cons_val_zero,hv]
  push_cast
  field_simp [hs]
  ring

theorem quadratic_flow_normalize (α wL wR c : ℝ) (hα : 0 < α) (hL : 0 < wL) (hR : 0 < wR)
    (hmatch : Real.pi^2/α=α*c^2) (z : ℂ) (x : Block 2 × Block 4) :
    quadratic (fun i => flow (coupling α wR) z (normalize α wL wR c ((split 2 4).symm x)) i)=
      radius ((α:ℂ)*(Complex.exp (z/2))^2) wL wR x.1 x.2+
        (α/32:ℝ)*(neutral (Complex.exp (z/2)) x.2)^2 := by
  have hs : (Real.sqrt (α*wR):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos hα hR)).ne'
  have hwc : (wR:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hlc : (wL:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne' 
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hr : Complex.exp (z/2) ≠ 0 := Complex.exp_ne_zero _
  have he : Complex.exp (-z/2)=(Complex.exp (z/2))⁻¹ := by
    rw [show -z/2=-(z/2) by ring,Complex.exp_neg]
  have hs2 : (Real.sqrt (α/wL):ℂ)^2=(α/wL:ℝ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hα.le hL.le)
  have ht2 : (Real.sqrt (α*wR):ℂ)^2=(α*wR:ℝ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have hb2 : (Real.sqrt (α/32):ℂ)^2=(α/32:ℝ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  have hm : (Real.pi:ℂ)^2=(α:ℂ)^2*(c:ℂ)^2 := by
    have ht : Real.pi^2=α^2*c^2 := by
      have ht := (div_eq_iff hα.ne').mp hmatch
      nlinarith
    exact_mod_cast ht
  have hl (i : Fin 2) : ((split 2 4).symm x) (.inl i)=x.1 i := rfl
  have hv (i : Fin 4) : ((split 2 4).symm x) (.inr i)=x.2 i := rfl
  have hf : flow (coupling α wR) z (normalize α wL wR c ((split 2 4).symm x)) =
      (WithLp.toLp 2 ![(Complex.exp (z/2))⁻¹*(Real.sqrt (α/wL):ℂ)*(c:ℂ)*(x.1 0:ℂ),
        (Complex.exp (z/2))⁻¹*(Real.sqrt (α*wR):ℂ)*(c:ℂ)*(x.1 1:ℂ),
        Complex.exp (z/2)*(Real.sqrt (α/wL):ℂ)*(x.2 1:ℂ),
        Complex.exp (z/2)*(Real.sqrt (α*wR):ℂ)*(x.2 2:ℂ),
        (Real.sqrt (α/32):ℂ)*neutral (Complex.exp (z/2)) x.2] : Space) := by
    ext i
    fin_cases i <;> simp only [flow,KFCausalIndependentRadialNormalization.normalize,
      coupling,neutral,Matrix.cons_val_zero,he,hl,hv]
    all_goals push_cast
    all_goals field_simp [hs]
    all_goals ring
  rw [hf]
  simp only [quadratic,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero,mul_pow,hs2,ht2,hb2]
  dsimp only [radius]
  rw [hm]
  push_cast
  field_simp [ha,hr,hwc,hlc]
  ring

theorem packet_flow_normalize (α wL wR c : ℝ) (hα : 0 < α) (hL : 0 < wL) (hR : 0 < wR)
    (hmatch : Real.pi^2/α=α*c^2) (z : ℂ) (x : Block 2 × Block 4) :
    Complex.exp (-radius ((α:ℂ)*(Complex.exp (z/2))^2) wL wR x.1 x.2)*
        neutralPacket (α/32) (Complex.exp (z/2)) 0 1 x.2 =
      Complex.exp (-quadratic (fun i => flow (coupling α wR) z
        (normalize α wL wR c ((split 2 4).symm x)) i)) := by
  rw [quadratic_flow_normalize α wL wR c hα hL hR hmatch]
  simp only [neutralPacket,zero_mul,add_zero,Polynomial.eval_one,mul_one]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

#print axioms neutral_flow_normalize
#print axioms quadratic_flow_normalize
#print axioms packet_flow_normalize
end
end UnifiedTheory.Audit.KFCausalIndependentRadialShearIdentity

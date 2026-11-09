/- Exact transverse directional derivatives and L2 bounds for a diagonal
Gaussian with an arbitrary square-integrable clock factor. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
import UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)

def gradient (α β : ℝ) (v : Transverse) (x : Transverse) : ℂ :=
  ∑ i : Fin 5, (-2*widths α β i*v i:ℝ)*(x i:ℂ)*physicalGaussian α β x

theorem physicalGaussian_differentiable (α β : ℝ) : Differentiable ℝ (physicalGaussian α β) := by
  have hq : Differentiable ℝ (fun x : Transverse => α*∑ i : Fin 4, (x i.castSucc)^2+β*(x 4)^2) := by
    fun_prop
  exact (Complex.ofRealCLM.differentiable.comp hq).neg.cexp

theorem physicalGaussian_hasLineDerivAt (α β : ℝ) (v x : Transverse) :
    HasLineDerivAt ℝ (physicalGaussian α β) (gradient α β v x) x v := by
  have hl (i : Fin 5) : HasDerivAt (fun t : ℝ => x i+t*v i) (v i) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)
  have hs (i : Fin 5) : HasDerivAt (fun t : ℝ => (x i+t*v i)^2) (2*x i*v i) 0 := by
    simpa only [zero_mul,add_zero,show 2-1=1 from rfl,pow_one,Nat.cast_ofNat,Pi.pow_apply] using (hl i).pow 2
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hs i.castSucc)
  have hq := (hsum.const_mul α).add ((hs 4).const_mul β)
  have he := hq.neg.ofReal_comp.cexp
  change HasDerivAt (fun t : ℝ => physicalGaussian α β (x+t • v)) (gradient α β v x) 0
  convert he using 1
  · funext t
    simp only [physicalGaussian,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply,Complex.ofReal_neg]
  · simp only [Pi.neg_apply,Pi.add_apply]
    simp only [gradient,physicalGaussian,widths,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,zero_mul]
    push_cast
    ring

theorem gradient_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (v : Transverse) :
    MemLp (gradient α β v) 2 volume := by
  apply memLp_finset_sum
  intro i _
  simpa only [mul_assoc] using
    (physicalGaussian_coordinate_memLp α β hα hβ i).const_mul ((-2*widths α β i*v i:ℝ):ℂ)

theorem configuration_product_memLp (g : ℝ → ℂ) (p : Transverse → ℂ)
    (hg : MemLp g 2 volume) (hp : MemLp p 2 volume) :
    MemLp (fun z : Configuration => g z.1*p z.2) 2 volume := by
  have hm := hg.aestronglyMeasurable.comp_fst.mul hp.aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hp2 := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  simpa only [Pi.mul_apply,norm_mul,mul_pow] using hg2.mul_prod hp2

theorem configurationProfile_derivative (α β : ℝ) (g : ℝ → ℂ) (v : Transverse)
    (z : Configuration) : derivative v (configurationProfile α β g) z =
      g z.1*gradient α β v z.2 := by
  exact ((physicalGaussian_hasLineDerivAt α β v z.2).const_mul (g z.1)).deriv

theorem configurationProfile_transverse_differentiable (α β : ℝ) (g : ℝ → ℂ) (s : ℝ) :
    Differentiable ℝ (fun y : Transverse => configurationProfile α β g (s,y)) :=
  (physicalGaussian_differentiable α β).const_mul (g s)

theorem configurationProfile_derivative_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (v : Transverse) :
    MemLp (derivative v (configurationProfile α β g)) 2 volume := by
  have he : derivative v (configurationProfile α β g) =
      fun z : Configuration => g z.1*gradient α β v z.2 :=
    funext (configurationProfile_derivative α β g v)
  rw [he]
  exact configuration_product_memLp g (gradient α β v) hg (gradient_memLp α β hα hβ v)

#print axioms physicalGaussian_differentiable
#print axioms physicalGaussian_hasLineDerivAt
#print axioms gradient_memLp
#print axioms configuration_product_memLp
#print axioms configurationProfile_derivative
#print axioms configurationProfile_transverse_differentiable
#print axioms configurationProfile_derivative_memLp

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative

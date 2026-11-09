/- Representative calculus for finite combinations of actual L2 moment
outputs. Fixed bounded clock multiplication acts on their coefficients. -/
import UnifiedTheory.Audit.KFCausalCoherentShearMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalShearOutputCoefficients
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem product_add (g f j : Hilbert) (m n : Configuration → ℂ)
    (hf : f =ᵐ[volume] fun x => m x*g x) (hj : j =ᵐ[volume] fun x => n x*g x) :
    f+j =ᵐ[volume] fun x => (m x+n x)*g x := by
  filter_upwards [Lp.coeFn_add f j,hf,hj] with x ha hb hc
  rw [ha]
  simp only [Pi.add_apply,hb,hc,add_mul]

theorem product_sub (g f j : Hilbert) (m n : Configuration → ℂ)
    (hf : f =ᵐ[volume] fun x => m x*g x) (hj : j =ᵐ[volume] fun x => n x*g x) :
    f-j =ᵐ[volume] fun x => (m x-n x)*g x := by
  filter_upwards [Lp.coeFn_sub f j,hf,hj] with x ha hb hc
  rw [ha]
  simp only [Pi.sub_apply,hb,hc,sub_mul]

theorem product_smul (g f : Hilbert) (m : Configuration → ℂ) (c : ℂ)
    (hf : f =ᵐ[volume] fun x => m x*g x) :
    c • f =ᵐ[volume] fun x => (c*m x)*g x := by
  filter_upwards [Lp.coeFn_smul c f,hf] with x ha hb
  rw [ha]
  simp only [Pi.smul_apply,smul_eq_mul,hb,mul_assoc]

theorem product_sum {ι : Type*} (g : Hilbert) (f : ι → Hilbert)
    (m : ι → Configuration → ℂ) (s : Finset ι)
    (hf : ∀ i, f i =ᵐ[volume] fun x => m i x*g x) :
    (∑ i ∈ s, f i : Hilbert) =ᵐ[volume] fun x => (∑ i ∈ s, m i x)*g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,zero_mul] using Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact product_add g _ _ _ _ (hf i) ih

theorem product_scale (ε h : ℝ) (hε : 0 < ε) (hbound : |h| ≤ 2*Real.pi*ε/3)
    (g f : Hilbert) (m : Configuration → ℂ) (hf : f =ᵐ[volume] fun x => m x*g x) :
    KFCausalCoherentShearPolynomial.scaleOperator ε h hε hbound f =ᵐ[volume] fun x =>
      (KFCausalClockFloorRelativeShift.scale ε (-h/2) x.1*m x)*g x := by
  filter_upwards [KFCausalCoherentShearPolynomial.scaleOperator_coe ε h hε hbound f,hf] with x ha hb
  rw [ha,hb,mul_assoc]

#print axioms product_add
#print axioms product_sub
#print axioms product_smul
#print axioms product_sum
#print axioms product_scale
end
end UnifiedTheory.Audit.KFCausalShearOutputCoefficients

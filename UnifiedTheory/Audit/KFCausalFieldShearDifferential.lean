/- The exact physical field/shear product rule, including the density
term already present in the shear differential. Field powers have their
own directional derivative; they do not commute with shear momentum. -/
import UnifiedTheory.Audit.KFCausalFieldPolynomialPackets
import UnifiedTheory.Audit.KFCausalCoherentWeightedShearDomains

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldShearDifferential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalFieldPolynomialPackets (scalePart)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

def fieldSlope (l : Transverse →L[ℝ] ℝ) : Transverse →L[ℝ] ℝ := (1/2:ℝ) • l.comp scalePart

theorem fieldSlope_apply (l : Transverse →L[ℝ] ℝ) (x : Transverse) : fieldSlope l x = l (velocity x) := by
  have hv : velocity x = (1/2:ℝ) • scalePart x := by
    funext i
    change (if i=4 then x 2+x 3 else x i/2) =
      (1/2:ℝ)*(if i=4 then 2*(x 2+x 3) else x i)
    split_ifs <;> ring
  rw [hv,map_smul]
  rfl

def powerValue (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℂ := (l x.2:ℂ)^(i.val+1)
def powerSlope (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℂ :=
  ((i.val+1:ℕ):ℂ)*(l x.2:ℂ)^i.val*(fieldSlope l x.2:ℂ)
def powerProfile (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  powerValue l i x*f x

theorem powerValue_smooth (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : ContDiff ℝ 1 (powerValue l i) :=
  (Complex.ofRealCLM.contDiff.comp (l.contDiff.comp contDiff_snd)).pow _

theorem powerSlope_smooth (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : ContDiff ℝ 1 (powerSlope l i) :=
  (contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp (l.contDiff.comp contDiff_snd)).pow _)).mul
    (Complex.ofRealCLM.contDiff.comp ((fieldSlope l).contDiff.comp contDiff_snd))

theorem power_line_derivative (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    HasLineDerivAt ℝ (powerValue l i) (powerSlope l i x) x ((0,velocity x.2):Configuration) := by
  have hd := (((hasDerivAt_id (0:ℝ)).mul_const (l (velocity x.2))).const_add (l x.2)).ofReal_comp.pow (i.val+1)
  change HasDerivAt (fun t : ℝ => powerValue l i (x+t • (0,velocity x.2))) _ 0
  convert hd using 1
  · funext t
    change (l (x.2+t • velocity x.2):ℂ)^(i.val+1) = _
    simp only [map_add,map_smul,smul_eq_mul,Pi.pow_apply,id_eq]
  · simp only [powerSlope,Nat.add_sub_cancel,id_eq,zero_mul,add_zero,one_mul,fieldSlope_apply]

theorem power_shear (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Configuration → ℂ)
    (hf : Differentiable ℝ f) (x : Configuration) :
    shearDerivative (powerProfile l i f) x =
      powerValue l i x*shearDerivative f x+powerSlope l i x*f x := by
  have hm := ((powerValue_smooth l i).differentiable (by norm_num) x).hasFDerivAt
  have hp := hm.mul (hf x).hasFDerivAt
  change HasFDerivAt (powerProfile l i f) _ x at hp
  have he := (power_line_derivative l i x).unique (hm.hasLineDerivAt ((0,velocity x.2):Configuration))
  rw [shearDerivative,hp.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [← he]
  unfold shearDerivative powerProfile
  ring

#print axioms fieldSlope_apply
#print axioms powerValue_smooth
#print axioms powerSlope_smooth
#print axioms power_line_derivative
#print axioms power_shear
end
end UnifiedTheory.Audit.KFCausalFieldShearDifferential

/- Classical physical transverse derivatives of the reciprocal packets,
including the neutral term in the second model direction. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowPacketDifferential
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalReciprocalGaussianStates (quadratic)
open KFCausalNarrowFourierPackets (configurationDensity)
open KFCausalNeutralLinePackets (packet packet_derivative step)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalTransverseTrialDerivative (derivative)

def quadraticSlope (w : ℝ) (q v : Transverse) : ℝ :=
  (w+1/w)*(q 0*v 0+q 1*v 1+q 2*v 2+q 3*v 3)+
    (1/w-w)*(v 0*q 1+q 0*v 1-v 2*q 3-q 2*v 3)

def modelSlope (w : ℝ) (q : Transverse) (j : Fin 4) : ℝ :=
  ![(2/w)*(q 0+q 1),(2*w)*(q 2+q 3),(2*w)*(q 0-q 1),(2/w)*(q 2-q 3)] j

theorem quadratic_derivative (w : ℝ) (q v : Transverse) :
    HasDerivAt (fun t : ℝ => quadratic w (q+t • v)) (quadraticSlope w q v) 0 := by
  have hl (i : Fin 5) : HasDerivAt (fun t : ℝ => q i+t*v i) (v i) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (q i)
  have hd := ((((hl 0).pow 2 |>.add ((hl 1).pow 2)).add ((hl 2).pow 2)).add ((hl 3).pow 2)).const_mul ((w+1/w)/2)
    |>.add ((((hl 0).mul (hl 1)).sub ((hl 2).mul (hl 3))).const_mul (1/w-w))
  convert hd using 1
  simp only [quadraticSlope,zero_mul,add_zero,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
  ring

theorem quadratic_model_slope (w : ℝ) (q : Transverse) (j : Fin 4) :
    quadraticSlope w q (modelDirections j) = modelSlope w q j := by
  fin_cases j <;> simp [quadraticSlope,modelDirections,modelSlope] <;> ring

theorem density_line_derivative (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (s : ℝ) (q v : Transverse) :
    HasLineDerivAt ℝ (fun y => configurationDensity α β w b P g (s,y))
      (-(α:ℂ)*(quadraticSlope w q v:ℂ)*configurationDensity α β w b P g (s,q)+
        (v 4:ℂ)*configurationDensity α β w b (step β b P) g (s,q)) q v := by
  have hl : HasDerivAt (fun t : ℝ => q 4+t*v 4) (v 4) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v 4)).const_add (q 4)
  have hn := (packet_derivative β b P (q 4+0*v 4)).scomp 0 hl
  simp only [zero_mul,add_zero] at hn
  have he := (((quadratic_derivative w q v).ofReal_comp).const_mul (-(α:ℂ))).cexp
  have hd := (he.mul hn).const_mul (g s)
  change HasDerivAt (fun t : ℝ => configurationDensity α β w b P g (s,q+t • v)) _ 0
  convert hd using 1
  · funext t
    simp only [configurationDensity,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.mul_apply,Function.comp_apply]
    ring
  · simp only [configurationDensity,zero_smul,add_zero,zero_mul,Function.comp_apply,Complex.real_smul]
    ring

theorem density_derivative (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (v : Transverse) (x : Configuration) :
    derivative v (configurationDensity α β w b P g) x =
      -(α:ℂ)*(quadraticSlope w x.2 v:ℂ)*configurationDensity α β w b P g x+
        (v 4:ℂ)*configurationDensity α β w b (step β b P) g x :=
  (density_line_derivative α β w b P g x.1 x.2 v).lineDeriv

theorem density_transverse_differentiable (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (s : ℝ) : Differentiable ℝ (fun q : Transverse => configurationDensity α β w b P g (s,q)) := by
  have hq : Differentiable ℝ (quadratic w) := by
    unfold quadratic KFCausalQuarticChargeProfiles.chargedRadius KFCausalChargedPairCoordinates.pairPolynomial
    fun_prop
  have hn : Differentiable ℝ (packet β b P) := fun x => (packet_derivative β b P x).differentiableAt
  exact (((Complex.ofRealCLM.differentiable.comp hq).const_mul (-(α:ℂ))).cexp.const_mul (g s)).mul
    (hn.comp (by fun_prop : Differentiable ℝ (fun q : Transverse => q 4)))

#print axioms quadratic_derivative
#print axioms quadratic_model_slope
#print axioms density_line_derivative
#print axioms density_derivative
#print axioms density_transverse_differentiable
end
end UnifiedTheory.Audit.KFCausalNarrowPacketDifferential

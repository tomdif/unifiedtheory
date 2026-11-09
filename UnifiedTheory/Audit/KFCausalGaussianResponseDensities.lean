/- Field-weighted densities of actual sourced Gaussian outputs are in L2.
The bounds follow from the existing operator domains, including the
ordered momentum correction. No response-integrability premise is added. -/
import UnifiedTheory.Audit.KFCausalSourcedMomentumDensity
import UnifiedTheory.Audit.KFCausalCoherentWeightedShearDomains

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalGaussianResponseDensities
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile slope)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (reducedOutput)
open UnifiedTheory.Audit.KFCausalSourcedMomentumOutput (shearOutput)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (weakSlope)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
  (fieldSquare fieldSquare_domain fieldSquare_linear_energy)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)

def amplitude (ε a α β p y : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  (l x.2:ℂ)^n.val*(C*profile (clockAmplitude ε a p y) (scale ε y) α β b x)

def momentum (ε a α β p y h : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  (-Complex.I*(h:ℂ))*weakSlope ε a p y x.1*amplitude ε a α β p y b C l n x

def shear (ε a α β p y h : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  (-Complex.I*(h:ℂ))*(slope (scale ε y) α β b x+1)*amplitude ε a α β p y b C l n x

def slopeDensity (ε a α β p y : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  slope (scale ε y) α β b x*amplitude ε a α β p y b C l n x

theorem field_power_memLp (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
    (f : Hilbert) (hf : f ∈ (fieldSquare l).domain) :
    MemLp (fun x : Configuration => (l x.2:ℂ)^n.val*f x) 2 volume := by
  fin_cases n
  · simpa only [pow_zero,one_mul] using Lp.memLp f
  · simpa only [pow_one] using fieldSquare_linear_energy l f hf
  · exact (fieldSquare_domain l f).mp hf

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "Ghalf" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb
local notation "TB" => reducedOutput ε a h hε ha hb p G Ghalf
local notation "JG" => shearOutput ε a α β hε ha hα hβ hw C p b h hb

theorem amplitude_density :
    (fun x : Configuration => (l x.2:ℂ)^n.val*G x) =ᵐ[volume]
      amplitude ε a α β p (-h/2) b C l n := by
  filter_upwards [KFCausalSourcedMomentumDensity.shifted_density ε a α β hε ha hα hβ hw C p b h hb]
    with x hx
  exact congrArg (fun z : ℂ => (l x.2:ℂ)^n.val*z) hx

theorem momentum_density :
    (fun x : Configuration => (l x.2:ℂ)^n.val*TB x) =ᵐ[volume]
      momentum ε a α β p (-h/2) h b C l n := by
  filter_upwards [KFCausalSourcedMomentumDensity.momentum_density ε a α β hε ha hα hβ hw C p b h hb]
    with x hx
  rw [hx]
  unfold momentum amplitude
  ring

theorem shear_density :
    (fun x : Configuration => (l x.2:ℂ)^n.val*JG x) =ᵐ[volume]
      shear ε a α β p (-h/2) h b C l n := by
  filter_upwards [Lp.coeFn_smul C (KFCausalShiftedGaussianShearDomain.shearOutput
    ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h),
    KFCausalShiftedGaussianShearDomain.shearOutput_coe
      ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h] with x hx hs
  dsimp only [KFCausalSourcedMomentumOutput.shearOutput]
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hs,shear,amplitude]
  ring

include hε ha hα hβ hw hb in
theorem amplitude_memLp : MemLp (amplitude ε a α β p (-h/2) b C l n) 2 volume :=
  (field_power_memLp l n G
    (KFCausalClockFloorSourcedCommonDomain.shiftedOutput_fieldSquare_domain
      ε a α β hε ha hα hβ hw C p b h hb l)).ae_eq
        (amplitude_density ε a α β hε ha hα hβ hw C p b h hb l n)

include hε ha hα hβ hw hb in
theorem momentum_memLp : MemLp (momentum ε a α β p (-h/2) h b C l n) 2 volume :=
  (field_power_memLp l n TB (KFCausalSourcedMomentumOutput.reduced_square_domain
    ε a α β hε ha hα hβ hw C p b h hb l)).ae_eq
      (momentum_density ε a α β hε ha hα hβ hw C p b h hb l n)

include hε ha hα hβ hw hb in
theorem shear_memLp : MemLp (shear ε a α β p (-h/2) h b C l n) 2 volume :=
  (field_power_memLp l n JG ((fieldSquare l).domain.smul_mem C
    (KFCausalCoherentWeightedShearDomains.shearOutput_square_domain
      ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h l))).ae_eq
        (shear_density ε a α β hε ha hα hβ hw C p b h hb l n)

include hε ha hα hβ hw hb in
theorem slopeDensity_memLp (hh : h ≠ 0) :
    MemLp (slopeDensity ε a α β p (-h/2) b C l n) 2 volume := by
  have hm := ((shear_memLp ε a α β hε ha hα hβ hw C p b h hb l n).const_mul
    (-Complex.I*(h:ℂ))⁻¹).sub (amplitude_memLp ε a α β hε ha hα hβ hw C p b h hb l n)
  apply hm.ae_eq
  filter_upwards [] with x
  simp only [Pi.sub_apply,shear,slopeDensity]
  have hz : -Complex.I*(h:ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hh)
  calc
    _ = ((-Complex.I*(h:ℂ))⁻¹*(-Complex.I*(h:ℂ)))*
      ((slope (scale ε (-h/2)) α β b x+1)*amplitude ε a α β p (-h/2) b C l n x)-
        amplitude ε a α β p (-h/2) b C l n x := by ring
    _ = _ := by rw [inv_mul_cancel₀ hz]; ring

#print axioms field_power_memLp
#print axioms amplitude_density
#print axioms momentum_density
#print axioms shear_density
#print axioms amplitude_memLp
#print axioms momentum_memLp
#print axioms shear_memLp
#print axioms slopeDensity_memLp
end
end UnifiedTheory.Audit.KFCausalGaussianResponseDensities

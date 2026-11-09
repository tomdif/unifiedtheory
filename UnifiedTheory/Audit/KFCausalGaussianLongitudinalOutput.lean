/- Exact expansion of the actual longitudinal momentum output. It uses
the actual shear output and bounded clock operators; no output regularity
or operator-composition identity is postulated. -/
import UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDomain
import UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalGaussianLongitudinalOutput
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile slope)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument scale)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude gaussianState_profile)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDomain (output differential_memLp)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential (profile_differential inverseClock)
open UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain (shearOutput shearOutput_coe)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum (differential)

variable (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
variable (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
variable (hy : |y| ≤ Real.pi*ε/3)
local notation "F" => profile (clockAmplitude ε a p y) (scale ε y) α β b
local notation "G" => gaussianState ε a α β p b y hε ha hα hβ hw hy
local notation "Ghalf" => gaussianState ε (a/2) α β p b y hε (by positivity) hα hβ hw hy
local notation "Z" => inverseOperator ε y hε hy
local notation "M" => momentOperator ε a y ha

theorem output_coe (h : ℝ) :
    output ε a α β p y b hε ha hα hβ hw hy h =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*(((p:ℂ)*Complex.I*inverseClock ε y x.1-
        2*(a:ℂ)*argument ε y x.1)*F x+inverseClock ε y x.1*slope (scale ε y) α β b x*F x) := by
  let hd := differential_memLp ε a α β p y b hε ha hα hβ hw hy
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hd.toLp _),hd.coeFn_toLp] with x hx hx'
  change ((-Complex.I*(h:ℂ)) • hd.toLp _) x = _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hx',profile_differential ε a α β p y b hε hy x]
  ring

theorem output_expansion (h : ℝ) :
    output ε a α β p y b hε ha hα hβ hw hy h =
      Z (shearOutput ε a α β p y b hε ha hα hβ hw hy h)+
        (-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • Z G-(2*(a:ℂ)) • M Ghalf) := by
  let j := shearOutput ε a α β p y b hε ha hα hβ hw hy h
  let c : ℂ := -Complex.I*(h:ℂ)
  let u : Hilbert := ((p:ℂ)*Complex.I-1) • Z G
  let v : Hilbert := (2*(a:ℂ)) • M Ghalf
  apply Lp.ext
  filter_upwards [output_coe ε a α β p y b hε ha hα hβ hw hy h,
    Lp.coeFn_add (Z j) (c • (u-v)),Lp.coeFn_smul c (u-v),Lp.coeFn_sub u v,
    Lp.coeFn_smul ((p:ℂ)*Complex.I-1) (Z G),Lp.coeFn_smul (2*(a:ℂ)) (M Ghalf),
    inverseOperator_coe ε y hε hy j,inverseOperator_coe ε y hε hy G,
    shearOutput_coe ε a α β p y b hε ha hα hβ hw hy h,
    gaussianState_profile ε a α β p y b hε ha hα hβ hw hy,
    gaussian_moment_coe ε a α β p y b hε ha hα hβ hw hy] with x ho hsum hc hs hu hv hzj hzg hj hg hm
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hsum hc hs hu hv
  change _ = (Z j+c • (u-v)) x
  rw [ho,hsum,hc,hs,hu,hv,hzj,hzg,hj,hg,hm]
  dsimp only [c]
  ring

#print axioms output_coe
#print axioms output_expansion
end
end UnifiedTheory.Audit.KFCausalGaussianLongitudinalOutput

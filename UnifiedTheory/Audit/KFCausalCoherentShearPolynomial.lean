/- Expand the actual shifted shear output into physical linear and
quadratic moments with bounded clock coefficients. This identity keeps
the neutral shear and the half-density term. -/
import UnifiedTheory.Audit.KFCausalCoherentShearCompositions
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalCoherentShearPolynomial
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position direction slope)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth scale_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput gaussianState)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput)

def coordinate (i : Fin 5) : Transverse →L[ℝ] ℝ := ContinuousLinearMap.proj i
def mix : Transverse →L[ℝ] ℝ := coordinate 2+coordinate 3

theorem slope_expansion (r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    KFCausalRelativeGaussianDifferential.slope r α β b x =
      (∑ i : Fin 4, (b i.castSucc/2)*r x.1*(x.2 i.castSucc:ℂ))+
      b 4*r x.1*(mix x.2:ℂ)-
      (α:ℂ)*(r x.1)^2*(∑ i : Fin 4, (x.2 i.castSucc:ℂ)^2)-
      2*(β:ℂ)*r x.1*(x.2 4:ℂ)*(mix x.2:ℂ)-
      4*(β:ℂ)*((r x.1)^2-r x.1)*(mix x.2:ℂ)^2 := by
  simp [KFCausalRelativeGaussianDifferential.slope,position,direction,
    KFCausalPhysicalGaussianMoments.widths,Fin.sum_univ_succ,mix,coordinate]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hbound : |h| ≤ 2*Real.pi*ε/3)

def scaleOperator : Hilbert →L[ℂ] Hilbert :=
  KFCausalBoundedLpMultiplier.operator (fun x : Configuration => scale ε (-h/2) x.1)
    (((scale_smooth ε (-h/2) hε (shift_bound ε h hbound)).continuous).comp continuous_fst).measurable
    (Real.exp (|(-h/2)|/(2*ε))) (Real.exp_pos _).le
    (fun x => scale_bound ε (-h/2) x.1 hε (shift_bound ε h hbound))

theorem scaleOperator_coe (f : Hilbert) :
    scaleOperator ε h hε hbound f =ᵐ[volume] fun x => scale ε (-h/2) x.1*f x :=
  KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ f

theorem shiftedShearOutput_coe (k : Joint 2 4) :
    shiftedShearOutput ε a h hε ha hh hbound k =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*(KFCausalRelativeGaussianDifferential.slope (scale ε (-h/2))
        (groundWidth h) (neutralWidth h) (sourceCoefficients h k) x+1)*
        shiftedOutput ε a h hε ha hh hbound k x := by
  let A := KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a (clockFrequency k) (-h/2)
  let r := scale ε (-h/2)
  let g := gaussianState ε a (groundWidth h) (neutralWidth h) (clockFrequency k)
    (sourceCoefficients h k) (-h/2) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hbound)
  let j := KFCausalShiftedGaussianShearDomain.shearOutput ε a (groundWidth h) (neutralWidth h)
    (clockFrequency k) (-h/2) (sourceCoefficients h k) hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hbound) h
  have hg := KFCausalShiftedGaussianPhysicalProfile.gaussianState_profile ε a
    (groundWidth h) (neutralWidth h) (clockFrequency k) (-h/2) (sourceCoefficients h k)
    hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (shift_bound ε h hbound)
  have hj := KFCausalShiftedGaussianShearDomain.shearOutput_coe ε a
    (groundWidth h) (neutralWidth h) (clockFrequency k) (-h/2) (sourceCoefficients h k)
    hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (shift_bound ε h hbound) h
  filter_upwards [Lp.coeFn_smul (amplitudeConstant h k) j,Lp.coeFn_smul (amplitudeConstant h k) g,hg,hj]
    with x ha' hb' hg' hj'
  change ((amplitudeConstant h k) • j) x =
    (-Complex.I*(h:ℂ))*(KFCausalRelativeGaussianDifferential.slope r _ _ _ x+1)*
      ((amplitudeConstant h k) • g) x
  rw [ha',hb']
  simp only [Pi.smul_apply,smul_eq_mul]
  change g x = _ at hg'
  change j x = _ at hj'
  rw [hg',hj']
  ring

#print axioms slope_expansion
#print axioms scaleOperator_coe
#print axioms shiftedShearOutput_coe
end
end UnifiedTheory.Audit.KFCausalCoherentShearPolynomial

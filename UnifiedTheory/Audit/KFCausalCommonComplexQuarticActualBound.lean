/- The original full-Joint quartic channel has a state-independent
actual clock response bound for one common arbitrary complex neutral
source and P=1. Distinct charged widths and coherent coefficients are
unrestricted within the original physical width floor. -/
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticJointResponse
import UnifiedTheory.Audit.KFCausalChargedQuarticPhysicalBound
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexQuarticActualBound
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalJointClockCoolingCoercivity (imaginaryRate)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalReciprocalGaussianCoordinates (area)

variable (n : ℕ) (α β ε y s : ℝ) (w : Fin n→ℝ)
    (hα : 0<α) (hβ : 0<β) (hwidth : 32*β≤α) (hε : 0<ε)
    (hy : |y|≤Real.pi*ε/3) (hw : ∀i,1≤w i)
local notation "r" => scale ε y s
include hα hβ hwidth hε hy hw

private theorem actual_geometry : |(r).im|<(r).re ∧
    (∀i,8*β*(r).im^2<2*(gamma α r).re*w i) ∧
    (∀i,0<(w i*α)*area r) ∧ (∀i,0<(w i*α)*area r-8*β*(r).im^2) := by
  have ha := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
  have hA := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have hr : |(r).im|<(r).re := by nlinarith [sq_abs (r).im,abs_nonneg (r).im]
  have hf (i : Fin n) : 0<(w i*α)*area r ∧ 0<(w i*α)*area r-8*β*(r).im^2 := by
    have hreg := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
    obtain ⟨hc,ha'⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hreg
    exact KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha' hc
  have hgamma : 2*(gamma α r).re=α*((r).re^2-(r).im^2) := by
    simp [gamma,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  refine ⟨hr,?_,fun i=>(hf i).1,fun i=>(hf i).2⟩
  intro i
  rw [hgamma]
  have h := (hf i).2
  unfold area at h
  nlinarith only [h]

theorem actual_integrable (A D : ℝ) (c : Fin n→ℂ) :
    Integrable (fun p:Joint=>KFCausalJointNeutralFourierOuterDensity.spatialFieldResponse n α β w
      (fun _=>source A D) c (fun _=>1) r (deriv (scale ε y) s)
      p.1.1 (p.1.2 0) p.2 2 (p.1.2 1)) jointMeasure := by
  have hg := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  simp_rw [KFCausalFiniteChannelCoolingSplit.spatial_response_eq]
  exact KFCausalFiniteNeutralResponseIntegrability.channel_response_integrable n α β w
    (fun _=>source A D) c (fun _=>1) 2 r (deriv (scale ε y) s) hβ hg.2.2.1 hg.2.2.2

omit hα hβ hwidth hε hy hw in
theorem global_bound : ∃ K : ℝ,0≤K ∧ ∀ (n : ℕ) (α β ε y s A D : ℝ)
    (w : Fin n→ℝ) (c : Fin n→ℂ),0<α→0<β→32*β≤α→0<ε→|y|≤Real.pi*ε/3→(∀i,1≤w i)→
    (∫p:Joint,KFCausalJointNeutralFourierOuterDensity.spatialFieldResponse n α β w
      (fun _=>source A D) c (fun _=>1) (scale ε y s) (deriv (scale ε y) s)
      p.1.1 (p.1.2 0) p.2 2 (p.1.2 1) ∂jointMeasure)≤
      K*fraction ε s*(∫p:Joint,KFCausalCommonComplexQuarticJointAngular.energyDensity n α β A D w
        (scale ε y s) c p ∂jointMeasure) := by
  obtain ⟨K,hK,hbound⟩ := KFCausalChargedQuarticPhysicalBound.global_bound
  refine ⟨K,hK,?_⟩
  intro n α β ε y s A D w c hα hβ hwidth hε hy hw
  let rr := scale ε y s
  let ell := imaginaryRate (fraction ε s) rr
  have hg := actual_geometry n α β ε y s w hα hβ hwidth hε hy hw
  have hwp : ∀i,0<w i := fun i=>lt_of_lt_of_le (by norm_num) (hw i)
  have hi := KFCausalJointFourierDilationJet.actual_imaginary_cancellation ε y s hε hy
  have he := KFCausalCommonComplexQuarticJointResponse.energy_integral n α β A D w rr c hα hβ hg.1 hwp hg.2.1
  rw [KFCausalCommonComplexQuarticJointResponse.response_integral n α β A D w rr
    (deriv (scale ε y) s) c ell hα hβ hg.1 hwp hg.2.1 hi,he]
  have hb := hbound n α β ε y s (4*D*rr.im) (A/(2*β)) w (fun i=>c i*(w i:ℂ))
    hα hβ hε hy hwp hg.2.1
  have hm := mul_le_mul_of_nonneg_left hb
    (KFCausalCommonComplexQuarticNeutralIntegral.mass_positive β A hβ).le
  convert hm using 1
  ring

#print axioms actual_integrable
#print axioms global_bound
end
end UnifiedTheory.Audit.KFCausalCommonComplexQuarticActualBound

/- The original spatial geometry response obeys a full integrated bound
for any finite packet family with at most two distinct charged widths.
All neutral sources, coefficients and polynomial degrees are retained.
The packet coefficients are fixed during this geometry derivative. -/
import UnifiedTheory.Audit.KFCausalChargedMarginalReordering
import UnifiedTheory.Audit.KFCausalFiniteNeutralResponseIntegrability
import UnifiedTheory.Audit.KFCausalTwoWidthCoolingMarginalBound
import UnifiedTheory.Audit.KFCausalTwoWidthPhysicalClockLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalTwoWidthIntegratedResponse
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity positiveDensity_nonneg)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointNeutralFourierOuterDensity (spatialQuarticResponse)
open KFCausalCorrelatedFourierCoolingResponse (cooling)
open KFCausalJointFourierDilationQuartic (quartic)
open KFCausalChargedMarginalReordering (outer_integrable integral_order)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction actual_normalized_velocity)
open KFCausalJointClockCoolingCoercivity (imaginaryRate)
open KFCausalJointFourierDissipationClock

def fieldLoss (α : ℝ) (r rd : ℂ) (ell m : ℝ) : ℝ :=
  4*(-2*(rd.re-ell*r.re)-3*ell)^2/(α*r.re*(rd.re-ell*r.re)*m)

theorem cooling_integrable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (r rd : ℂ) (ell : ℝ)
    (hi : rd.im=ell*r.im) (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) :
    Integrable (cooling n α β w b c P r rd ell) jointMeasure := by
  have hR := KFCausalFiniteNeutralResponseIntegrability.spatial_response_integrable
    n α β w b c P r rd hβ hA hC
  have hD := KFCausalJointFourierDilationQuartic.integrable
    n α β w b c P r ell hβ hA hC
  apply (hR.sub hD).congr
  exact Filter.Eventually.of_forall
    (KFCausalCorrelatedFourierCoolingResponse.pointwise_identity n α β w b c P r rd ell hi)

theorem cooling_integral_bound (n : ℕ) (α β : ℝ) (w : Fin 2 → ℝ)
    (label : Fin n → Fin 2) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (r rd : ℂ) (ell : ℝ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (hδ : 0 < rd.re-ell*r.re) (hi : rd.im=ell*r.im)
    (hβ : 0 < β) (hA : ∀ i, 0 < (w (label i)*α)*area r)
    (hC : ∀ i, 0 < (w (label i)*α)*area r-8*β*r.im^2) :
    (∫ p, cooling n α β (w ∘ label) b c P r rd ell p ∂jointMeasure) ≤
      fieldLoss α r rd ell (min (w 0) (w 1))*
        ∫ p, positiveDensity n α β (w ∘ label) r c
          (fun i => exponentialProfile (b i) 1 (P i)) p ∂jointMeasure := by
  have hR := cooling_integrable n α β (w ∘ label) b c P r rd ell hi hβ hA hC
  have hE := KFCausalJointFourierDilationQuartic.density_integrable
    n α β (w ∘ label) b c P r hβ hA hC
  rw [integral_order _ hR,integral_order _ hE,← integral_const_mul]
  apply integral_mono (outer_integrable _ hR)
    ((outer_integrable _ hE).const_mul (fieldLoss α r rd ell (min (w 0) (w 1))))
  intro q
  exact KFCausalTwoWidthCoolingMarginalBound.physical_marginal_bound
    n α β w label b c P r rd ell q.1 q.2 hα hr hw hδ

theorem response_integral_bound (n : ℕ) (α β : ℝ) (w : Fin 2 → ℝ)
    (label : Fin n → Fin 2) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (r rd : ℂ) (ell : ℝ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (hδ : 0 < rd.re-ell*r.re) (hi : rd.im=ell*r.im)
    (hβ : 0 < β) (hA : ∀ i, 0 < (w (label i)*α)*area r)
    (hC : ∀ i, 0 < (w (label i)*α)*area r-8*β*r.im^2) :
    (∫ p : Joint, spatialQuarticResponse n α β (w ∘ label) b c P r rd
      p.1.1 (p.1.2 0) p.2 (p.1.2 1) ∂jointMeasure) ≤
      (-4*ell+fieldLoss α r rd ell (min (w 0) (w 1)))*
        ∫ p, positiveDensity n α β (w ∘ label) r c
          (fun i => exponentialProfile (b i) 1 (P i)) p ∂jointMeasure := by
  have hR := KFCausalFiniteNeutralResponseIntegrability.spatial_response_integrable
    n α β (w ∘ label) b c P r rd hβ hA hC
  have hD := KFCausalJointFourierDilationQuartic.integrable
    n α β (w ∘ label) b c P r ell hβ hA hC
  have he := integral_congr_ae (μ := jointMeasure) (Filter.Eventually.of_forall
    (KFCausalCorrelatedFourierCoolingResponse.pointwise_identity
      n α β (w ∘ label) b c P r rd ell hi))
  rw [integral_sub hR hD,KFCausalJointFourierDilationQuartic.integral_identity
    n α β (w ∘ label) b c P r ell hβ hA hC] at he
  have hb := cooling_integral_bound n α β w label b c P r rd ell hα hr hw hδ hi hβ hA hC
  nlinarith only [he,hb]

theorem actual_integral_bound (n : ℕ) (α β ε y s : ℝ) (w : Fin 2 → ℝ)
    (label : Fin n → Fin 2) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    (∫ p : Joint, spatialQuarticResponse n α β (w ∘ label) b c P
      (scale ε y s) (deriv (scale ε y) s)
      p.1.1 (p.1.2 0) p.2 (p.1.2 1) ∂jointMeasure) ≤
      ((48+82944/α)*fraction ε s)*
        ∫ p, positiveDensity n α β (w ∘ label) (scale ε y s) c
          (fun i => exponentialProfile (b i) 1 (P i)) p ∂jointMeasure := by
  let r := scale ε y s
  let rd := deriv (scale ε y) s
  let ell := imaginaryRate (fraction ε s) r
  have hf := KFCausalClusteredResponseLimit.actual_width_floors α β ε y
    hα hβ hwidth hε hy s
  have hp := KFCausalChargedPairCompactGeometry.widthFloor_positive α hα
  have hfloor (i : Fin n) := KFCausalJointFourierDilationQuartic.width_floors
    α r (w (label i)) β (hw (label i)) (hp.trans_le hf.1) (hp.trans_le hf.2)
  have hδ : 0 < rd.re-ell*r.re := by
    dsimp only [rd,ell,r]
    rw [(actual_normalized_velocity ε y s hε hy).deriv]
    exact actual_real_cooling_positive ε y s hε hy
  have hi : rd.im=ell*r.im :=
    KFCausalJointFourierDilationJet.actual_imaginary_cancellation ε y s hε hy
  have hb := response_integral_bound n α β w label b c P r rd ell hα
    (KFCausalChargedCoolingActualPhase.actual_sector ε y s hε hy)
    (fun i => zero_lt_one.trans_le (hw i)) hδ hi hβ
    (fun i => (hfloor i).1) (fun i => (hfloor i).2)
  have hl : -4*ell+fieldLoss α r rd ell (min (w 0) (w 1)) =
      KFCausalTwoWidthPhysicalClockLoss.loss α (min (w 0) (w 1)) (fraction ε s) r := by
    unfold fieldLoss KFCausalTwoWidthPhysicalClockLoss.loss
    dsimp only [rd,ell]
    rw [(actual_normalized_velocity ε y s hε hy).deriv,real_cooling_identity]
    have hk : -2*(fraction ε s*normalizedRealCooling (fraction ε s) r)-
        3*imaginaryRate (fraction ε s) r =
        fraction ε s*normalizedFieldJet (fraction ε s) r := by
      rw [dilation_identity]
      unfold normalizedFieldJet
      ring
    rw [hk]
  rw [hl] at hb
  have hlb := KFCausalTwoWidthPhysicalClockLoss.actual_loss_bound ε y s hε hy
    α (min (w 0) (w 1)) hα (le_min (hw 0) (hw 1))
  have hE : 0 ≤ ∫ p, positiveDensity n α β (w ∘ label) r c
      (fun i => exponentialProfile (b i) 1 (P i)) p ∂jointMeasure :=
    integral_nonneg (positiveDensity_nonneg n α β (w ∘ label) r c
      (fun i => exponentialProfile (b i) 1 (P i)))
  exact hb.trans (mul_le_mul_of_nonneg_right hlb hE)

#print axioms cooling_integrable
#print axioms cooling_integral_bound
#print axioms response_integral_bound
#print axioms actual_integral_bound
end
end UnifiedTheory.Audit.KFCausalTwoWidthIntegratedResponse

/- The original correlated clock response splits into its exact charged
Jacobian contribution and a pure-real charged cooling response. All
full-space integrability is derived for the constructed finite family. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationQuartic
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedFourierCoolingResponse
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalNeutralFourierMovingJet (chargedSlope)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalClusteredClockFactors (Z)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointFourierDilationQuartic (quartic)
open KFCausalJointNeutralFourierOuterDensity (spatialQuarticResponse)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r rd : ℂ) (ell : ℝ)

def fieldCooling (j : ℕ) (p : Joint) : ℝ :=
  KFCausalNeutralFourierResponseSplit.response n β b (coefficients n w c (Z α r p))
    (chargedSlope n α w c r ((rd.re-ell*r.re:ℝ):ℂ) p.1.1 (p.1.2 0) p.2) P j
    (fieldSlope r*p.1.2 0) (2*r.im*p.1.2 0) ((-2*(rd.re-ell*r.re)-3*ell)*p.1.2 0) 0 (p.1.2 1)

def cooling (p : Joint) : ℝ :=
  fieldCooling n α β w b c P r rd ell 0 p+fieldCooling n α β w b c P r rd ell 1 p/2+
    fieldCooling n α β w b c P r rd ell 2 p/4

theorem pointwise_identity (hi : rd.im=ell*r.im) (p : Joint) :
    spatialQuarticResponse n α β w b c P r rd p.1.1 (p.1.2 0) p.2 (p.1.2 1)-
      quartic n α β w b c P r ell p = cooling n α β w b c P r rd ell p := by
  have h := KFCausalJointFourierDilationJet.corrected_response n β b P α w c r rd ell
    p.1.1 (p.1.2 0) p.2 (p.1.2 1)
  have h0 := h 0 hi
  have h1 := h 1 hi
  have h2 := h 2 hi
  unfold spatialQuarticResponse KFCausalJointNeutralFourierOuterDensity.spatialFieldResponse
    quartic KFCausalJointFourierDilationResponse.response cooling fieldCooling Z
  linarith

variable {m : ℕ} (f : KFCausalCorrelatedClusteredProfiles.Family m) (δ : ℝ) (hδ : 0 < δ)
open KFCausalCorrelatedClusteredProfiles
include hδ

omit n w b c P in
theorem constructed_pointwise (hi : rd.im=ell*r.im) (p : Joint) :
    KFCausalCorrelatedClusteredDensity.response f α β δ r rd p-
      quartic (count f) α β (widths f δ) (sources f) (coefficients f δ) (polynomials f) r ell p =
      cooling (count f) α β (widths f δ) (sources f) (coefficients f δ) (polynomials f) r rd ell p := by
  have hp : ((p.1.1,![p.1.2 0,p.1.2 1]),p.2) = p := by
    congr 2
    ext i
    fin_cases i <;> rfl
  have he := KFCausalCorrelatedClusteredFourierResponse.response_spatial f α β δ hδ r rd
    p.1.1 (p.1.2 0) (p.1.2 1) p.2
  rw [hp] at he
  rw [he]
  exact pointwise_identity (count f) α β _ _ _ _ r rd ell hi p

variable (hβ : 0 < β) (ha : 0 < α*area r) (hc : 0 < α*area r-8*β*r.im^2)
include hβ ha hc

omit n w b c P in
theorem constructed_integrable (hi : rd.im=ell*r.im) :
    Integrable (cooling (count f) α β (widths f δ) (sources f) (coefficients f δ)
      (polynomials f) r rd ell) jointMeasure := by
  have hf (i : Fin (count f)) := KFCausalJointFourierDilationQuartic.width_floors α r
    (widths f δ i) β (widths_admissible f δ hδ.le i) ha hc
  have hD := KFCausalJointFourierDilationQuartic.integrable (count f) α β (widths f δ)
    (sources f) (coefficients f δ) (polynomials f) r ell hβ (fun i => (hf i).1) (fun i => (hf i).2)
  have hR := (KFCausalCorrelatedClusteredIntegrals.integrability f α β δ hδ r rd hβ ha hc).2.1
  change Integrable (fun p => cooling (count f) α β (widths f δ) (sources f) (coefficients f δ)
    (polynomials f) r rd ell p) jointMeasure
  simp_rw [← constructed_pointwise α β r rd ell f δ hδ hi]
  exact hR.sub hD

omit n w b c P in
theorem constructed_integral (hi : rd.im=ell*r.im) :
    (∫ p, KFCausalCorrelatedClusteredDensity.response f α β δ r rd p ∂jointMeasure) =
      -4*ell*(∫ p, KFCausalCorrelatedClusteredDensity.density f α β δ r p ∂jointMeasure)+
        ∫ p, cooling (count f) α β (widths f δ) (sources f) (coefficients f δ)
          (polynomials f) r rd ell p ∂jointMeasure := by
  have hf (i : Fin (count f)) := KFCausalJointFourierDilationQuartic.width_floors α r
    (widths f δ i) β (widths_admissible f δ hδ.le i) ha hc
  have hD := KFCausalJointFourierDilationQuartic.integrable (count f) α β (widths f δ)
    (sources f) (coefficients f δ) (polynomials f) r ell hβ (fun i => (hf i).1) (fun i => (hf i).2)
  have hR := (KFCausalCorrelatedClusteredIntegrals.integrability f α β δ hδ r rd hβ ha hc).2.1
  have he := integral_congr_ae (μ := jointMeasure) (Filter.Eventually.of_forall
    (constructed_pointwise α β r rd ell f δ hδ hi))
  rw [integral_sub hR hD,
    KFCausalJointFourierDilationQuartic.integral_identity (count f) α β (widths f δ)
      (sources f) (coefficients f δ) (polynomials f) r ell hβ (fun i => (hf i).1) (fun i => (hf i).2)] at he
  exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)

omit n w b c P r rd ell ha hc in
theorem actual_totalResponse (ε y s : ℝ) (hα : 0 < α) (hw : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) :
    let r := KFCausalClockFloorRelativeShift.scale ε y s
    let rd := deriv (KFCausalClockFloorRelativeShift.scale ε y) s
    let ell := KFCausalJointClockCoolingCoercivity.imaginaryRate
      (KFCausalNeutralPlaneNormalizedGeometry.fraction ε s) r
    KFCausalReciprocalNeutralClockDerivative.totalResponse (count f) ε y α β (widths f δ)
      (sources f) (polynomials f) (fun _ => coefficients f δ) s =
      -4*ell*KFCausalReciprocalNeutralClockDerivative.totalEnergy (count f) ε y α β (widths f δ)
        (sources f) (polynomials f) (fun _ => coefficients f δ) s+
      Real.pi/4*(∫ p, cooling (count f) α β (widths f δ) (sources f) (coefficients f δ)
        (polynomials f) r rd ell p ∂jointMeasure) := by
  dsimp only
  have hf := KFCausalClusteredResponseLimit.actual_width_floors α β ε y hα hβ hw hε hy s
  have hp := KFCausalChargedPairCompactGeometry.widthFloor_positive α hα
  rw [KFCausalCorrelatedClusteredResponseLimit.actual_totalResponse_integral f α β ε y
    hα hβ hw hε hy δ hδ s,
    KFCausalCorrelatedClusteredResponseLimit.actual_totalEnergy_integral f α β ε y
    hα hβ hw hε hy δ hδ s,
    constructed_integral α β _ _ _ f δ hδ hβ (hp.trans_le hf.1) (hp.trans_le hf.2)
      (KFCausalJointFourierDilationJet.actual_imaginary_cancellation ε y s hε hy)]
  ring

#print axioms pointwise_identity
#print axioms constructed_pointwise
#print axioms constructed_integrable
#print axioms constructed_integral
#print axioms actual_totalResponse
end
end UnifiedTheory.Audit.KFCausalCorrelatedFourierCoolingResponse

/- Explicit Fourier formulas for the original transport and complete
potential response of the constructed correlated clustered family.
The neutral frequency variable remains innermost. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierResponse
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalClockLimit
import UnifiedTheory.Audit.KFCausalJointNeutralFourierResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierResponsePhysical
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift amplitudes)
open KFCausalJointNeutralFourierMarginal (quarticResponse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)

def explicitTransport (δ s : ℝ) : ℝ :=
  let g := reweight f (amplitudes ε (-h/2) a p s)
  Real.pi/4*(∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
    quarticResponse (count g) (groundWidth h) (neutralWidth h) (widths g δ)
      (sources g) (coefficients g δ) (polynomials g)
      (scale ε (-h/2) s) (deriv (scale ε (-h/2)) s) u v Y k)

def explicitReduced (δ s : ℝ) : ℝ :=
  KFCausalClockResponseTransport.coefficient ε (-h/2) s*
    KFCausalJointNeutralFourierResponse.energy (count f) (groundWidth h) (neutralWidth h)
      (widths f δ) (sources f)
      (KFCausalReciprocalNeutralPositiveEnergy.coefficients (count f) ε h
        (lift f a) (lift f p) (coefficients f δ) s) (polynomials f) (scale ε (-h/2) s)-
    explicitTransport f ε h a p δ s/KFCausalClockResponseTransport.clock ε s

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
include hε hh hb

theorem transport_identity (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    KFCausalReciprocalNeutralWholeClock.transportResponse (count f) ε h (lift f a)
      (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f) s =
      explicitTransport f ε h a p δ s := by
  rw [KFCausalCorrelatedClusteredPhysicalClockLimit.slice_transport f ε h a p hε hh hb δ hδ s]
  have hf := KFCausalClusteredResponseLimit.actual_width_floors (groundWidth h) (neutralWidth h)
    ε (-h/2) (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    hε (KFCausalCorrelatedClusteredPhysicalClockLimit.shift_bound ε h hb) s
  have hq := KFCausalChargedPairCompactGeometry.widthFloor_positive (groundWidth h) (groundWidth_positive h hh)
  unfold KFCausalCorrelatedClusteredWholeClock.transport explicitTransport
  dsimp only
  rw [KFCausalCorrelatedClusteredFourierResponse.response_integral _ _ _ δ hδ
    (neutralWidth_positive h hh) _ _ (hq.trans_le hf.1) (hq.trans_le hf.2)]

theorem reduced_identity (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    KFCausalReciprocalNeutralWholeClock.reducedResponse (count f) ε h (lift f a)
      (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f) s =
      explicitReduced f ε h a p δ s := by
  unfold KFCausalReciprocalNeutralWholeClock.reducedResponse explicitReduced
  rw [KFCausalJointNeutralFourierResponse.actual_slice_fourier _ _ _ _ _ _ _ _ _
    hε hh (widths_admissible f δ hδ.le) hb,
    transport_identity f ε h a p hε hh hb δ hδ s]

variable (ha : ∀ i, 0 < a i)
include ha

theorem transport_integrable (δ : ℝ) (hδ : 0 < δ) :
    Integrable (explicitTransport f ε h a p δ) := by
  have hy := KFCausalCorrelatedClusteredPhysicalClockLimit.shift_bound ε h hb
  have hi := (KFCausalCorrelatedClusteredWholeClock.integrability f (amplitudes ε (-h/2) a p)
    (groundWidth h) (neutralWidth h) ε (-h/2) (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε hy
    (KFCausalCorrelatedClusteredPhysicalClockLimit.amplitudes_continuous ε (-h/2) a p hε hy)
    (KFCausalCorrelatedClusteredPhysicalClockLimit.amplitudes_memLp ε (-h/2) a p hε hy ha) δ hδ).2.1
  unfold KFCausalCorrelatedClusteredWholeClock.wholeMeasure at hi
  apply (hi.integral_prod_left.const_mul (Real.pi/4)).congr
  filter_upwards [] with s
  exact (KFCausalCorrelatedClusteredPhysicalClockLimit.slice_transport f ε h a p hε hh hb δ hδ s).symm.trans
    (transport_identity f ε h a p hε hh hb δ hδ s)

theorem reduced_integrable (δ : ℝ) (hδ : 0 < δ) :
    Integrable (explicitReduced f ε h a p δ) :=
  (KFCausalReciprocalNeutralWholeClock.response_integrability (count f) ε h (lift f a)
    (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
    hε hh (widths_admissible f δ hδ.le) hb (fun j => ha (index f j).1)).2.1.congr
    (Filter.Eventually.of_forall (reduced_identity f ε h a p hε hh hb δ hδ))

theorem potential_identity (δ : ℝ) (hδ : 0 < δ) :
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse (count f) ε h (lift f a)
      (widths f δ) (lift f p) (coefficients f δ) (sources f) (polynomials f)
      hε (fun j => ha (index f j).1) hh (widths_admissible f δ hδ.le) hb =
      ∫ s, explicitReduced f ε h a p δ s := by
  rw [KFCausalReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (reduced_identity f ε h a p hε hh hb δ hδ)

#print axioms transport_identity
#print axioms reduced_identity
#print axioms transport_integrable
#print axioms reduced_integrable
#print axioms potential_identity
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierResponsePhysical

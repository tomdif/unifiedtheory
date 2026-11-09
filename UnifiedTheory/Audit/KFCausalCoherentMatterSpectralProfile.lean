/- The actual second matter spectral endpoint is a mixed field power
times the doubled-shift coherent output, retaining the original widths. -/
import UnifiedTheory.Audit.KFCausalMixedFieldCoherentPureClock
import UnifiedTheory.Audit.KFCausalCoherentMatterSquare
import UnifiedTheory.Audit.KFCausalVariableWidthOrderedProfile
import UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral
import UnifiedTheory.Audit.KFCausalMixedFieldClockBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterSpectralProfile
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalMixedFieldPhysicalProfile (field field_smooth)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalCoherentMatterSquare (spectralOutput)
open KFCausalClockFloorSourcedSpectral (shiftedOutput)
open KFCausalVariableWidthOrderedProfile (gaussianProfile sourced_output_coe)
open KFCausalGaussianVacuumSquare (original_strip double_strip)
open KFCausalMixedFieldGaussianContour (strip_pair double_shift_bound)
open KFCausalUnboundedMultiplierIntegral (relation)

theorem half_double (h : ℝ) : -(2*h)/2 = -h := by ring
theorem two_halves (h : ℝ) : -h/2+(-h/2) = -h := by ring

def multiplier (ε h : ℝ) (j : Fin 2) (x : Configuration) : ℂ :=
  field (scale ε (-h/2) x.1) x.2^degree j

theorem field_eq (r : ℂ) (q : KFCausalTransverseDilationFlow.Transverse) :
    field r q = KFCausalMixedFieldClockBounds.field r q := by
  simp only [field,KFCausalMixedFieldClockBounds.field,Complex.ofReal_add]

theorem multiplier_continuous (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ Real.pi*ε/3) (j : Fin 2) :
    Continuous (multiplier ε h j) :=
  ((field_smooth _ (KFCausalClockFloorRelativeShift.scale_smooth ε (-h/2) hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h (original_strip ε h hε hb)))).pow (degree j)).continuous

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
local notation "hd" => double_shift_bound ε h hb
local notation "hs" => strip_pair ε (-h/2) |-h/2| (-h/2) hd le_rfl

theorem spectral_coe (j : Fin 2) :
    spectralOutput ε a α β hε ha hα hβ hw h hb C p b j =ᵐ[volume] fun x =>
      multiplier ε h j x*gaussianProfile ε a α β (2*h) C p b x := by
  filter_upwards [Lp.coeFn_smul C
    (KFCausalMixedFieldCoherentSpectral.state ε a α β (-h/2) p b (-h/2) j hε ha hα hβ hw hs.1 hs.2),
    KFCausalMixedFieldCoherentPureClock.state_profile ε a α β (-h/2) p (-h/2) b j hε ha hα hβ hw hs.1 hs.2]
    with x hc hx
  change (C • KFCausalMixedFieldCoherentSpectral.state ε a α β (-h/2) p b (-h/2) j
    hε ha hα hβ hw hs.1 hs.2 : Hilbert) x = _
  rw [hc,Pi.smul_apply,smul_eq_mul,hx]
  simp only [KFCausalMixedFieldCoherentPureClock.multiplier,multiplier,gaussianProfile,two_halves,half_double]
  ring

theorem spectral_relation (j : Fin 2) : relation (multiplier ε h j)
    (shiftedOutput ε a α β hε ha hα hβ hw C p b (2*h) (double_strip ε h hb))
    (spectralOutput ε a α β hε ha hα hβ hw h hb C p b j) := by
  filter_upwards [spectral_coe ε a α β hε ha hα hβ hw h hb C p b j,
    sourced_output_coe ε a α β hε ha hα hβ hw (2*h) (double_strip ε h hb) C p b] with x hsp hg
  rw [hsp,hg]

#print axioms half_double
#print axioms two_halves
#print axioms field_eq
#print axioms multiplier_continuous
#print axioms spectral_coe
#print axioms spectral_relation
end
end UnifiedTheory.Audit.KFCausalCoherentMatterSpectralProfile

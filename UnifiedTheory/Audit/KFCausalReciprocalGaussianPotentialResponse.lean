/- The reciprocal Gaussian state's actual potential response is an absolutely
integrable full-configuration density. All three ordered factors retain
the physical Gaussian clock slope. This identifies the remaining term
in the full response bound without assuming a bound on that term. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianOutputs
import UnifiedTheory.Audit.KFCausalReciprocalGaussianResponse
import UnifiedTheory.Audit.KFCausalChargedPairPotentialResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianPotentialResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockResponseTransport (weakSlope)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalReciprocalGaussianOutputs (shifted output_coe momentumOutput_coe)
open KFCausalReciprocalGaussianResponse
open KFCausalReciprocalGaussianHamiltonian (fullResponse)
open KFCausalChargedPairPotentialResponse (scalar_response_identity)

def pairDensity (ε a h w : ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  conj (shifted ε a h w n x)*
    (clockSlope ε a h 0 x*shifted ε a h w n x)

def responseDensity (ε a h w : ℝ) (n : Fin 3) (x : Configuration) : ℝ :=
  2*(weakSlope ε a 0 (-h/2) x.1).re*‖shifted ε a h w n x‖^2

def potentialDensity (ε a h w : ℝ) (x : Configuration) : ℝ :=
  responseDensity ε a h w 0 x+responseDensity ε a h w 1 x/2+responseDensity ε a h w 2 x/4

theorem response_density_identity (ε a h w : ℝ) (hh : h ≠ 0) (n : Fin 3) (x : Configuration) :
    (-2/h)*(pairDensity ε a h w n x).im = responseDensity ε a h w n x :=
  scalar_response_identity h hh _ _

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha hh hw hb in
theorem pairDensity_integrable (n : Fin 3) : Integrable (pairDensity ε a h w n) volume := by
  have hA := (Lp.memLp (KFCausalReciprocalGaussianMomentum.output ε a h w hε ha hh hw hb (index n))).ae_eq
    (output_coe ε a h w hε ha hh hw hb n)
  have hB := (Lp.memLp (KFCausalReciprocalGaussianMomentum.momentumOutput ε a h w hε ha hh hw hb (index n))).ae_eq
    (momentumOutput_coe ε a h w hε ha hh hw hb n)
  have hi := hA.star.integrable_mul hB
  simpa only [pairDensity,clockSlope,Complex.star_def] using hi

include hε ha hh hw hb in
theorem responseDensity_integrable (n : Fin 3) : Integrable (responseDensity ε a h w n) volume :=
  ((pairDensity_integrable ε a h w hε ha hh hw hb n).im.const_mul (-2/h)).congr
    (Filter.Eventually.of_forall (response_density_identity ε a h w hh n))

theorem factorRate_integral (n : Fin 3) :
    factorRate ε a h w hε ha hh hw hb (index n) = ∫ x, responseDensity ε a h w n x := by
  have hi :
      inner ℂ (KFCausalReciprocalGaussianMomentum.output ε a h w hε ha hh hw hb (index n))
        (KFCausalReciprocalGaussianMomentum.momentumOutput ε a h w hε ha hh hw hb (index n)) =
          ∫ x, pairDensity ε a h w n x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [output_coe ε a h w hε ha hh hw hb n,
      momentumOutput_coe ε a h w hε ha hh hw hb n] with x hu hm
    simp only [hu,hm,RCLike.inner_apply,pairDensity,clockSlope]
    ring
  have him : (∫ x, pairDensity ε a h w n x).im = ∫ x, (pairDensity ε a h w n x).im := by
    simpa only [RCLike.im_eq_complex_im] using
      (integral_im (pairDensity_integrable ε a h w hε ha hh hw hb n)).symm
  rw [factorRate,hi,him,← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (response_density_identity ε a h w hh n))

include hε ha hh hw hb in
theorem potentialDensity_integrable : Integrable (potentialDensity ε a h w) volume :=
  ((responseDensity_integrable ε a h w hε ha hh hw hb 0).add
    ((responseDensity_integrable ε a h w hε ha hh hw hb 1).div_const 2)).add
      ((responseDensity_integrable ε a h w hε ha hh hw hb 2).div_const 4)

theorem potentialResponse_integral :
    potentialResponse ε a h w hε ha hh hw hb = ∫ x, potentialDensity ε a h w x := by
  have h0 := factorRate_integral ε a h w hε ha hh hw hb 0
  have h1 := factorRate_integral ε a h w hε ha hh hw hb 1
  have h2 := factorRate_integral ε a h w hε ha hh hw hb 2
  change factorRate ε a h w hε ha hh hw hb 7 = ∫ x, responseDensity ε a h w 0 x at h0
  change factorRate ε a h w hε ha hh hw hb 5 = ∫ x, responseDensity ε a h w 1 x at h1
  change factorRate ε a h w hε ha hh hw hb 6 = ∫ x, responseDensity ε a h w 2 x at h2
  have h01 : Integrable (fun x => responseDensity ε a h w 0 x+responseDensity ε a h w 1 x/2) volume :=
    (responseDensity_integrable ε a h w hε ha hh hw hb 0).add
      ((responseDensity_integrable ε a h w hε ha hh hw hb 1).div_const 2)
  unfold potentialResponse potentialDensity
  rw [integral_add h01 ((responseDensity_integrable ε a h w hε ha hh hw hb 2).div_const 4),
    integral_add (responseDensity_integrable ε a h w hε ha hh hw hb 0)
      ((responseDensity_integrable ε a h w hε ha hh hw hb 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

theorem fullResponse_integral (t : ℝ) :
    fullResponse ε a h w hε ha hh hw hb 1 1 1 t =
      clockKineticResponse ε a h w hε ha hh hw hb t+
        Real.exp (2*t)*(∫ x, potentialDensity ε a h w x) := by
  rw [unit_full_response,potentialResponse_integral]

#print axioms response_density_identity
#print axioms pairDensity_integrable
#print axioms responseDensity_integrable
#print axioms factorRate_integral
#print axioms potentialDensity_integrable
#print axioms potentialResponse_integral
#print axioms fullResponse_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianPotentialResponse

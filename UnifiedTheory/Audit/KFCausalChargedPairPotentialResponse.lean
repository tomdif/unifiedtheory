/- The paired state's actual potential response is an absolutely
integrable full-configuration density. All three ordered factors retain
the physical Gaussian clock slope. This identifies the remaining term
in the full response bound without assuming a bound on that term. -/
import UnifiedTheory.Audit.KFCausalChargedPairOrderedMomentumDensity
import UnifiedTheory.Audit.KFCausalChargedPairHamiltonianResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairPotentialResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockResponseTransport (weakSlope)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalChargedPairOrderedOutputs (pairedShifted output_coe pairedShifted_memLp)
open KFCausalChargedPairOrderedMomentumDensity (momentum_density momentum_density_memLp)
open KFCausalChargedPairFactorResponse (factorRate)
open KFCausalChargedPairHamiltonianResponse
  (potentialResponse fullResponse clockKineticResponse unit_full_response)

theorem scalar_response_identity (h : ℝ) (hh : h ≠ 0) (z w : ℂ) :
    (-2/h)*(conj z*((-Complex.I*(h:ℂ))*w*z)).im = 2*w.re*‖z‖^2 := by
  have he : conj z*((-Complex.I*(h:ℂ))*w*z) =
      (-Complex.I*(h:ℂ))*w*(‖z‖^2:ℝ) := by
    push_cast
    rw [← Complex.conj_mul' z]
    ring
  rw [he]
  simp only [Complex.mul_im,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    neg_zero,zero_mul,zero_add,sub_zero,zero_sub,mul_zero]
  field_simp [hh]

def pairDensity (ε a h : ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  conj (pairedShifted ε a h pointField n x)*
    (clockSlope ε a h 0 x*pairedShifted ε a h pointField n x)

def responseDensity (ε a h : ℝ) (n : Fin 3) (x : Configuration) : ℝ :=
  2*(weakSlope ε a 0 (-h/2) x.1).re*‖pairedShifted ε a h pointField n x‖^2

def potentialDensity (ε a h : ℝ) (x : Configuration) : ℝ :=
  responseDensity ε a h 0 x+responseDensity ε a h 1 x/2+responseDensity ε a h 2 x/4

theorem response_density_identity (ε a h : ℝ) (hh : h ≠ 0) (n : Fin 3) (x : Configuration) :
    (-2/h)*(pairDensity ε a h n x).im = responseDensity ε a h n x :=
  scalar_response_identity h hh _ _

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha hh hb in
theorem pairDensity_integrable (n : Fin 3) : Integrable (pairDensity ε a h n) volume := by
  have hi := (pairedShifted_memLp ε a h hε ha hh hb modelDirections pointField n).star.integrable_mul
    (momentum_density_memLp ε a h hε ha hh hb pointField n)
  simpa only [pairDensity,Complex.star_def] using hi

include hε ha hh hb in
theorem responseDensity_integrable (n : Fin 3) : Integrable (responseDensity ε a h n) volume :=
  ((pairDensity_integrable ε a h hε ha hh hb n).im.const_mul (-2/h)).congr
    (Filter.Eventually.of_forall (response_density_identity ε a h hh n))

theorem factorRate_integral (n : Fin 3) :
    factorRate ε a h hε ha hh hb (index n) = ∫ x, responseDensity ε a h n x := by
  have hi :
      inner ℂ (KFCausalChargedPairDomain.output ε a h hε ha hh hb modelDirections pointField (index n))
        (KFCausalChargedPairClockMomentum.factor ε a h hε ha hh hb modelDirections pointField (index n)) =
          ∫ x, pairDensity ε a h n x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [output_coe ε a h hε ha hh hb modelDirections pointField n,
      momentum_density ε a h hε ha hh hb modelDirections pointField n] with x hu hm
    simp only [hu,hm,RCLike.inner_apply,pairDensity]
    ring
  have him : (∫ x, pairDensity ε a h n x).im = ∫ x, (pairDensity ε a h n x).im := by
    simpa only [RCLike.im_eq_complex_im] using
      (integral_im (pairDensity_integrable ε a h hε ha hh hb n)).symm
  rw [factorRate,hi,him,← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (response_density_identity ε a h hh n))

include hε ha hh hb in
theorem potentialDensity_integrable : Integrable (potentialDensity ε a h) volume :=
  ((responseDensity_integrable ε a h hε ha hh hb 0).add
    ((responseDensity_integrable ε a h hε ha hh hb 1).div_const 2)).add
      ((responseDensity_integrable ε a h hε ha hh hb 2).div_const 4)

theorem potentialResponse_integral :
    potentialResponse ε a h hε ha hh hb = ∫ x, potentialDensity ε a h x := by
  have h0 := factorRate_integral ε a h hε ha hh hb 0
  have h1 := factorRate_integral ε a h hε ha hh hb 1
  have h2 := factorRate_integral ε a h hε ha hh hb 2
  change factorRate ε a h hε ha hh hb 7 = ∫ x, responseDensity ε a h 0 x at h0
  change factorRate ε a h hε ha hh hb 5 = ∫ x, responseDensity ε a h 1 x at h1
  change factorRate ε a h hε ha hh hb 6 = ∫ x, responseDensity ε a h 2 x at h2
  have h01 : Integrable (fun x => responseDensity ε a h 0 x+responseDensity ε a h 1 x/2) volume :=
    (responseDensity_integrable ε a h hε ha hh hb 0).add
      ((responseDensity_integrable ε a h hε ha hh hb 1).div_const 2)
  unfold potentialResponse potentialDensity
  rw [integral_add h01 ((responseDensity_integrable ε a h hε ha hh hb 2).div_const 4),
    integral_add (responseDensity_integrable ε a h hε ha hh hb 0)
      ((responseDensity_integrable ε a h hε ha hh hb 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

theorem fullResponse_integral (t : ℝ) :
    fullResponse ε a h hε ha hh hb 1 1 1 t =
      clockKineticResponse ε a h hε ha hh hb t+
        Real.exp (2*t)*(∫ x, potentialDensity ε a h x) := by
  rw [unit_full_response,potentialResponse_integral]

#print axioms scalar_response_identity
#print axioms response_density_identity
#print axioms pairDensity_integrable
#print axioms responseDensity_integrable
#print axioms factorRate_integral
#print axioms potentialDensity_integrable
#print axioms potentialResponse_integral
#print axioms fullResponse_integral
end
end UnifiedTheory.Audit.KFCausalChargedPairPotentialResponse

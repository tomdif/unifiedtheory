/- Reduced whole-configuration kernels for finite normalized superpositions.
The configuration integral is taken first, then the two charge angles.
Every fixed-angle reduced kernel is integrable and its configuration
integral is integrable in the angles. Joint absolute integrability of the
reduced density, and arbitrary exchange of its integrations, are not claimed. -/
import UnifiedTheory.Audit.KFCausalStructuredChargeResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalStructuredReducedResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (Packet StructuredState inputOrbit momentumOrbit)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles measure)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (source clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalDisplacedResponseDensities (coefficient)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)

def kernel (reduced : Bool) (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (P Q : Packet) (n : Fin 3) (t : ℝ × ℝ) : Configuration → ℂ :=
  (if reduced then KFCausalGaussianResponseIntegrability.reducedDensity
    else KFCausalGaussianResponseIntegrability.weakDensity)
    ε (-h/2) P.width Q.width
    (clockFrequency h (parameter (2*Real.pi*t.1) P.frequency))
    (clockFrequency h (parameter (2*Real.pi*t.2) Q.frequency))
    (groundWidth h) (neutralWidth h) (groundWidth h) (neutralWidth h)
    (source h (parameter (2*Real.pi*t.1) P.centre) (parameter (2*Real.pi*t.1) P.frequency))
    (source h (parameter (2*Real.pi*t.2) Q.centre) (parameter (2*Real.pi*t.2) Q.frequency))
    (coefficient ε P.width h hε P.width_pos hh
      (parameter (2*Real.pi*t.1) P.centre) (parameter (2*Real.pi*t.1) P.frequency))
    (coefficient ε Q.width h hε Q.width_pos hh
      (parameter (2*Real.pi*t.2) Q.centre) (parameter (2*Real.pi*t.2) Q.frequency)) pointField n

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hb in
theorem kernel_integrable (reduced : Bool) (P Q : Packet) (n : Fin 3) (t : ℝ × ℝ) :
    Integrable (kernel reduced ε h hε hh P Q n t) volume := by
  cases reduced
  · exact KFCausalGaussianResponseIntegrability.weakDensity_integrable
      ε P.width Q.width _ _ (groundWidth h) (neutralWidth h) (groundWidth h) (neutralWidth h)
      _ _ _ _ pointField n h hε hh hb P.width_pos Q.width_pos
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
  · exact KFCausalGaussianResponseIntegrability.reducedDensity_integrable
      ε P.width Q.width _ _ (groundWidth h) (neutralWidth h) (groundWidth h) (neutralWidth h)
      _ _ _ _ pointField n h hε hh hb P.width_pos Q.width_pos
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)

include hb in
theorem kernel_integrals_eq (P Q : Packet) (n : Fin 3) (t : ℝ × ℝ) :
    (∫ x : Configuration, kernel false ε h hε hh P Q n t x) =
      ∫ x : Configuration, kernel true ε h hε hh P Q n t x :=
  KFCausalGaussianWholeClockResponse.configuration_integrals_eq
    ε P.width Q.width _ _ (groundWidth h) (neutralWidth h) (groundWidth h) (neutralWidth h)
    h _ _ _ _ pointField n hε hh hb P.width_pos Q.width_pos
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)

private theorem finite_cross {m n : ℕ} (c : Fin m → ℂ) (d : Fin n → ℂ)
    (A M : Fin m → ℂ) (B N : Fin n → ℂ) (r : ℂ) :
    r*(star (∑ i, c i*A i)*(∑ j, d j*N j)-star (∑ i, c i*M i)*(∑ j, d j*B j)) =
      ∑ i, ∑ j, (star (c i)*d j)*(r*(star (A i)*N j-star (M i)*B j)) := by
  calc
    _ = ∑ i, ∑ j, r*(star (c i*A i)*(d j*N j)-star (c i*M i)*(d j*B j)) := by
      simp only [mul_sub,star_sum,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
      congr 1 <;> exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [star_mul]
      ring

variable (P Q : StructuredState) (n : Fin 3)

def density (reduced : Bool) (t : ℝ × ℝ) (x : Configuration) : ℂ :=
  ∑ i, ∑ j, (star (P.coefficient i)*Q.coefficient j)*
    kernel reduced ε h hε hh (P.packet i) (Q.packet j) n t x

theorem weak_cross_terms (t : ℝ × ℝ) (x : Configuration) :
    KFCausalStructuredChargeResponse.weakDensity ε h hε hh P Q n (t,x) =
      density ε h hε hh P Q n false t x := by
  unfold KFCausalStructuredChargeResponse.weakDensity KFCausalChargeResponseFubini.pair
    KFCausalStructuredChargeResponse.inputDensity KFCausalStructuredChargeResponse.momentumDensity
  rw [finite_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (KFCausalGaussianResponseIntegrability.weak_factorization ε (-h/2)
    (P.packet i).width (Q.packet j).width _ _ (groundWidth h) (neutralWidth h)
    (groundWidth h) (neutralWidth h) _ _ _ _ pointField n h hh x).symm

include hb in
theorem density_integrable (reduced : Bool) (t : ℝ × ℝ) :
    Integrable (density ε h hε hh P Q n reduced t) volume :=
  integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
    (kernel_integrable ε h hε hh hb reduced (P.packet i) (Q.packet j) n t).const_mul _))

include hb in
theorem configuration_integrals_eq (t : ℝ × ℝ) :
    (∫ x : Configuration, KFCausalStructuredChargeResponse.weakDensity ε h hε hh P Q n (t,x)) =
      ∫ x : Configuration, density ε h hε hh P Q n true t x := by
  simp_rw [weak_cross_terms ε h hε hh P Q n t]
  have hw (i : Fin P.size) (j : Fin Q.size) : Integrable (fun x =>
      (star (P.coefficient i)*Q.coefficient j)*kernel false ε h hε hh (P.packet i) (Q.packet j) n t x) volume :=
    (kernel_integrable ε h hε hh hb false (P.packet i) (Q.packet j) n t).const_mul _
  have hr (i : Fin P.size) (j : Fin Q.size) : Integrable (fun x =>
      (star (P.coefficient i)*Q.coefficient j)*kernel true ε h hε hh (P.packet i) (Q.packet j) n t x) volume :=
    (kernel_integrable ε h hε hh hb true (P.packet i) (Q.packet j) n t).const_mul _
  unfold density
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hw i j)),
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hr i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hw i j),integral_finset_sum _ (fun j _ => hr i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_const_mul,kernel_integrals_eq ε h hε hh hb]

include hb in
theorem reduced_iterated_integrable :
    Integrable (fun t => ∫ x : Configuration, density ε h hε hh P Q n true t x) angles := by
  have hi := (KFCausalStructuredChargeResponse.weak_integrable ε h hε hh hb P Q n).integral_prod_left
  apply hi.congr
  exact Filter.Eventually.of_forall (configuration_integrals_eq ε h hε hh hb P Q n)

include hb in
theorem reduced_iterated_pairing :
    (∫ t, ∫ x : Configuration, density ε h hε hh P Q n true t x ∂volume ∂angles) =
      (Complex.I/(h:ℂ))*(
        inner ℂ (∫ θ, inputOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
          (∫ φ, momentumOrbit ε h hε hh hb Q (index n) φ ∂angleMeasure)-
        inner ℂ (∫ θ, momentumOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
          (∫ φ, inputOrbit ε h hε hh hb Q (index n) φ ∂angleMeasure)) := by
  calc
    _ = ∫ t, ∫ x : Configuration, KFCausalStructuredChargeResponse.weakDensity ε h hε hh P Q n (t,x) ∂volume ∂angles := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => (configuration_integrals_eq ε h hε hh hb P Q n t).symm)
    _ = ∫ z, KFCausalStructuredChargeResponse.weakDensity ε h hε hh P Q n z ∂measure :=
      (integral_prod _ (KFCausalStructuredChargeResponse.weak_integrable ε h hε hh hb P Q n)).symm
    _ = _ := KFCausalStructuredChargeResponse.weak_integral_pairing ε h hε hh hb P Q n

include hb in
theorem diagonal_response :
    (∫ t, ∫ x : Configuration, density ε h hε hh P P n true t x ∂volume ∂angles) =
      (((-2/h)*(inner ℂ (∫ θ, inputOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
        (∫ φ, momentumOrbit ε h hε hh hb P (index n) φ ∂angleMeasure)).im : ℝ) : ℂ) := by
  calc
    _ = ∫ z, KFCausalStructuredChargeResponse.weakDensity ε h hε hh P P n z ∂measure :=
      (reduced_iterated_pairing ε h hε hh hb P P n).trans
        (KFCausalStructuredChargeResponse.weak_integral_pairing ε h hε hh hb P P n).symm
    _ = _ := KFCausalStructuredChargeResponse.diagonal_response ε h hε hh hb P n

#print axioms kernel_integrable
#print axioms kernel_integrals_eq
#print axioms weak_cross_terms
#print axioms density_integrable
#print axioms configuration_integrals_eq
#print axioms reduced_iterated_integrable
#print axioms reduced_iterated_pairing
#print axioms diagonal_response
end
end UnifiedTheory.Audit.KFCausalStructuredReducedResponse

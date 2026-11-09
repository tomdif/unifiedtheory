/- Whole-clock weak response for finite complex displaced superpositions.
Normalized packet representatives are summed before forming the response,
so every complex interference term and both independent charge angles are
retained. This covers the three growing energy factors, not a uniform
energy estimate or an evolution theorem. -/
import UnifiedTheory.Audit.KFCausalChargeResponseFubini
import UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalStructuredChargeResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState inputOrbit momentumOrbit inputOrbit_continuous momentumOrbit_continuous)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (measure pair pair_integrable pair_integral)

private theorem finite_density {m : ℕ} (f : Fin m → Hilbert) (F : Fin m → Configuration → ℂ)
    (hf : ∀ j, f j =ᵐ[volume] F j) (S : Finset (Fin m)) :
    (∑ j ∈ S, f j : Hilbert) =ᵐ[volume] fun x => ∑ j ∈ S, F j x := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℂ 2 volume
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ S, f j),hf i,ih] with x ha hx hs
    rw [ha]
    simp only [Pi.add_apply,hx,hs,Finset.sum_insert hi]

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (P Q : StructuredState) (n : Fin 3)

def inputDensity (θ : ℝ) (x : Configuration) : ℂ := ∑ j, P.coefficient j*
  KFCausalDisplacedResponseDensities.inputDensity ε (P.packet j).width h hε (P.packet j).width_pos hh
    (parameter (2*Real.pi*θ) (P.packet j).centre) (parameter (2*Real.pi*θ) (P.packet j).frequency) pointField n x

def momentumDensity (θ : ℝ) (x : Configuration) : ℂ := ∑ j, P.coefficient j*
  KFCausalDisplacedResponseDensities.momentumDensity ε (P.packet j).width h hε (P.packet j).width_pos hh
    (parameter (2*Real.pi*θ) (P.packet j).centre) (parameter (2*Real.pi*θ) (P.packet j).frequency) pointField n x

theorem input_density (θ : ℝ) : inputOrbit ε h hε hh hb P (index n) θ =ᵐ[volume]
    inputDensity ε h hε hh P n θ := by
  unfold inputOrbit inputDensity
  apply finite_density
  intro j
  filter_upwards [Lp.coeFn_smul (P.coefficient j)
    (KFCausalClockFloorDisplacedCommonDomain.factorOutput ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (parameter (2*Real.pi*θ) (P.packet j).centre)
        (parameter (2*Real.pi*θ) (P.packet j).frequency) modelDirections pointField (index n)),
    KFCausalDisplacedResponseDensities.input_factor_density ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (parameter (2*Real.pi*θ) (P.packet j).centre)
        (parameter (2*Real.pi*θ) (P.packet j).frequency) modelDirections pointField n] with x hs hd
  rw [hs]
  simp only [Pi.smul_apply,hd,smul_eq_mul]

theorem momentum_density (θ : ℝ) : momentumOrbit ε h hε hh hb P (index n) θ =ᵐ[volume]
    momentumDensity ε h hε hh P n θ := by
  unfold momentumOrbit momentumDensity
  apply finite_density
  intro j
  filter_upwards [Lp.coeFn_smul (P.coefficient j)
    (KFCausalDisplacedMomentumOrbit.factorOutput ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (parameter (2*Real.pi*θ) (P.packet j).centre)
        (parameter (2*Real.pi*θ) (P.packet j).frequency) modelDirections pointField (index n)),
    KFCausalDisplacedResponseDensities.momentum_factor_density ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (parameter (2*Real.pi*θ) (P.packet j).centre)
        (parameter (2*Real.pi*θ) (P.packet j).frequency) modelDirections pointField n] with x hs hd
  rw [hs]
  simp only [Pi.smul_apply,hd,smul_eq_mul]

include hb in
theorem input_joint_continuous : Continuous (fun z : ℝ × Configuration =>
    inputDensity ε h hε hh P n z.1 z.2) :=
  continuous_finset_sum Finset.univ (fun j _ =>
    continuous_const.mul (KFCausalDisplacedResponseDensities.input_joint_continuous ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (P.packet j).centre (P.packet j).frequency pointField n))

include hb in
theorem momentum_joint_continuous : Continuous (fun z : ℝ × Configuration =>
    momentumDensity ε h hε hh P n z.1 z.2) :=
  continuous_finset_sum Finset.univ (fun j _ =>
    continuous_const.mul (KFCausalDisplacedResponseDensities.momentum_joint_continuous ε (P.packet j).width h hε
      (P.packet j).width_pos hh hb (P.packet j).centre (P.packet j).frequency pointField n))

def weakDensity (z : (ℝ × ℝ) × Configuration) : ℂ := (Complex.I/(h:ℂ))*
  (pair (inputDensity ε h hε hh P n) (momentumDensity ε h hε hh Q n) z-
    pair (momentumDensity ε h hε hh P n) (inputDensity ε h hε hh Q n) z)

include hb in
private theorem first_pair_integrable :
    Integrable (pair (inputDensity ε h hε hh P n) (momentumDensity ε h hε hh Q n)) measure :=
  pair_integrable (inputOrbit ε h hε hh hb P (index n)) (momentumOrbit ε h hε hh hb Q (index n)) _ _
    (inputOrbit_continuous ε h hε hh hb P (index n)) (momentumOrbit_continuous ε h hε hh hb Q (index n))
    (input_joint_continuous ε h hε hh hb P n) (momentum_joint_continuous ε h hε hh hb Q n)
    (input_density ε h hε hh hb P n) (momentum_density ε h hε hh hb Q n)

include hb in
private theorem second_pair_integrable :
    Integrable (pair (momentumDensity ε h hε hh P n) (inputDensity ε h hε hh Q n)) measure :=
  pair_integrable (momentumOrbit ε h hε hh hb P (index n)) (inputOrbit ε h hε hh hb Q (index n)) _ _
    (momentumOrbit_continuous ε h hε hh hb P (index n)) (inputOrbit_continuous ε h hε hh hb Q (index n))
    (momentum_joint_continuous ε h hε hh hb P n) (input_joint_continuous ε h hε hh hb Q n)
    (momentum_density ε h hε hh hb P n) (input_density ε h hε hh hb Q n)

include hb in
theorem weak_integrable : Integrable (weakDensity ε h hε hh P Q n) measure :=
  ((first_pair_integrable ε h hε hh hb P Q n).sub
    (second_pair_integrable ε h hε hh hb P Q n)).const_mul _

include hb in
theorem weak_integral_pairing : (∫ z, weakDensity ε h hε hh P Q n z ∂measure) =
    (Complex.I/(h:ℂ))*(
      inner ℂ (∫ θ, inputOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
        (∫ φ, momentumOrbit ε h hε hh hb Q (index n) φ ∂angleMeasure)-
      inner ℂ (∫ θ, momentumOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
        (∫ φ, inputOrbit ε h hε hh hb Q (index n) φ ∂angleMeasure)) := by
  unfold weakDensity
  rw [integral_const_mul,integral_sub (first_pair_integrable ε h hε hh hb P Q n)
    (second_pair_integrable ε h hε hh hb P Q n)]
  rw [pair_integral (inputOrbit ε h hε hh hb P (index n)) (momentumOrbit ε h hε hh hb Q (index n)) _ _
    (inputOrbit_continuous ε h hε hh hb P (index n)) (momentumOrbit_continuous ε h hε hh hb Q (index n))
    (input_joint_continuous ε h hε hh hb P n) (momentum_joint_continuous ε h hε hh hb Q n)
    (input_density ε h hε hh hb P n) (momentum_density ε h hε hh hb Q n)]
  rw [pair_integral (momentumOrbit ε h hε hh hb P (index n)) (inputOrbit ε h hε hh hb Q (index n)) _ _
    (momentumOrbit_continuous ε h hε hh hb P (index n)) (inputOrbit_continuous ε h hε hh hb Q (index n))
    (momentum_joint_continuous ε h hε hh hb P n) (input_joint_continuous ε h hε hh hb Q n)
    (momentum_density ε h hε hh hb P n) (input_density ε h hε hh hb Q n)]

private theorem hermitian_real (h : ℝ) (z : ℂ) :
    (Complex.I/(h:ℂ))*(z-star z) = (((-2/h)*z.im : ℝ) : ℂ) := by
  rw [div_eq_mul_inv,← Complex.ofReal_inv]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,div_eq_mul_inv]
  ring

include hb in
theorem diagonal_response : (∫ z, weakDensity ε h hε hh P P n z ∂measure) =
    (((-2/h)*(inner ℂ (∫ θ, inputOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
      (∫ φ, momentumOrbit ε h hε hh hb P (index n) φ ∂angleMeasure)).im : ℝ) : ℂ) := by
  rw [weak_integral_pairing ε h hε hh hb P P n]
  have he : inner ℂ (∫ θ, momentumOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
      (∫ φ, inputOrbit ε h hε hh hb P (index n) φ ∂angleMeasure) =
      star (inner ℂ (∫ θ, inputOrbit ε h hε hh hb P (index n) θ ∂angleMeasure)
        (∫ φ, momentumOrbit ε h hε hh hb P (index n) φ ∂angleMeasure)) :=
    (inner_conj_symm _ _).symm
  rw [he]
  exact hermitian_real h _

#print axioms input_density
#print axioms momentum_density
#print axioms input_joint_continuous
#print axioms momentum_joint_continuous
#print axioms weak_integrable
#print axioms weak_integral_pairing
#print axioms diagonal_response
end
end UnifiedTheory.Audit.KFCausalStructuredChargeResponse

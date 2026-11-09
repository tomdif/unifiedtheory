/- Reduced polynomial clock responses after zero-charge projection.
Both independent charge angles are retained. Configuration integration
is performed first; interchange with a local clock derivative is not claimed. -/
import UnifiedTheory.Audit.KFCausalPolynomialResponsePairing
import UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse
import UnifiedTheory.Audit.KFCausalChargeResponseFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialProjectedClockResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift
  (inputOrbit momentumOrbit inputOrbit_continuous momentumOrbit_continuous)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse (meanInput meanMomentum factorRate)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

theorem pair_integrable (U V : ℝ → Hilbert) (hU : Continuous U) (hV : Continuous V) :
    Integrable (fun t : ℝ × ℝ => inner ℂ (U t.1) (V t.2)) angles := by
  have hu := (continuous_angle_memLp U hU).comp_fst angleMeasure
  have hv := (continuous_angle_memLp V hV).comp_snd angleMeasure
  apply (hu.norm.integrable_mul hv.norm).mono'
    ((hU.comp continuous_fst).inner (hV.comp continuous_snd)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => norm_inner_le_norm (U t.1) (V t.2))

theorem pair_integral (U V : ℝ → Hilbert) (hU : Continuous U) (hV : Continuous V) :
    (∫ t : ℝ × ℝ, inner ℂ (U t.1) (V t.2) ∂angles) =
      inner ℂ (∫ θ, U θ ∂angleMeasure) (∫ φ, V φ ∂angleMeasure) := by
  have hu := (continuous_angle_memLp U hU).integrable (by norm_num)
  have hv := (continuous_angle_memLp V hV).integrable (by norm_num)
  change (∫ t : ℝ × ℝ, inner ℂ (U t.1) (V t.2) ∂angleMeasure.prod angleMeasure) = _
  rw [integral_prod _ (pair_integrable U V hU hV)]
  calc
    _ = ∫ θ, inner ℂ (U θ) (∫ φ, V φ ∂angleMeasure) ∂angleMeasure := by
      exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => integral_inner hv (U θ)))
    _ = ∫ θ, star (inner ℂ (∫ φ, V φ ∂angleMeasure) (U θ)) ∂angleMeasure := by
      exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => (inner_conj_symm _ _).symm))
    _ = _ := by
      change (∫ θ, (starRingEnd ℂ) (inner ℂ (∫ φ, V φ ∂angleMeasure) (U θ)) ∂angleMeasure) = _
      rw [integral_conj,integral_inner hu,inner_conj_symm]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (P Q : Polynomial ℂ) (n : Fin 3)
local notation "qθ" θ => parameter (2*Real.pi*θ) q
local notation "kθ" θ => parameter (2*Real.pi*θ) k
local notation "u" => inputOrbit ε a h hε ha hh hb q k P (index n)
local notation "v" => inputOrbit ε a h hε ha hh hb q k Q (index n)
local notation "bu" => momentumOrbit ε a h hε ha hh hb q k P (index n)
local notation "bv" => momentumOrbit ε a h hε ha hh hb q k Q (index n)

def reducedDensity (t : ℝ × ℝ) (x : Configuration) : ℂ :=
  KFCausalPolynomialResponseIntegrability.reducedDensity ε a a h
    (clockFrequency h (kθ t.1)) (clockFrequency h (kθ t.2))
    (source h (qθ t.1) (kθ t.1)) (source h (qθ t.2) (kθ t.2))
    (amplitude h (qθ t.1) (kθ t.1)) (amplitude h (qθ t.2) (kθ t.2)) P Q pointField n x

theorem orbit_pairing (t : ℝ × ℝ) :
    (∫ x : Configuration, reducedDensity ε a h q k P Q n t x) =
      (Complex.I/(h:ℂ))*(inner ℂ (u t.1) (bv t.2)-inner ℂ (bu t.1) (v t.2)) :=
  KFCausalPolynomialResponsePairing.reduced_integral_pairing ε a a h
    (clockFrequency h (kθ t.1)) (clockFrequency h (kθ t.2))
    (source h (qθ t.1) (kθ t.1)) (source h (qθ t.2) (kθ t.2))
    (amplitude h (qθ t.1) (kθ t.1)) (amplitude h (qθ t.2) (kθ t.2)) P Q pointField n
    hε ha ha hh hb

include hε ha hh hb in
theorem iterated_integrable :
    Integrable (fun t : ℝ × ℝ => ∫ x : Configuration, reducedDensity ε a h q k P Q n t x) angles := by
  have hi := pair_integrable u bv
    (inputOrbit_continuous ε a h hε ha hh hb q k P (index n))
    (momentumOrbit_continuous ε a h hε ha hh hb q k Q (index n))
  have hj := pair_integrable bu v
    (momentumOrbit_continuous ε a h hε ha hh hb q k P (index n))
    (inputOrbit_continuous ε a h hε ha hh hb q k Q (index n))
  apply ((hi.sub hj).const_mul (Complex.I/(h:ℂ))).congr
  exact Filter.Eventually.of_forall (fun t => (orbit_pairing ε a h hε ha hh hb q k P Q n t).symm)

theorem projected_pairing :
    (∫ t : ℝ × ℝ, ∫ x : Configuration, reducedDensity ε a h q k P Q n t x ∂volume ∂angles) =
      (Complex.I/(h:ℂ))*(inner ℂ (meanInput ε a h hε ha hh hb q k P (index n))
        (meanMomentum ε a h hε ha hh hb q k Q (index n))-
        inner ℂ (meanMomentum ε a h hε ha hh hb q k P (index n))
          (meanInput ε a h hε ha hh hb q k Q (index n))) := by
  have hu := inputOrbit_continuous ε a h hε ha hh hb q k P (index n)
  have hv := inputOrbit_continuous ε a h hε ha hh hb q k Q (index n)
  have hbu := momentumOrbit_continuous ε a h hε ha hh hb q k P (index n)
  have hbv := momentumOrbit_continuous ε a h hε ha hh hb q k Q (index n)
  simp_rw [orbit_pairing ε a h hε ha hh hb q k P Q n]
  rw [integral_const_mul,integral_sub (pair_integrable u bv hu hbv) (pair_integrable bu v hbu hv),
    pair_integral u bv hu hbv,pair_integral bu v hbu hv]
  rfl

private theorem diagonal_scalar (h : ℝ) (z : ℂ) :
    (Complex.I/(h:ℂ))*(z-star z) = (((-2/h)*z.im:ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,Complex.mul_im]
  ring

omit Q in
theorem factorRate_integral :
    (∫ t : ℝ × ℝ, ∫ x : Configuration, reducedDensity ε a h q k P P n t x ∂volume ∂angles) =
      (factorRate ε a h hε ha hh hb q k P (index n):ℂ) := by
  rw [projected_pairing ε a h hε ha hh hb q k P P n,
    ← inner_conj_symm (meanMomentum ε a h hε ha hh hb q k P (index n))
      (meanInput ε a h hε ha hh hb q k P (index n))]
  exact diagonal_scalar h _

#print axioms pair_integrable
#print axioms pair_integral
#print axioms orbit_pairing
#print axioms iterated_integrable
#print axioms projected_pairing
#print axioms factorRate_integral
end
end UnifiedTheory.Audit.KFCausalPolynomialProjectedClockResponse

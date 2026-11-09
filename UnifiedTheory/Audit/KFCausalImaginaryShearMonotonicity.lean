/- The actual inverse-clock interpolation satisfies the weighted shear
monotonicity theorem. This compares its endpoints; the initial endpoint
is not asserted to have zero or nonnegative charge average. -/
import UnifiedTheory.Audit.KFCausalClockShearPositiveVariation
import UnifiedTheory.Audit.KFCausalClockFloorShearWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearMonotonicity
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (coefficient coefficient_re_positive)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)

variable (ε a p h α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
variable (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3) (b : Fin 5 → ℂ) (hh : h ≠ 0)
local notation "F" => input ε a p h α β hε ha hα hβ hw hb b
local notation "J" => shear ε a p h α β hε ha hα hβ hw hb b
local notation "K" => secondShear ε a p h α β hε ha hα hβ hw hb b
local notation "C" => coefficientOperator ε h hε hb hh

variable (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
variable (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hW hh in
theorem derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (expectation W F J) (2*∫ x, (coefficient ε h x.1).re*‖W (J t) x‖^2) t := by
  rw [← KFCausalClockShearPositiveVariation.pairing_integral C (coefficient ε h)
    (coefficientOperator_coe ε h hε hb hh)]
  exact KFCausalClockShearPositiveVariation.expectation_derivative C W (coefficient ε h) w
    (coefficientOperator_coe ε h hε hb hh) hW h hh F J (K ⟨t,ht.1.le,ht.2.le⟩) t
    (input_strong_derivative ε a p h α β hε ha hα hβ hw hb b hh t ht)
    (shear_strong_derivative ε a p h α β hε ha hα hβ hw hb b hh t ht)
    (input_shear_graph ε a p h α β hε ha hα hβ hw hb b hh ⟨t,ht.1.le,ht.2.le⟩)
    (shear_second_graph ε a p h α β hε ha hα hβ hw hb b hh ⟨t,ht.1.le,ht.2.le⟩)

include hW hh in
theorem monotone : MonotoneOn (expectation W F J) (Icc (0:ℝ) 1) :=
  KFCausalClockShearPositiveVariation.expectation_monotone C W (coefficient ε h) w
    (coefficientOperator_coe ε h hε hb hh) hW
    (fun s => (coefficient_re_positive ε h s hε hh hb).le) h hh F J K
    (input_continuous ε a p h α β hε ha hα hβ hw hb b)
    (shear_continuous ε a p h α β hε ha hα hβ hw hb b)
    (input_strong_derivative ε a p h α β hε ha hα hβ hw hb b hh)
    (shear_strong_derivative ε a p h α β hε ha hα hβ hw hb b hh)
    (input_shear_graph ε a p h α β hε ha hα hβ hw hb b hh)
    (shear_second_graph ε a p h α β hε ha hα hβ hw hb b hh)

include hW hh in
theorem endpoints : expectation W F J 0 ≤ expectation W F J 1 :=
  monotone ε a p h α β hε ha hα hβ hw hb b hh W w hW
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)

local notation "R" => KFCausalClockFloorShearWeight.root ε hε h hb hh

theorem physical_weight_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (expectation R F J) (2*∫ x, (coefficient ε h x.1).re*‖R (J t) x‖^2) t :=
  derivative ε a p h α β hε ha hα hβ hw hb b hh R
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh) t ht

theorem physical_weight_monotone : MonotoneOn (expectation R F J) (Icc (0:ℝ) 1) :=
  monotone ε a p h α β hε ha hα hβ hw hb b hh R
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh)

theorem physical_weight_endpoints : expectation R F J 0 ≤ expectation R F J 1 :=
  endpoints ε a p h α β hε ha hα hβ hw hb b hh R
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh)

#print axioms derivative
#print axioms monotone
#print axioms endpoints
#print axioms physical_weight_derivative
#print axioms physical_weight_monotone
#print axioms physical_weight_endpoints
end
end UnifiedTheory.Audit.KFCausalImaginaryShearMonotonicity

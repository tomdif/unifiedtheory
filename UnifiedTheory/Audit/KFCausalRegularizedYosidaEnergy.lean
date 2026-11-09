/- Cutoff-uniform energy control along the actual bounded homogeneous
evolution. The initial state may be any vector in the common completed
form domain. The unbounded evolution limit is not assumed or asserted. -/
import UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics
import UnifiedTheory.Audit.KFCausalRegularizedYosidaDerivative
import UnifiedTheory.Audit.KFCausalFormEnergyIdentities
import UnifiedTheory.Audit.KFCausalSchrodingerEnergyEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedYosidaEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalYosidaApproximation
open UnifiedTheory.Audit.KFCausalFormEnergyIdentities
open UnifiedTheory.Audit.KFCausalSchrodingerEnergyEstimate
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
open UnifiedTheory.Audit.KFCausalRegularizedYosida
open UnifiedTheory.Audit.KFCausalRegularizedYosidaDerivative
open UnifiedTheory.Audit.KFCausalRegularizedYosidaDynamics

theorem quadratic_eq_timeEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    quadratic (clockMap ε hε hbar coupling) (momentumMap ε hε hbar coupling) t w =
      timeEnergy ε hε hbar coupling t w := by
  rw [quadratic_eq]
  rfl

theorem lift_equation (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    referenceShift ε hε hbar coupling a t (resolventFormLift ε hε hbar coupling a t f) =
      referenceAdjoint ε hε hbar coupling f := referenceInverse_right ε hε hbar coupling a t ha _

theorem yosida_action (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (f : Hilbert) :
    homogeneousYosida ε hε hbar coupling a t f =
      a • (f-a • embedding ε hε hbar coupling 0 (resolventFormLift ε hε hbar coupling a t f)) := by
  unfold homogeneousYosida
  rw [yosida_apply,shiftedResolvent_apply,smul_sub]

def boundedEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (f : Hilbert) : ℝ :=
  expectation (homogeneousYosida ε hε hbar coupling a t) f

theorem boundedEnergy_split (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (f : Hilbert) :
    boundedEnergy ε hε hbar coupling a t f =
      a*‖f-a • embedding ε hε hbar coupling 0 (resolventFormLift ε hε hbar coupling a t f)‖^2 +
      a^2*timeEnergy ε hε hbar coupling t (resolventFormLift ε hε hbar coupling a t f) := by
  have hh := congrArg Complex.re (shiftedResolvent_variational ε hε hbar coupling a t ha f
    (resolventFormLift ε hε hbar coupling a t f))
  rw [shiftedResolvent_apply] at hh
  have hq : timeEnergy ε hε hbar coupling t (resolventFormLift ε hε hbar coupling a t f) =
      (inner ℂ (f-a • embedding ε hε hbar coupling 0 (resolventFormLift ε hε hbar coupling a t f))
        (embedding ε hε hbar coupling 0 (resolventFormLift ε hε hbar coupling a t f))).re := by
    rw [← quadratic_eq_timeEnergy,quadratic]
    exact hh
  rw [boundedEnergy,expectation,yosida_action]
  exact vector_energy_split a f _ _ hq

theorem boundedEnergy_le_form (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (w : FormSpace ε hε hbar coupling 0) :
    boundedEnergy ε hε hbar coupling a t (embedding ε hε hbar coupling 0 w) ≤
      timeEnergy ε hε hbar coupling t w := by
  rw [boundedEnergy,expectation,yosida_action,← quadratic_eq_timeEnergy]
  exact resolvent_energy_le_form _ _ _ a t ha w _ (lift_equation ε hε hbar coupling a t ha _)

theorem yosidaDerivative_energy_bounds (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (f : Hilbert) :
    0 ≤ expectation (yosidaDerivative ε hε hbar coupling a t) f ∧
      expectation (yosidaDerivative ε hε hbar coupling a t) f ≤ 2*boundedEnergy ε hε hbar coupling a t f := by
  have he := boundedEnergy_split ε hε hbar coupling a t ha f
  rw [← quadratic_eq_timeEnergy,quadratic_eq] at he
  simp only [expectation,yosidaDerivative_diagonal ε hε hbar coupling a t ha f]
  constructor
  · positivity
  · rw [he]
    have hq := mul_nonneg (sq_nonneg a)
      (sq_nonneg ‖clockMap ε hε hbar coupling (resolventFormLift ε hε hbar coupling a t f)‖)
    have hn := mul_nonneg ha.le
      (sq_nonneg ‖f-a • embedding ε hε hbar coupling 0 (resolventFormLift ε hε hbar coupling a t f)‖)
    nlinarith

def trajectoryEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : ℝ :=
  boundedEnergy ε hε hbar coupling a t (dynamics ε hε hbar coupling a ha s t f)

def trajectoryEnergyDerivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : ℝ :=
  expectation (yosidaDerivative ε hε hbar coupling a t) (dynamics ε hε hbar coupling a ha s t f)

theorem trajectoryEnergy_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    HasDerivAt (fun z => trajectoryEnergy ε hε hbar coupling a ha s z f)
      (trajectoryEnergyDerivative ε hε hbar coupling a ha s t f) t :=
  energy_derivative _ _ _ hbar t (homogeneousYosida_derivative ε hε hbar coupling a t ha)
    (homogeneousYosida_selfAdjoint ε hε hbar coupling a t ha)
    (dynamics_state_derivative ε hε hbar coupling a ha s t f)

theorem trajectoryEnergy_derivative_bounds (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    0 ≤ trajectoryEnergyDerivative ε hε hbar coupling a ha s t f ∧
      trajectoryEnergyDerivative ε hε hbar coupling a ha s t f ≤
        2*trajectoryEnergy ε hε hbar coupling a ha s t f :=
  yosidaDerivative_energy_bounds ε hε hbar coupling a t ha _

theorem trajectoryEnergy_initial (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s : ℝ) (f : Hilbert) :
    trajectoryEnergy ε hε hbar coupling a ha s s f = boundedEnergy ε hε hbar coupling a s f := by
  rw [trajectoryEnergy,dynamics_initial,ContinuousLinearMap.one_apply]

theorem trajectoryEnergy_comparison (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (hst : s ≤ t) (f : Hilbert) :
    boundedEnergy ε hε hbar coupling a s f ≤ trajectoryEnergy ε hε hbar coupling a ha s t f ∧
      trajectoryEnergy ε hε hbar coupling a ha s t f ≤
        Real.exp (2*(t-s))*boundedEnergy ε hε hbar coupling a s f := by
  have he := energy_comparison _ _ (fun z => trajectoryEnergy_derivative ε hε hbar coupling a ha s z f)
    (fun z => trajectoryEnergy_derivative_bounds ε hε hbar coupling a ha s z f) s t hst
  simpa only [trajectoryEnergy_initial] using he

theorem uniform_energy_bound (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (w : FormSpace ε hε hbar coupling 0) :
    trajectoryEnergy ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w) ≤
      Real.exp (2*|t-s|)*timeEnergy ε hε hbar coupling s w := by
  apply energy_bound_all_times _ _
    (fun z => trajectoryEnergy_derivative ε hε hbar coupling a ha s z _)
    (fun z => trajectoryEnergy_derivative_bounds ε hε hbar coupling a ha s z _)
  · rw [← quadratic_eq_timeEnergy]
    exact quadratic_nonneg _ _ s w
  · rw [trajectoryEnergy_initial]
    exact boundedEnergy_le_form ε hε hbar coupling a s ha w

theorem uniform_energy_forward (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a)
    (s t : ℝ) (hst : s ≤ t) (w : FormSpace ε hε hbar coupling 0) :
    trajectoryEnergy ε hε hbar coupling a ha s t (embedding ε hε hbar coupling 0 w) ≤
      Real.exp (2*(t-s))*timeEnergy ε hε hbar coupling s w := by
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using uniform_energy_bound ε hε hbar coupling a ha s t w

#print axioms quadratic_eq_timeEnergy
#print axioms boundedEnergy_split
#print axioms boundedEnergy_le_form
#print axioms yosidaDerivative_energy_bounds
#print axioms trajectoryEnergy_derivative
#print axioms trajectoryEnergy_derivative_bounds
#print axioms trajectoryEnergy_comparison
#print axioms uniform_energy_bound
#print axioms uniform_energy_forward

end
end UnifiedTheory.Audit.KFCausalRegularizedYosidaEnergy

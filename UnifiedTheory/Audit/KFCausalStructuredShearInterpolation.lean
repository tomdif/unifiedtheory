/- The actual imaginary-shear interpolation for every finite structured
state, with independent widths, displacements and complex amplitudes.
The initial endpoint is identified by bounded clock operators. Its charge
covariance is derived; no projected vacuum sign is assumed. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint
import UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
import UnifiedTheory.Audit.KFCausalDisplacedMatterWeakResponse
import UnifiedTheory.Audit.KFCausalDisplacedResponseDensities

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredShearInterpolation
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState Packet inputOrbit)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds (clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_compose)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed sumInput sumShear sumSecond)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint (initialOperator)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

theorem sourced_zero (ε a α β h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    C • KFCausalActualImaginaryShearCurve.input ε a p h α β hε ha hα hβ hw hb b 0 =
      initialOperator ε a p h hε hb
        (KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b) := by
  rw [KFCausalImaginaryShearInitialEndpoint.input_zero_eq,← map_smul,
    ← KFCausalClockFloorSourcedSpectral.dampedState_gaussian,
    KFCausalClockFloorSourcedClockMomentum.dampedState_eq_inverseAction]
  exact (KFCausalImaginaryShearInitialEndpoint.initialOperator_inverse ε a p h hε hb _).symm

def seed (h : ℝ) (hh : h ≠ 0) (P : Packet) (θ : ℝ) : Seed where
  a := P.width
  p := clockFrequency h (parameter θ P.frequency)
  α := groundWidth h
  β := neutralWidth h
  b := source h (parameter θ P.centre) (parameter θ P.frequency)
  ha := P.width_pos
  hα := groundWidth_positive h hh
  hβ := neutralWidth_positive h hh
  hw := neutralWidth_bound h

def amplitudeCoefficient (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (P : Packet) (θ : ℝ) : ℂ :=
  (‖trialState ε P.width h hε P.width_pos hh‖⁻¹:ℝ)*
    amplitude h (parameter θ P.centre) (parameter θ P.frequency)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (S : StructuredState)

def input (θ t : ℝ) : Hilbert := sumInput ε h hε hb (fun i => seed h hh (S.packet i) θ)
  (fun i => S.coefficient i*amplitudeCoefficient ε h hε hh (S.packet i) θ) t
def shear (θ t : ℝ) : Hilbert := sumShear ε h hε hb (fun i => seed h hh (S.packet i) θ)
  (fun i => S.coefficient i*amplitudeCoefficient ε h hε hh (S.packet i) θ) t
def second (θ : ℝ) (t : Interval) : Hilbert := sumSecond ε h hε hb
  (fun i => seed h hh (S.packet i) θ)
  (fun i => S.coefficient i*amplitudeCoefficient ε h hε hh (S.packet i) θ) t

theorem input_zero (θ : ℝ) : input ε h hε hh hb S θ 0 =
    ∑ i, S.coefficient i • initialOperator ε (S.packet i).width
      (clockFrequency h (S.packet i).frequency) h hε hb
      (state ε (S.packet i).width h hε (S.packet i).width_pos hh
        (parameter θ (S.packet i).centre) (parameter θ (S.packet i).frequency)) := by
  unfold input sumInput
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_smul]
  congr 1
  dsimp only [seed]
  rw [sourced_zero]
  have hz := KFCausalDisplacedMatterWeakResponse.normalized_eq_sourced ε (S.packet i).width h
    hε (S.packet i).width_pos hh (parameter θ (S.packet i).centre) (parameter θ (S.packet i).frequency)
    ((KFCausalClockFloorDisplacedBoostOrbit.parameter_clock θ (S.packet i).centre).trans (S.packet i).clock_zero)
  change _ = KFCausalClockFloorSourcedClockMomentum.state _ _ _ _ _ _ _ _ _
    (amplitudeCoefficient ε h hε hh (S.packet i) θ) _ _ at hz
  rw [← hz,clockFrequency_parameter]

theorem initial_charge (θ φ : ℝ) : action h hh φ (input ε h hε hh hb S θ 0) =
    input ε h hε hh hb S (θ+φ) 0 := by
  rw [input_zero,input_zero,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,← KFCausalImaginaryShearInitialEndpoint.initialOperator_charge,
    action_state,parameter_compose,parameter_compose]

theorem input_one (θ : ℝ) : input ε h hε hh hb S (2*Real.pi*θ) 1 = inputOrbit ε h hε hh hb S 7 θ := by
  unfold input
  rw [KFCausalImaginaryShearSuperposition.input_one]
  unfold inputOrbit
  apply Finset.sum_congr rfl
  intro i _
  change (S.coefficient i*amplitudeCoefficient ε h hε hh (S.packet i) (2*Real.pi*θ)) • _ =
    S.coefficient i • ((‖trialState ε (S.packet i).width h hε (S.packet i).width_pos hh‖⁻¹:ℝ) •
      (amplitude h (parameter (2*Real.pi*θ) (S.packet i).centre)
        (parameter (2*Real.pi*θ) (S.packet i).frequency) • _))
  rw [← smul_smul]
  congr 1
  unfold amplitudeCoefficient
  rw [mul_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

theorem input_graph (θ : ℝ) (t : Interval) :
    (input ε h hε hh hb S θ t,shear ε h hε hh hb S θ t) ∈ (shearMomentum h).graph :=
  KFCausalImaginaryShearSuperposition.input_graph ε h hε hb _ _ hh t

theorem shear_graph (θ : ℝ) (t : Interval) :
    (shear ε h hε hh hb S θ t,second ε h hε hh hb S θ t) ∈ (shearMomentum h).graph :=
  KFCausalImaginaryShearSuperposition.shear_graph ε h hε hb _ _ hh t

theorem input_derivative (θ t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (input ε h hε hh hb S θ) (coefficientOperator ε h hε hb hh (shear ε h hε hh hb S θ t)) t :=
  KFCausalImaginaryShearSuperposition.input_derivative ε h hε hb _ _ hh t ht

theorem shear_derivative (θ t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (shear ε h hε hh hb S θ)
      (coefficientOperator ε h hε hb hh (second ε h hε hh hb S θ ⟨t,ht.1.le,ht.2.le⟩)) t :=
  KFCausalImaginaryShearSuperposition.shear_derivative ε h hε hb _ _ hh t ht

theorem weighted_endpoints (θ : ℝ) (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) :
    (inner ℂ (W (input ε h hε hh hb S θ 0)) (W (shear ε h hε hh hb S θ 0))).re ≤
      (inner ℂ (W (input ε h hε hh hb S θ 1)) (W (shear ε h hε hh hb S θ 1))).re :=
  KFCausalImaginaryShearSuperposition.expectation_endpoints ε h hε hb _ _ hh W w hW

#print axioms sourced_zero
#print axioms input_zero
#print axioms initial_charge
#print axioms input_one
#print axioms input_graph
#print axioms shear_graph
#print axioms input_derivative
#print axioms shear_derivative
#print axioms weighted_endpoints
end
end UnifiedTheory.Audit.KFCausalStructuredShearInterpolation

/- The transported initial field and its shear vary continuously along
charge rotations. This follows from exact fixed bounded clock assembly
of the existing field paths, and yields the charge-integrated comparison.
No Hilbert-norm bound for the algebraic field operators is inferred. -/
import UnifiedTheory.Audit.KFCausalTransportedInitialAssembly
import UnifiedTheory.Audit.KFCausalIntrinsicMatterInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalTransportedChargeInitial
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalCoherentStateBasis (extend extend_seed extension_unique)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalTransportedInitialAssembly
open UnifiedTheory.Audit.KFCausalIntrinsicTransportedMatter (initialInput initialShear initial_graph)
open UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator (rotate field shear shear_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "S" => coherentSpan ε a h hε ha hh

def fieldData : S →ₗ[ℂ] Fields where
  toFun f m j := field ε a h hε ha hh hb m j 0 f
  map_add' f g := by funext m j; exact map_add _ f g
  map_smul' c f := by funext m j; exact map_smul _ c f

theorem initialInput_assembly (f : S) :
    initialInput ε a h hε ha hh hb l i f =
      assemble ε h hε hb hh l i (fun m j => field ε a h hε ha hh hb m j 0 f) := by
  have he : initialInput ε a h hε ha hh hb l i =
      (assembleL ε h hε hb hh l i).comp (fieldData ε a h hε ha hh hb) := by
    unfold initialInput
    apply extension_unique
    intro k
    change assemble ε h hε hb hh l i
      (fun m j => field ε a h hε ha hh hb m j 0 (KFCausalCoherentStateBasis.seed ε a h hε ha hh k)) = _
    simp_rw [field,extend_seed]
    change assembleL ε h hε hb hh l i (amplitudeConstant h k •
      (fun m j => KFCausalFieldShearPathGraphs.state ε h hε hb (coherentSeed a h ha hh k) (fieldWeight m j) 0)) = _
    rw [map_smul]
    exact congrArg (fun v : Hilbert => amplitudeConstant h k • v)
      (seed_initial ε h hε hb hh l i (coherentSeed a h ha hh k)).symm
  exact congrArg (fun L : S →ₗ[ℂ] Hilbert => L f) he

theorem initialShear_assembly (f : S) :
    initialShear ε a h hε ha hh hb l i f =
      assemble ε h hε hb hh l i (fun m j => shear ε a h hε ha hh hb m j 0 f) := by
  have hg := assemble_graph ε h hε hb hh l i
    (fun m j => field ε a h hε ha hh hb m j 0 f)
    (fun m j => shear ε a h hε ha hh hb m j 0 f)
    (fun m j => shear_graph ε a h hε ha hh hb m j f ⟨0,by constructor <;> norm_num⟩)
  exact (shearMomentum h).mem_graph_snd_inj' (initial_graph ε a h hε ha hh hb l i f) hg
    (initialInput_assembly ε a h hε ha hh hb l i f)

def input (f : S) (θ : ℝ) : Hilbert :=
  initialInput ε a h hε ha hh hb l i (rotate ε a h hε ha hh (2*Real.pi*θ) f)
def output (f : S) (θ : ℝ) : Hilbert :=
  initialShear ε a h hε ha hh hb l i (rotate ε a h hε ha hh (2*Real.pi*θ) f)

theorem curves_continuous (f : S) :
    Continuous (input ε a h hε ha hh hb l i f) ∧ Continuous (output ε a h hε ha hh hb l i f) := by
  have hc (m : Transverse →L[ℝ] ℝ) (j : Fin 2) :=
    KFCausalIntrinsicMatterInterpolation.curves_joint_continuous ε a h hε ha hh hb m j f
  have hp : Continuous (fun θ : ℝ => (θ,(0:ℝ))) := continuous_id.prodMk continuous_const
  constructor
  · have hu := assemble_continuous ε h hε hb hh l i
      (fun θ m j => field ε a h hε ha hh hb m j 0 (rotate ε a h hε ha hh (2*Real.pi*θ) f))
      (fun m j => by
        have hu := (hc m j).1.comp hp
        dsimp only [Function.comp_def,KFCausalIntrinsicMatterInterpolation.field] at hu
        exact hu)
    exact hu.congr (fun θ => (initialInput_assembly ε a h hε ha hh hb l i _).symm)
  · have hu := assemble_continuous ε h hε hb hh l i
      (fun θ m j => shear ε a h hε ha hh hb m j 0 (rotate ε a h hε ha hh (2*Real.pi*θ) f))
      (fun m j => by
        have hu := (hc m j).2.1.comp hp
        dsimp only [Function.comp_def,KFCausalIntrinsicMatterInterpolation.shear] at hu
        exact hu)
    exact hu.congr (fun θ => (initialShear_assembly ε a h hε ha hh hb l i _).symm)

variable (W : Hilbert →L[ℂ] Hilbert)

def expectation (f : S) (θ : ℝ) : ℝ :=
  (inner ℂ (W (input ε a h hε ha hh hb l i f θ)) (W (output ε a h hε ha hh hb l i f θ))).re

theorem expectation_continuous (f : S) : Continuous (expectation ε a h hε ha hh hb l i W f) :=
  Complex.continuous_re.comp
    ((W.continuous.comp (curves_continuous ε a h hε ha hh hb l i f).1).inner
      (W.continuous.comp (curves_continuous ε a h hε ha hh hb l i f).2))

theorem expectation_integrable (f : S) :
    Integrable (expectation ε a h hε ha hh hb l i W f) angleMeasure :=
  (continuous_angle_memLp _ (expectation_continuous ε a h hε ha hh hb l i W f)).integrable (by norm_num)

theorem actual_average_lower (w : ℝ → ℂ)
    (hW : ∀ v : Hilbert, W v =ᵐ[volume] fun x => w x.1*v x) (f : S) (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) (f:Hilbert),g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    Continuous u ∧ Continuous j ∧
      Integrable (fun θ => (inner ℂ (W (u θ)) (W (j θ))).re) angleMeasure ∧
      (∫ θ, expectation ε a h hε ha hh hb l i W f θ ∂angleMeasure) ≤
        ∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure := by
  obtain ⟨n,k,z,hf⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f f.property
  have hg' : ∀ θ, (action h hh (2*Real.pi*θ) (∑ r, z r • state ε a h hε ha hh (k r)),g θ) ∈
      (orderedExponential ε hε h).graph := by rw [← hf]; exact hg
  have he := KFCausalAveragedMatterInterpolation.actual_average_lower ε a h hε ha hh hb l i k z
    W w hW g u j hg' hu hj
  refine ⟨he.1,he.2.1,he.2.2.1,?_⟩
  apply integral_mono (expectation_integrable ε a h hε ha hh hb l i W f) he.2.2.1
  intro θ
  exact KFCausalIntrinsicTransportedMatter.actual_endpoint_lower ε a h hε ha hh hb l i W w hW
    (rotate ε a h hε ha hh (2*Real.pi*θ) f) (g θ) (u θ) (j θ) (hg θ) (hu θ) (hj θ)

#print axioms initialInput_assembly
#print axioms initialShear_assembly
#print axioms curves_continuous
#print axioms expectation_continuous
#print axioms expectation_integrable
#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalTransportedChargeInitial

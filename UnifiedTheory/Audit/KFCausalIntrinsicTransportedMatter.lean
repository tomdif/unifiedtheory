/- The transported initial field and its actual shear are intrinsic
algebraic operators on the coherent span. Their signed pairing gives a
lower bound for the original matter output without an integrated path
cost. The remaining initial pairing and terminal moment are not bounded
here by the Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalTransportedMatterInterpolation
import UnifiedTheory.Audit.KFCausalCoherentStateBasis
import UnifiedTheory.Audit.KFCausalCoherentMatterInterpolation
import UnifiedTheory.Audit.KFCausalActualMatterAbsorbedLower

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalIntrinsicTransportedMatter
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalCoherentStateBasis (extend extend_of_representation)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials (modes)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root root_coe rootValue)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "S" => coherentSpan ε a h hε ha hh

def initialInput : S →ₗ[ℂ] Hilbert := extend ε a h hε ha hh (fun k => amplitudeConstant h k • ∑ r,
  KFCausalActualTransportedField.input ε h hε hb hh (coherentSeed a h ha hh k) (modes l i r) 0)
def initialShear : S →ₗ[ℂ] Hilbert := extend ε a h hε ha hh (fun k => amplitudeConstant h k • ∑ r,
  KFCausalActualTransportedField.output ε h hε hb hh (coherentSeed a h ha hh k) (modes l i r) 0)

theorem initial_representations (f : S) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert)=∑ r, z r • state ε a h hε ha hh (k r)) :
    initialInput ε a h hε ha hh hb l i f = KFCausalTransportedMatterInterpolation.input ε h hε hb hh l i
      (fun r => coherentSeed a h ha hh (k r)) (fun r => z r*amplitudeConstant h (k r)) 0 ∧
    initialShear ε a h hε ha hh hb l i f = KFCausalTransportedMatterInterpolation.output ε h hε hb hh l i
      (fun r => coherentSeed a h ha hh (k r)) (fun r => z r*amplitudeConstant h (k r)) 0 := by
  constructor
  · unfold initialInput
    rw [extend_of_representation ε a h hε ha hh _ f k z hf]
    simp only [smul_smul,KFCausalTransportedMatterInterpolation.input]
  · unfold initialShear
    rw [extend_of_representation ε a h hε ha hh _ f k z hf]
    simp only [smul_smul,KFCausalTransportedMatterInterpolation.output]

theorem initial_graph (f : S) :
    (initialInput ε a h hε ha hh hb l i f,initialShear ε a h hε ha hh hb l i f) ∈ (shearMomentum h).graph := by
  obtain ⟨n,k,z,hf⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f f.property
  obtain ⟨hu,hj⟩ := initial_representations ε a h hε ha hh hb l i f k z hf
  rw [hu,hj]
  exact KFCausalTransportedMatterInterpolation.input_graph ε h hε hb hh l i _ _ ⟨0,by constructor <;> norm_num⟩

theorem actual_endpoint_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) (f : S) (g u j : Hilbert)
    (hg : ((f:Hilbert),g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    (inner ℂ (W (initialInput ε a h hε ha hh hb l i f))
      (W (initialShear ε a h hε ha hh hb l i f))).re ≤ (inner ℂ (W u) (W j)).re := by
  obtain ⟨n,k,z,hf⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f f.property
  have hg' : (∑ r, z r • state ε a h hε ha hh (k r),g) ∈ (orderedExponential ε hε h).graph := hf ▸ hg
  obtain ⟨eu,ej⟩ := KFCausalCoherentMatterInterpolation.endpoints_actual ε a h hε ha hh hb l i k z g u j hg' hu hj
  have he := KFCausalTransportedMatterInterpolation.endpoint_lower ε h hε hb hh l i
    (fun r => coherentSeed a h ha hh (k r)) (fun r => z r*amplitudeConstant h (k r)) W w hW
  obtain ⟨e0,e1⟩ := initial_representations ε a h hε ha hh hb l i f k z hf
  rw [e0,e1]
  change _ ≤ (inner ℂ (W u) (W j)).re
  change _ ≤ expectation W (KFCausalCoherentMatterInterpolation.field ε a h hε ha hh hb l i k z)
    (KFCausalCoherentMatterInterpolation.shear ε a h hε ha hh hb l i k z) 1 at he
  simpa only [expectation,eu,ej] using he

local notation "W" => root ε hε h hb hh

theorem actual_weak_lower (f : S) (b g jg u v : Hilbert)
    (hB : ((f:Hilbert),b) ∈ (pureMomentum ε hε h).graph)
    (hg : ((f:Hilbert),g) ∈ (orderedExponential ε hε h).graph)
    (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : ((f:Hilbert),u) ∈ (matterFactor ε hε h (fieldPower l i)).graph)
    (hv : (b,v) ∈ (matterFactor ε hε h (fieldPower l i)).graph) :
    ∃ j d : Hilbert, (jg,j) ∈ (fieldPower l i).graph ∧
      d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph ∧
      (4/ε^2)*(inner ℂ (W (initialInput ε a h hε ha hh hb l i f))
        (W (initialShear ε a h hε ha hh hb l i f))).re-
        coefficient ε h*moment ε hε d ≤ (-2/h)*(inner ℂ u v).im := by
  obtain ⟨j,d,hj,hd,hk,_,hr⟩ := KFCausalActualMatterAbsorbedLower.actual_weak_lower
    ε hε h hb hh a ha l i f f.property b g jg u v hB hg hjg hu hv
  obtain ⟨g',ht,hF⟩ := (composition_graph _ _ _ _).mp hu
  have eg : g' = g := (orderedExponential ε hε h).mem_graph_snd_inj' ht hg rfl
  have hF' : (g,u) ∈ (fieldPower l i).graph := eg ▸ hF
  have hl := actual_endpoint_lower ε a h hε ha hh hb l i W (fun s => (rootValue ε h s:ℂ))
    (root_coe ε hε h hb hh) f g u (j+(-Complex.I*(h:ℂ)) • d) hg hF' hk
  refine ⟨j,d,hj,hd,hk,?_⟩
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4/ε^2)) _).trans hr

#print axioms initial_representations
#print axioms initial_graph
#print axioms actual_endpoint_lower
#print axioms actual_weak_lower
end
end UnifiedTheory.Audit.KFCausalIntrinsicTransportedMatter

/- Identify the field-weighted interpolation endpoint with the actual
ordered matter and shear outputs for every coherent-span state. The
initial expectation and integrated derivative cost remain explicit. -/
import UnifiedTheory.Audit.KFCausalFieldShearInterpolationEstimate
import UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge
import UnifiedTheory.Audit.KFCausalCoherentSpanVacuumSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterInterpolation
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
local notation "seeds" => fun j => coherentSeed a h ha hh (k j)
local notation "coeffs" => fun j => z j*amplitudeConstant h (k j)

def field := KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i seeds coeffs
def shear := KFCausalFieldShearInterpolationEstimate.shear ε h hε hb l i seeds coeffs
def derivativeField := KFCausalFieldShearInterpolationEstimate.derivativeField ε h hε hb l i seeds coeffs

local notation "U" => field ε a h hε ha hh hb l i k z
local notation "J" => shear ε a h hε ha hh hb l i k z
local notation "D" => derivativeField ε a h hε ha hh hb l i k z

theorem endpoints_actual (g u j : Hilbert)
    (hg : (∑ r, z r • state ε a h hε ha hh (k r),g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    U 1 = u ∧ J 1 = j := by
  have ht := KFCausalImaginaryShearCoherentBridge.endpoint_ordered_graph ε a h hε ha hh hb k z
  have eg : KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb k z 1 = g :=
    (orderedExponential ε hε h).mem_graph_snd_inj' ht hg rfl
  have hF := KFCausalFieldShearInterpolationEstimate.field_graph_sum ε h hε hb l i seeds coeffs
    ⟨1,by constructor <;> norm_num⟩
  change (KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb k z 1,U 1) ∈ (fieldPower l i).graph at hF
  rw [eg] at hF
  have eu : U 1 = u := (fieldPower l i).mem_graph_snd_inj' hF hu rfl
  have hJ := KFCausalFieldShearInterpolationEstimate.shear_graph_sum ε h hε hb l i seeds coeffs hh
    ⟨1,by constructor <;> norm_num⟩
  change (U 1,J 1) ∈ (shearMomentum h).graph at hJ
  rw [eu] at hJ
  exact ⟨eu,(shearMomentum h).mem_graph_snd_inj' hJ hj rfl⟩

theorem actual_endpoint_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) (g u j : Hilbert)
    (hg : (∑ r, z r • state ε a h hε ha hh (k r),g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    expectation W U J 0-(h^2/(4*ε))*(∫ t in (0:ℝ)..1, ‖W (D t)‖^2) ≤ (inner ℂ (W u) (W j)).re := by
  have he := KFCausalFieldShearInterpolationEstimate.endpoint_comparison ε h hε hb l i seeds coeffs hh W w hW
  obtain ⟨eu,ej⟩ := endpoints_actual ε a h hε ha hh hb l i k z g u j hg hu hj
  change expectation W U J 0-(h^2/(4*ε))*(∫ t in (0:ℝ)..1, ‖W (D t)‖^2) ≤
    (inner ℂ (W (U 1)) (W (J 1))).re at he
  rwa [eu,ej] at he

theorem physical_shear_lower (g u j : Hilbert)
    (hg : (∑ r, z r • state ε a h hε ha hh (k r),g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    let W := KFCausalClockFloorShearWeight.root ε hε h hb hh
    (4/ε^2)*expectation W U J 0-(h^2/ε^3)*(∫ t in (0:ℝ)..1, ‖W (D t)‖^2) ≤
      (4/ε^2)*(inner ℂ (W u) (W j)).re := by
  dsimp only
  have he := actual_endpoint_lower ε a h hε ha hh hb l i k z
    (KFCausalClockFloorShearWeight.root ε hε h hb hh)
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh) g u j hg hu hj
  convert mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4/ε^2) using 1
  ring

include hb in
theorem coherent_actual_path (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) (g u j : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (u,j) ∈ (shearMomentum h).graph) :
    ∃ uPath jPath dPath : ℝ → Hilbert, Continuous uPath ∧ Continuous jPath ∧ Continuous dPath ∧
      uPath 1 = u ∧ jPath 1 = j ∧
      (∀ t ∈ Icc (0:ℝ) 1, (uPath t,jPath t) ∈ (shearMomentum h).graph) ∧
      IntervalIntegrable (fun t => ‖W (dPath t)‖^2) volume 0 1 ∧
      (∀ t ∈ Ioo (0:ℝ) 1, -(h^2/(4*ε))*‖W (dPath t)‖^2 ≤ deriv (expectation W uPath jPath) t) ∧
      expectation W uPath jPath 0-(h^2/(4*ε))*(∫ t in (0:ℝ)..1, ‖W (dPath t)‖^2) ≤ (inner ℂ (W u) (W j)).re := by
  obtain ⟨m,k',z',hf'⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have hg' : (∑ r, z' r • state ε a h hε ha hh (k' r),g) ∈ (orderedExponential ε hε h).graph := by
    rw [← hf']
    exact hg
  let seeds' := fun r => coherentSeed a h ha hh (k' r)
  let coeffs' := fun r => z' r*amplitudeConstant h (k' r)
  have hc := KFCausalFieldShearInterpolationEstimate.curves_continuous ε h hε hb l i seeds' coeffs'
  have he := endpoints_actual ε a h hε ha hh hb l i k' z' g u j hg' hu hj
  refine ⟨field ε a h hε ha hh hb l i k' z',shear ε a h hε ha hh hb l i k' z',
    derivativeField ε a h hε ha hh hb l i k' z',hc.1,hc.2.1,hc.2.2,he.1,he.2,?_,?_,?_,?_⟩
  · intro t ht
    exact KFCausalFieldShearInterpolationEstimate.shear_graph_sum ε h hε hb l i seeds' coeffs' hh ⟨t,ht⟩
  · exact (KFCausalFieldShearInterpolationEstimate.cost_continuous ε h hε hb l i seeds' coeffs' W).intervalIntegrable 0 1
  · intro t ht
    exact KFCausalFieldShearInterpolationEstimate.expectation_derivative_lower ε h hε hb l i seeds' coeffs' hh W w hW t ht
  · exact actual_endpoint_lower ε a h hε ha hh hb l i k' z' W w hW g u j hg' hu hj

#print axioms endpoints_actual
#print axioms actual_endpoint_lower
#print axioms physical_shear_lower
#print axioms coherent_actual_path
end
end UnifiedTheory.Audit.KFCausalCoherentMatterInterpolation

/- Charge averaging of actual matter graphs through their closed primitive
operators. The composed matter operator is not assumed closed. -/
import UnifiedTheory.Audit.KFCausalClosedGraphPathIntegral
import UnifiedTheory.Audit.KFCausalMatterHalfStepAssembly
import UnifiedTheory.Audit.KFCausalStandingChargeOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalMatterPrimitiveAverage
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_selfAdjoint)
open KFCausalPhysicalField (physicalField_selfAdjoint)
open KFCausalTransverseFieldSquare (fieldSquare_selfAdjoint)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalMatterHalfStepAssembly (fieldFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalSourcedWidthMatterSquare (matterSecond)
open KFCausalPhysicalCircleAction (action action_strong_continuous)
open KFCausalStandingChargeOperator (zeroProjection zeroProjection_integral)

def average (f : ℝ → Hilbert) : Hilbert :=
  (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, f θ

theorem average_graph (T : Hilbert →ₗ.[ℂ] Hilbert) (hT : T.IsClosed)
    (f g : ℝ → Hilbert) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, (f θ,g θ) ∈ T.graph) : (average f,average g) ∈ T.graph := by
  have hi := KFCausalClosedGraphPathIntegral.integral_graph T hT f g hf hg hfg 0 (2*Real.pi)
  exact (T.graph.restrictScalars ℝ).smul_mem (2*Real.pi)⁻¹ hi

theorem fieldFactor_closed (j : Fin 2) : (fieldFactor j).IsClosed := by
  fin_cases j
  · exact (physicalField_selfAdjoint pointField).isClosed
  · exact (fieldSquare_selfAdjoint pointField).isClosed

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "D" => inverseL ε hε
local notation "E" => longitudinalExponential ε hε h (1/2)

theorem average_inverseL (f : ℝ → Hilbert) (hf : Continuous f) :
    average (fun θ => D (f θ)) = D (average f) := by
  unfold average
  rw [ContinuousLinearMap.map_smul_of_tower,
    ← (D).intervalIntegral_comp_comm (hf.intervalIntegrable 0 (2*Real.pi))]

theorem average_action (hh : h ≠ 0) (f : Hilbert) :
    average (fun θ => action h hh θ f) = zeroProjection h hh f := by
  rw [zeroProjection_integral]
  rfl

theorem actual_average_graphs (j : Fin 2) (f g a z y : ℝ → Hilbert)
    (hf : Continuous f) (hg : Continuous g) (ha : Continuous a)
    (hz : Continuous z) (hy : Continuous y)
    (hfg : ∀ θ, (D (f θ),g θ) ∈ (E).graph)
    (hga : ∀ θ, (g θ,a θ) ∈ (fieldFactor j).graph)
    (haz : ∀ θ, (a θ,z θ) ∈ (fieldFactor j).graph)
    (hzy : ∀ θ, (z θ,y θ) ∈ (E).graph) :
    (average f,average a) ∈ (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph ∧
    (average a,D (average y)) ∈ (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph ∧
    (average f,D (average y)) ∈ (matterSecond ε h j hε).graph := by
  have he := (longitudinal_exponential_selfAdjoint ε hε h (1/2)).isClosed
  have h1 := average_graph E he (fun θ => D (f θ)) g ((D).continuous.comp hf) hg hfg
  rw [average_inverseL ε hε f hf] at h1
  have h2 := average_graph (fieldFactor j) (fieldFactor_closed j) g a hg ha hga
  have h3 := average_graph (fieldFactor j) (fieldFactor_closed j) a z ha hz haz
  have h4 := average_graph E he z y hz hy hzy
  exact ⟨KFCausalMatterHalfStepAssembly.actual_forward_graph ε hε h j _ _ _ h1 h2,
    KFCausalMatterHalfStepAssembly.actual_reverse_graph ε hε h j _ _ _ h3 h4,
    KFCausalMatterHalfStepAssembly.actual_second_graph ε hε h j _ _ _ _ _ h1 h2 h3 h4⟩

theorem actual_projected_graphs (hh : h ≠ 0) (j : Fin 2) (f : Hilbert)
    (g a z y : ℝ → Hilbert) (hg : Continuous g) (ha : Continuous a)
    (hz : Continuous z) (hy : Continuous y)
    (hfg : ∀ θ, (D (action h hh θ f),g θ) ∈ (E).graph)
    (hga : ∀ θ, (g θ,a θ) ∈ (fieldFactor j).graph)
    (haz : ∀ θ, (a θ,z θ) ∈ (fieldFactor j).graph)
    (hzy : ∀ θ, (z θ,y θ) ∈ (E).graph) :
    (zeroProjection h hh f,average a) ∈
      (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph ∧
    (average a,D (average y)) ∈
      (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph ∧
    (zeroProjection h hh f,D (average y)) ∈ (matterSecond ε h j hε).graph := by
  have hgph := actual_average_graphs ε hε h j (fun θ => action h hh θ f) g a z y
    (action_strong_continuous h hh f) hg ha hz hy hfg hga haz hzy
  rwa [average_action h hh f] at hgph

theorem actual_projected_domain (hh : h ≠ 0) (j : Fin 2) (f : Hilbert)
    (g a z y : ℝ → Hilbert) (hg : Continuous g) (ha : Continuous a)
    (hz : Continuous z) (hy : Continuous y)
    (hfg : ∀ θ, (D (action h hh θ f),g θ) ∈ (E).graph)
    (hga : ∀ θ, (g θ,a θ) ∈ (fieldFactor j).graph)
    (haz : ∀ θ, (a θ,z θ) ∈ (fieldFactor j).graph)
    (hzy : ∀ θ, (z θ,y θ) ∈ (E).graph) :
    zeroProjection h hh f ∈ (matterSecond ε h j hε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (actual_projected_graphs ε hε h hh j f g a z y hg ha hz hy hfg hga haz hzy).2.2

#print axioms average_graph
#print axioms fieldFactor_closed
#print axioms average_inverseL
#print axioms average_action
#print axioms actual_average_graphs
#print axioms actual_projected_graphs
#print axioms actual_projected_domain
end
end UnifiedTheory.Audit.KFCausalMatterPrimitiveAverage

/- Two independently charge-conjugated vacuum squares on the actual
single Gaussian. The operator at angle theta is U(-theta) Q U(theta),
with the full natural domain inherited from Q. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquare
import UnifiedTheory.Audit.KFCausalSingleGaussianCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalSingleGaussianTwoAngleSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action action_compose action_reverse)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalSingleGaussianSecondInput (state firstOutput first_graph)
open KFCausalSingleGaussianMixedSquare (original_strip secondOutput mixed_square_graph)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)

def rotatedGraph (θ : ℝ) : Submodule ℂ (Hilbert × Hilbert) :=
  (square ε hε h).graph.comap
    ((action h hh θ).toLinearMap.prodMap (action h hh θ).toLinearMap)

def squareAt (θ : ℝ) : Hilbert →ₗ.[ℂ] Hilbert := (rotatedGraph ε hε h hh θ).toLinearPMap

theorem squareAt_graph (θ : ℝ) (f g : Hilbert) :
    (f,g) ∈ (squareAt ε hε h hh θ).graph ↔
      (action h hh θ f,action h hh θ g) ∈ (square ε hε h).graph := by
  have he : (squareAt ε hε h hh θ).graph=rotatedGraph ε hε h hh θ := by
    apply Submodule.toLinearPMap_graph_eq
    intro z hz hz0
    apply (action h hh θ).injective
    change (action h hh θ z.1,action h hh θ z.2) ∈ (square ε hε h).graph at hz
    rw [hz0,map_zero] at hz
    exact ((square ε hε h).graph_fst_eq_zero_snd hz rfl).trans (map_zero _).symm
  rw [he]
  rfl

variable (a : ℝ) (ha : 0 < a) (hb : |h| ≤ ε/10)
local notation "hb₀" => original_strip ε h hε hb

def firstAt (θ : ℝ) : Hilbert := action h hh (-θ) (firstOutput ε h a hε hh ha hb₀)
def secondAt (θ φ : ℝ) : Hilbert := action h hh (-φ) (secondOutput ε h a hε hh ha hb (φ-θ))

theorem firstAt_graph (θ : ℝ) :
    (state ε h a hε hh ha,firstAt ε hε h hh a ha hb θ) ∈ (squareAt ε hε h hh θ).graph := by
  apply (squareAt_graph ε hε h hh θ _ _).mpr
  rw [KFCausalSingleGaussianCharge.action_state ε h a hε hh ha θ]
  unfold firstAt
  rw [action_compose,neg_add_cancel,KFCausalPhysicalCircleAction.action_zero]
  exact first_graph ε h a hε hh ha hb₀

theorem secondAt_graph (θ φ : ℝ) :
    (firstAt ε hε h hh a ha hb θ,secondAt ε hε h hh a ha hb θ φ) ∈
      (squareAt ε hε h hh φ).graph := by
  apply (squareAt_graph ε hε h hh φ _ _).mpr
  unfold firstAt secondAt
  rw [action_compose,action_compose,neg_add_cancel,KFCausalPhysicalCircleAction.action_zero]
  simpa only [show -θ+φ=φ-θ by ring] using mixed_square_graph ε h a hε hh ha hb (φ-θ)

theorem two_angle_graph (θ φ : ℝ) :
    (state ε h a hε hh ha,secondAt ε hε h hh a ha hb θ φ) ∈
      (composition (squareAt ε hε h hh φ) (squareAt ε hε h hh θ)).graph :=
  (composition_graph _ _ _ _).mpr ⟨firstAt ε hε h hh a ha hb θ,
    firstAt_graph ε hε h hh a ha hb θ,secondAt_graph ε hε h hh a ha hb θ φ⟩

include hb in
theorem two_angle_domain (θ φ : ℝ) :
    state ε h a hε hh ha ∈
      (composition (squareAt ε hε h hh φ) (squareAt ε hε h hh θ)).domain :=
  LinearPMap.mem_domain_of_mem_graph (two_angle_graph ε hε h hh a ha hb θ φ)

#print axioms squareAt_graph
#print axioms firstAt_graph
#print axioms secondAt_graph
#print axioms two_angle_graph
#print axioms two_angle_domain
end
end UnifiedTheory.Audit.KFCausalSingleGaussianTwoAngleSquare

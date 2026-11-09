/- Actual second vacuum action for all sourced physical Gaussians in a
sufficient smaller strip. The first and second spectral actions are
constructed; the adjoint-domain conclusion is not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianVacuumSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorSourcedClockMomentum (state dampedState dampedState_eq_inverseAction)
open KFCausalClockFloorSourcedSpectral (shiftedOutput shiftedOutput_graph)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare

theorem double_strip (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) :
    |2*h| ≤ 2*Real.pi*ε/3 := by
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

theorem original_strip (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ Real.pi*ε/3) :
    |h| ≤ 2*Real.pi*ε/3 := by
  have hp := mul_pos Real.pi_pos hε
  linarith

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)

local notation "S" => state ε a α β hε ha hα hβ hw C p b

def doubleOutput : Hilbert :=
  shiftedOutput ε a α β hε ha hα hβ hw C p b (2*h) (double_strip ε h hb)

def squareOutput : Hilbert := inverseL ε hε
  (doubleOutput ε a α β hε ha hα hβ hw C p b h hb)

theorem doubleOutput_graph :
    (inverseL ε hε S,doubleOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg := shiftedOutput_graph ε a α β hε ha hα hβ hw C p b
    (2*h) (double_strip ε h hb)
  rw [dampedState_eq_inverseAction] at hg
  have hr := (exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show (1/2:ℝ)*2=1 by norm_num] using hr

theorem squareOutput_graph :
    (S,squareOutput ε a α β hε ha hα hβ hw C p b h hb) ∈ (square ε hε h).graph :=
  (square_graph ε hε h S _).mpr
    ⟨_,doubleOutput_graph ε a α β hε ha hα hβ hw C p b h hb,rfl⟩

include hb in
theorem state_square_domain : S ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (squareOutput_graph ε a α β hε ha hα hβ hw C p b h hb)

theorem squareOutput_adjoint_graph :
    (S,squareOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (KFCausalOrderedOperatorComposition.composition
        (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).adjoint
        (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h)).graph :=
  square_adjoint_graph ε hε h (by have hp := mul_pos Real.pi_pos hε; linarith) _ _
    (squareOutput_graph ε a α β hε ha hα hβ hw C p b h hb)

#print axioms double_strip
#print axioms original_strip
#print axioms doubleOutput_graph
#print axioms squareOutput_graph
#print axioms state_square_domain
#print axioms squareOutput_adjoint_graph
end
end UnifiedTheory.Audit.KFCausalGaussianVacuumSquare

/- Actual clock and ordered momentum graphs for arbitrary complex-sourced
physical Gaussians. This removes the restriction to the older real
coherent parameter family before treating displaced charge orbits. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)
open UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative (derivative_momentum_graph)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

def profileState (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2) : Hilbert :=
  (physicalProfile_memLp C p α β hα hβ hw b g hg).toLp (physicalProfile C p α β b g)

theorem profileState_coe (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2) :
    profileState α β hα hβ hw C p b g hg =ᵐ[volume] physicalProfile C p α β b g :=
  (physicalProfile_memLp C p α β hα hβ hw b g hg).coeFn_toLp

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)

def state : Hilbert := profileState α β hα hβ hw C p b (clockFunction ε a) (clockFunction_memLp ε a hε ha)
def clockOutput : Hilbert := profileState α β hα hβ hw C p b
  (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)
def dampedState : Hilbert := profileState α β hα hβ hw C p b
  (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha)

local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "H" => clockOutput ε a α β hε ha hα hβ hw C p b
local notation "D" => dampedState ε a α β hε ha hα hβ hw C p b

theorem state_coe : S =ᵐ[volume] physicalProfile C p α β b (clockFunction ε a) :=
  profileState_coe _ _ _ _ _ _ _ _ _ _

theorem clockOutput_graph : (S,H) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [state_coe ε a α β hε ha hα hβ hw C p b,
    profileState_coe α β hα hβ hw C p b (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)]
    with x hx hy
  change H x = physicalProfile C p α β b (halfClockFunction ε a) x at hy
  rw [hy,hx]
  simp only [physicalProfile,clockMultiplier,halfClockFunction,halfWeight]
  ring

theorem dampedState_coe : D =ᵐ[volume] physicalProfile C p α β b (dampedClockFunction ε a) :=
  profileState_coe _ _ _ _ _ _ _ _ _ _

theorem dampedState_graph : (S,D) ∈ (inverseClockHalf ε).graph := by
  apply (inverseClockHalf_graph ε _ _).mpr
  filter_upwards [state_coe ε a α β hε ha hα hβ hw C p b,
    dampedState_coe ε a α β hε ha hα hβ hw C p b] with x hx hy
  rw [hy,hx]
  simp only [physicalProfile,clockMultiplier,dampedClockFunction,inverseWeight,halfWeight,Complex.ofReal_inv]
  ring

theorem dampedState_eq_inverseAction : D = inverseAction ε hε S :=
  (inverseClockHalf ε).mem_graph_snd_inj' (dampedState_graph ε a α β hε ha hα hβ hw C p b)
    ((inverseClockHalf ε).mem_graph ⟨_,inverseClockHalf_domain ε hε _⟩) rfl

def momentumOutput (h : ℝ) (v : Transverse) : Hilbert :=
  (-Complex.I*(h:ℂ)) • (physicalProfile_derivative_memLp C p α β hα hβ hw b
    (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) v).toLp
      (derivative v (physicalProfile C p α β b (dampedClockFunction ε a)))

theorem dampedState_momentum_graph (h : ℝ) (v : Transverse) :
    (D,momentumOutput ε a α β hε ha hα hβ hw C p b h v) ∈ (transverseMomentum h v).graph :=
  derivative_momentum_graph h _ v
    (physicalProfile_memLp C p α β hα hβ hw b (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha))
    (physicalProfile_derivative_memLp C p α β hα hβ hw b
      (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) v)
    (physicalProfile_transverse_differentiable _ _ _ _ _ _)

theorem state_clockMomentum_graph (h : ℝ) (v : Transverse) :
    (S,momentumOutput ε a α β hε ha hα hβ hw C p b h v) ∈ (clockMomentum ε h v).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,dampedState_graph ε a α β hε ha hα hβ hw C p b,
    dampedState_momentum_graph ε a α β hε ha hα hβ hw C p b h v⟩

theorem state_clockHalf_domain : S ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (clockOutput_graph ε a α β hε ha hα hβ hw C p b)

theorem state_clockMomentum_domain (h : ℝ) (v : Transverse) : S ∈ (clockMomentum ε h v).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h v)

#print axioms profileState_coe
#print axioms state_coe
#print axioms clockOutput_graph
#print axioms dampedState_coe
#print axioms dampedState_graph
#print axioms dampedState_eq_inverseAction
#print axioms dampedState_momentum_graph
#print axioms state_clockMomentum_graph
#print axioms state_clockHalf_domain
#print axioms state_clockMomentum_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum

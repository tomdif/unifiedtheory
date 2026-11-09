/- Extension to the closure of actual neutral packet/momentum pairs
in the product of completed Hamiltonian form spaces. Limits remain
actual pure-clock momentum pairs. No density of this closure in the
full zero-charge response domain, or evolution invariance, is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockFullBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralResponseGraphClosure
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector zeroSector_closed)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockHamiltonian

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "V" => FormSpace ε hε h hh hb 1 1 1
local notation "J" => embedding ε hε h hh hb 1 1 1
local notation "A" => energyOutput ε hε h hh hb 1 1 1

def packetPairs (t : ℝ) : Set (V t × V t) := {z |
  ∃ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ),
    z = (inputLift ε h hε hh hb N a p ha b C P 1 1 1 t,
      momentumLift ε h hε hh hb N a p ha b C P 1 1 1 t)}

def completedPairs (t : ℝ) : Set (V t × V t) := closure (packetPairs ε h hε hh hb t)
def pairEnergy (t : ℝ) (z : V t × V t) : ℝ := ‖A t z.1‖^2
def pairResponse (t : ℝ) (z : V t × V t) : ℝ := (-2/h)*(inner ℂ (A t z.1) (A t z.2)).im

theorem completedPairs_zeroSector (t : ℝ) (z : V t × V t)
    (hz : z ∈ completedPairs ε h hε hh hb t) :
    J t z.1 ∈ zeroSector h hh ∧ J t z.2 ∈ zeroSector h hh := by
  have hc : IsClosed {w : V t × V t |
      J t w.1 ∈ zeroSector h hh ∧ J t w.2 ∈ zeroSector h hh} :=
    ((zeroSector_closed h hh).preimage ((J t).continuous.comp continuous_fst)).inter
      ((zeroSector_closed h hh).preimage ((J t).continuous.comp continuous_snd))
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    J t w.1 ∈ zeroSector h hh ∧ J t w.2 ∈ zeroSector h hh}) _ hc hz
  rintro w ⟨N,a,p,ha,b,C,P,rfl⟩
  exact ⟨KFCausalNeutralMixedClockCharge.state_mem_zeroSector ε h hε hh N a p ha b C P,
    KFCausalNeutralMixedClockCharge.momentum_mem_zeroSector ε h hε hh N a p ha b C P⟩

theorem completedPairs_momentum_graph (t : ℝ) (z : V t × V t)
    (hz : z ∈ completedPairs ε h hε hh hb t) :
    (J t z.1,J t z.2) ∈ (pureMomentum ε hε h).graph := by
  have hc : IsClosed {w : V t × V t | (J t w.1,J t w.2) ∈ (pureMomentum ε hε h).graph} :=
    (pure_closed ε hε h hh).preimage
      (((J t).continuous.comp continuous_fst).prodMk ((J t).continuous.comp continuous_snd))
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    (J t w.1,J t w.2) ∈ (pureMomentum ε hε h).graph}) _ hc hz
  rintro w ⟨N,a,p,ha,b,C,P,rfl⟩
  exact lifted_momentum_graph ε h hε hh hb N a p ha b C P 1 1 1 t

theorem lower_bound_closed (t κ : ℝ) :
    IsClosed {z : V t × V t |
      -κ*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z} := by
  have hE : Continuous (pairEnergy ε h hε hh hb t) :=
    (((A t).continuous.comp continuous_fst).norm).pow 2
  have hR : Continuous (pairResponse ε h hε hh hb t) :=
    continuous_const.mul (Complex.continuous_im.comp
      (((A t).continuous.comp continuous_fst).inner ((A t).continuous.comp continuous_snd)))
  exact isClosed_le (continuous_const.mul hE) hR

theorem bound_on_completedPairs (t κ : ℝ)
    (hbound : ∀ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
      (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ),
      -κ*fullEnergy ε h hε hh hb N a p ha b C P 1 1 1 t ≤
        fullResponse ε h hε hh hb N a p ha b C P 1 1 1 t)
    (z : V t × V t) (hz : z ∈ completedPairs ε h hε hh hb t) :
    -κ*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z := by
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    -κ*pairEnergy ε h hε hh hb t w ≤ pairResponse ε h hε hh hb t w}) _
      (lower_bound_closed ε h hε hh hb t κ) hz
  rintro w ⟨N,a,p,ha,b,C,P,rfl⟩
  exact hbound N a p ha b C P

theorem exists_uniform_completed_response_bound :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (t : ℝ) (z : V t × V t),
      z ∈ completedPairs ε h hε hh hb t →
        (J t z.1,J t z.2) ∈ (pureMomentum ε hε h).graph ∧
        -κ*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z := by
  obtain ⟨κ,hκ,hbound⟩ :=
    KFCausalNeutralMixedClockFullBound.full_response_lower_exists ε h hε hh hb
  refine ⟨κ,hκ,?_⟩
  intro t z hz
  exact ⟨completedPairs_momentum_graph ε h hε hh hb t z hz,
    bound_on_completedPairs ε h hε hh hb t κ
      (fun N a p ha b C P => hbound N a p ha b C P t) z hz⟩

#print axioms completedPairs_zeroSector
#print axioms completedPairs_momentum_graph
#print axioms lower_bound_closed
#print axioms bound_on_completedPairs
#print axioms exists_uniform_completed_response_bound
end
end UnifiedTheory.Audit.KFCausalNeutralResponseGraphClosure

/- The response estimate passes to limits in both completed form norms.
The closed pure-clock graph and zero-charge sector are preserved. No
density or dynamical invariance of this explicit closure is assumed. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockFullBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPairedSpanResponseClosure
noncomputable section
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalStandingChargeOperator (zeroSector zeroSector_closed)
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanMixedClockHamiltonian

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "V" => FormSpace ε hε h hh hb 1 1 1
local notation "J" => embedding ε hε h hh hb 1 1 1
local notation "A" => energyOutput ε hε h hh hb 1 1 1

def packetPairs (t : ℝ) : Set (V t × V t) := {z |
  ∃ (a b p q : ℝ) (ha : 0 < a) (hbw : 0 < b) (c : Coefficients),
    z = (inputLift ε a b h p q hε ha hbw hh hb c 1 1 1 t,
      momentumLift ε a b h p q hε ha hbw hh hb c 1 1 1 t)}
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
  rintro w ⟨a,b,p,q,ha,hbw,c,rfl⟩
  exact ⟨KFCausalPairedSpanMixedClockDomain.state_zeroSector ε a b h p q hε ha hbw hh c,
    KFCausalPairedSpanMixedClockDomain.momentum_zeroSector ε a b h p q hε ha hbw hh c⟩

theorem completedPairs_momentum_graph (t : ℝ) (z : V t × V t)
    (hz : z ∈ completedPairs ε h hε hh hb t) :
    (J t z.1,J t z.2) ∈ (pureMomentum ε hε h).graph := by
  have hc : IsClosed {w : V t × V t | (J t w.1,J t w.2) ∈ (pureMomentum ε hε h).graph} :=
    (pure_closed ε hε h hh).preimage
      (((J t).continuous.comp continuous_fst).prodMk ((J t).continuous.comp continuous_snd))
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    (J t w.1,J t w.2) ∈ (pureMomentum ε hε h).graph}) _ hc hz
  rintro w ⟨a,b,p,q,ha,hbw,c,rfl⟩
  exact lifted_momentum_graph ε a b h p q hε ha hbw hh hb c 1 1 1 t

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
    (hbound : ∀ (a b p q : ℝ) (ha : 0 < a) (hbw : 0 < b) (c : Coefficients),
      -κ*fullEnergy ε a b h p q hε ha hbw hh hb c 1 1 1 t ≤
        fullResponse ε a b h p q hε ha hbw hh hb c 1 1 1 t)
    (z : V t × V t) (hz : z ∈ completedPairs ε h hε hh hb t) :
    -κ*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z := by
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    -κ*pairEnergy ε h hε hh hb t w ≤ pairResponse ε h hε hh hb t w}) _
      (lower_bound_closed ε h hε hh hb t κ) hz
  rintro w ⟨a,b,p,q,ha,hbw,c,rfl⟩
  exact hbound a b p q ha hbw c

theorem exists_uniform_completed_response_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
      (t : ℝ) (z : FormSpace ε hε h hh hb 1 1 1 t × FormSpace ε hε h hh hb 1 1 1 t),
      z ∈ completedPairs ε h hε hh hb t →
        (embedding ε hε h hh hb 1 1 1 t z.1,embedding ε hε h hh hb 1 1 1 t z.2) ∈
          (pureMomentum ε hε h).graph ∧
        -((C+2)/ε)*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z := by
  obtain ⟨C,hC,hbound⟩ := KFCausalPairedSpanMixedClockFullBound.exists_uniform_full_response h hh
  refine ⟨C,hC,?_⟩
  intro ε hε hb t z hz
  exact ⟨completedPairs_momentum_graph ε h hε hh hb t z hz,
    bound_on_completedPairs ε h hε hh hb t ((C+2)/ε)
      (fun a b p q ha hbw c => hbound ε a b p q hε ha hbw hb c t) z hz⟩

#print axioms completedPairs_zeroSector
#print axioms completedPairs_momentum_graph
#print axioms lower_bound_closed
#print axioms bound_on_completedPairs
#print axioms exists_uniform_completed_response_bound
end
end UnifiedTheory.Audit.KFCausalPairedSpanResponseClosure

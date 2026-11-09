/- The reciprocal response estimate extends to the closure of the actual
state/momentum pairs in both completed form norms. The extension proves
the momentum graph and zero charge, without assuming a dense core or
that the Hamiltonian evolution belongs to this closure. -/
import UnifiedTheory.Audit.KFCausalReciprocalStrongCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalResponseClosure
noncomputable section
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open KFCausalStandingChargeOperator (zeroSector zeroSector_closed)
open KFCausalFixedCommonEnergyPairing
open KFCausalReciprocalSuperpositionFactors
open KFCausalGaussianVacuumSquare (original_strip)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "V" => FormSpace ε hε h hh hb₀ 1 1 1
local notation "J" => embedding ε hε h hh hb₀ 1 1 1
local notation "A" => energyOutput ε hε h hh hb₀ 1 1 1

def inputLift (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (t : ℝ) : V t :=
  graphFormVector ε hε h hh hb₀ 1 1 1 t
    (fixedLift ε h hε hh hb₀ 1 1 1 t (state n ε h a w c hε ha hh hw)
      (state_zeroSector n ε h a w c hε ha hh hw)
      (output n ε h a w c hε ha hh hw hb₀) (output_graph n ε h a w c hε ha hh hw hb₀))

def momentumLift (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (t : ℝ) : V t :=
  graphFormVector ε hε h hh hb₀ 1 1 1 t
    (fixedLift ε h hε hh hb₀ 1 1 1 t (momentum n ε h a w c hε ha hh hw)
      (momentum_zeroSector n ε h a w c hε ha hh hw)
      (momentumOutput n ε h a w c hε ha hh hw hb₀)
      (momentumOutput_graph n ε h a w c hε ha hh hw hb₀))

theorem inputLift_embedding (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (t : ℝ) :
    J t (inputLift ε h hε hh hb n a w c ha hw t) = state n ε h a w c hε ha hh hw := rfl

theorem momentumLift_embedding (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (t : ℝ) :
    J t (momentumLift ε h hε hh hb n a w c ha hw t) = momentum n ε h a w c hε ha hh hw := rfl

def packetPairs (t : ℝ) : Set (V t × V t) := {z |
  ∃ (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ) (ha : ∀ i, 0 < a i)
    (hw : ∀ i, 1 ≤ w i),
    z = (inputLift ε h hε hh hb n a w c ha hw t,momentumLift ε h hε hh hb n a w c ha hw t)}

def completedPairs (t : ℝ) : Set (V t × V t) := closure (packetPairs ε h hε hh hb t)
def pairEnergy (t : ℝ) (z : V t × V t) : ℝ := ‖A t z.1‖^2
def pairResponse (t : ℝ) (z : V t × V t) : ℝ := (-2/h)*(inner ℂ (A t z.1) (A t z.2)).im

theorem lifted_energy (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (t : ℝ) :
    pairEnergy ε h hε hh hb t
      (inputLift ε h hε hh hb n a w c ha hw t,momentumLift ε h hε hh hb n a w c ha hw t) =
      KFCausalReciprocalSuperpositionEnergy.fullEnergy n ε h a w c hε ha hh hw hb₀ t :=
  fixedLift_energy ε h hε hh hb₀ 1 1 1 t _ (state_zeroSector n ε h a w c hε ha hh hw)
    _ (output_graph n ε h a w c hε ha hh hw hb₀)

theorem lifted_response (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (t : ℝ) :
    pairResponse ε h hε hh hb t
      (inputLift ε h hε hh hb n a w c ha hw t,momentumLift ε h hε hh hb n a w c ha hw t) =
      KFCausalReciprocalSuperpositionEnergy.fullResponse n ε h a w c hε ha hh hw hb₀ t :=
  fixedLift_response ε h hε hh hb₀ 1 1 1 t _ (state_zeroSector n ε h a w c hε ha hh hw)
    _ (output_graph n ε h a w c hε ha hh hw hb₀)
    _ (momentum_zeroSector n ε h a w c hε ha hh hw)
    _ (momentumOutput_graph n ε h a w c hε ha hh hw hb₀)

theorem completedPairs_zeroSector (t : ℝ) (z : V t × V t)
    (hz : z ∈ completedPairs ε h hε hh hb t) :
    J t z.1 ∈ zeroSector h hh ∧ J t z.2 ∈ zeroSector h hh := by
  have hc : IsClosed {w : V t × V t |
      J t w.1 ∈ zeroSector h hh ∧ J t w.2 ∈ zeroSector h hh} :=
    ((zeroSector_closed h hh).preimage ((J t).continuous.comp continuous_fst)).inter
      ((zeroSector_closed h hh).preimage ((J t).continuous.comp continuous_snd))
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    J t w.1 ∈ zeroSector h hh ∧ J t w.2 ∈ zeroSector h hh}) _ hc hz
  rintro w ⟨n,a,w,c,ha,hw,rfl⟩
  exact ⟨state_zeroSector n ε h a w c hε ha hh hw,momentum_zeroSector n ε h a w c hε ha hh hw⟩

theorem completedPairs_momentum_graph (t : ℝ) (z : V t × V t)
    (hz : z ∈ completedPairs ε h hε hh hb t) :
    (J t z.1,J t z.2) ∈ (pureMomentum ε hε h).graph := by
  have hc : IsClosed {w : V t × V t | (J t w.1,J t w.2) ∈ (pureMomentum ε hε h).graph} :=
    (pure_closed ε hε h hh).preimage
      (((J t).continuous.comp continuous_fst).prodMk ((J t).continuous.comp continuous_snd))
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    (J t w.1,J t w.2) ∈ (pureMomentum ε hε h).graph}) _ hc hz
  rintro w ⟨n,a,w,c,ha,hw,rfl⟩
  exact momentum_graph n ε h a w c hε ha hh hw

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
    (hbound : ∀ (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
      (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i),
      -κ*KFCausalReciprocalSuperpositionEnergy.fullEnergy n ε h a w c hε ha hh hw hb₀ t ≤
        KFCausalReciprocalSuperpositionEnergy.fullResponse n ε h a w c hε ha hh hw hb₀ t)
    (z : V t × V t) (hz : z ∈ completedPairs ε h hε hh hb t) :
    -κ*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z := by
  apply closure_minimal (s := packetPairs ε h hε hh hb t) (t := {w |
    -κ*pairEnergy ε h hε hh hb t w ≤ pairResponse ε h hε hh hb t w}) _
      (lower_bound_closed ε h hε hh hb t κ) hz
  rintro z ⟨n,a,w,c,ha,hw,rfl⟩
  change -κ*pairEnergy ε h hε hh hb t _ ≤ pairResponse ε h hε hh hb t _
  rw [lifted_energy,lifted_response]
  exact hbound n a w c ha hw

theorem exists_uniform_completed_response_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ)
      (z : FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t ×
        FormSpace ε hε h hh (original_strip ε h hε hb) 1 1 1 t),
      z ∈ completedPairs ε h hε hh hb t →
        (embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t z.1,
          embedding ε hε h hh (original_strip ε h hε hb) 1 1 1 t z.2) ∈ (pureMomentum ε hε h).graph ∧
        -((C+2)/ε)*pairEnergy ε h hε hh hb t z ≤ pairResponse ε h hε hh hb t z := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalSuperpositionEnergy.exists_uniform_full_response
  refine ⟨C,hC,?_⟩
  intro ε h hε hh hb t z hz
  exact ⟨completedPairs_momentum_graph ε h hε hh hb t z hz,
    bound_on_completedPairs ε h hε hh hb t ((C+2)/ε)
      (fun n a w c ha hw => hbound n ε h a w c hε ha hh hw hb t) z hz⟩

#print axioms inputLift_embedding
#print axioms momentumLift_embedding
#print axioms lifted_energy
#print axioms lifted_response
#print axioms completedPairs_zeroSector
#print axioms completedPairs_momentum_graph
#print axioms lower_bound_closed
#print axioms bound_on_completedPairs
#print axioms exists_uniform_completed_response_bound
end
end UnifiedTheory.Audit.KFCausalReciprocalResponseClosure

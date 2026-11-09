/- Actual completed Hamiltonian form lifts for joint neutral/reciprocal
superpositions, with exact energy and clock-response identities retaining
all pairs of packets. A uniform bound on this larger class is not assumed. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonian
noncomputable section
open KFCausalReciprocalNeutralSuperposition
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalFixedCommonEnergyPairing

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "f" => state n ε h a w p C b P hε ha hh hw
local notation "Bf" => momentum n ε h a w p C b P hε ha hh hw
local notation "u" => output n ε h a w p C b P hε ha hh hw hb
local notation "v" => momentumOutput n ε h a w p C b P hε ha hh hw hb
local notation "V" => FormSpace ε hε h hh hb mass2 quartic vacuum t
local notation "J" => embedding ε hε h hh hb mass2 quartic vacuum t
local notation "A" => energyOutput ε hε h hh hb mass2 quartic vacuum t

def inputLift : V := graphFormVector ε hε h hh hb mass2 quartic vacuum t
  (fixedLift ε h hε hh hb mass2 quartic vacuum t f
    (state_zeroSector n ε h a w p C b P hε ha hh hw) u
    (output_graph n ε h a w p C b P hε ha hh hw hb))

def momentumLift : V := graphFormVector ε hε h hh hb mass2 quartic vacuum t
  (fixedLift ε h hε hh hb mass2 quartic vacuum t Bf
    (momentum_zeroSector n ε h a w p C b P hε ha hh hw) v
    (momentumOutput_graph n ε h a w p C b P hε ha hh hw hb))

local notation "L" => inputLift n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t
local notation "BL" => momentumLift n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t

theorem inputLift_embedding : J L = f := rfl
theorem momentumLift_embedding : J BL = Bf := rfl

theorem lifted_momentum_graph : (J L,J BL) ∈ (pureMomentum ε hε h).graph :=
  momentum_graph n ε h a w p C b P hε ha hh hw

def fullEnergy : ℝ := ‖A L‖^2
def fullResponse : ℝ := (-2/h)*(inner ℂ (A L) (A BL)).im

theorem energy_decomposition :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*‖u j‖^2 :=
  fixedLift_energy ε h hε hh hb mass2 quartic vacuum t f
    (state_zeroSector n ε h a w p C b P hε ha hh hw) u
    (output_graph n ε h a w p C b P hε ha hh hw hb)

theorem response_decomposition :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*((-2/h)*(inner ℂ (u j) (v j)).im) :=
  fixedLift_response ε h hε hh hb mass2 quartic vacuum t f
    (state_zeroSector n ε h a w p C b P hε ha hh hw) u
    (output_graph n ε h a w p C b P hε ha hh hw hb) Bf
    (momentum_zeroSector n ε h a w p C b P hε ha hh hw) v
    (momentumOutput_graph n ε h a w p C b P hε ha hh hw hb)

theorem energy_interference :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*
        (∑ i : Fin n, ∑ k : Fin n, inner ℂ
          (KFCausalReciprocalNeutralPackets.output ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i) hb j)
          (KFCausalReciprocalNeutralPackets.output ε (a k) h (w k) hε (ha k) hh (hw k) (C k) (p k) (b k) (P k) hb j)).re := by
  rw [energy_decomposition]
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (u j),output,KFCausalNeutralFinitePairing.sum_inner_pairs]
  rfl

theorem response_interference :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      ∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*((-2/h)*
        (∑ i : Fin n, ∑ k : Fin n, inner ℂ
          (KFCausalReciprocalNeutralPackets.output ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i) hb j)
          (KFCausalReciprocalNeutralPackets.momentumOutput ε (a k) h (w k) hε (ha k) hh (hw k) (C k) (p k) (b k) (P k) hb j)).im) := by
  rw [response_decomposition]
  simp only [output,momentumOutput,KFCausalNeutralFinitePairing.sum_inner_pairs]

#print axioms inputLift_embedding
#print axioms momentumLift_embedding
#print axioms lifted_momentum_graph
#print axioms energy_decomposition
#print axioms response_decomposition
#print axioms energy_interference
#print axioms response_interference
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonian

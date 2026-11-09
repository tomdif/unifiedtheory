/- Actual kinetic responses and exact Hamiltonian decompositions for the
finite neutral/reciprocal family. These retain all coherent cross terms;
the clock-output composition and potential estimates are separate. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport
import UnifiedTheory.Audit.KFCausalReciprocalSuperpositionEnergy
import UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralKineticResponse
noncomputable section
open KFCausalReciprocalNeutralSuperposition
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight energyWeight_norm_square)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalReciprocalNeutralPositiveEnergy (potentialEnergy)
open KFCausalReciprocalNeutralPotentialTransport (potentialResponse)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "f" => state n ε h a w p C b P hε ha hh hw
local notation "Bf" => momentum n ε h a w p C b P hε ha hh hw
local notation "u" => output n ε h a w p C b P hε ha hh hw hb
local notation "v" => momentumOutput n ε h a w p C b P hε ha hh hw hb

def factorEnergy (j : Fin 8) : ℝ := ‖u j‖^2
def factorRate (j : Fin 8) : ℝ := (-2/h)*(inner ℂ (u j) (v j)).im
local notation "E" => factorEnergy n ε h a w p C b P hε ha hh hw hb
local notation "R" => factorRate n ε h a w p C b P hε ha hh hw hb

def clockKineticEnergy (t : ℝ) : ℝ :=
  (E 0+E 1+E 2)/2+Real.exp (2*t)*(E 3+E 4)/2
def clockKineticResponse (t : ℝ) : ℝ :=
  (R 0+R 1+R 2)/2+Real.exp (2*t)*(R 3+R 4)/2

theorem kinetic_response (i : Fin 4) : R (kineticIndex i) =
    KFCausalClockFloorPureClockKineticResponse.response ε hε (u (kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    f _ Bf _
  · have hg := output_graph n ε h a w p C b P hε ha hh hw hb (kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph n ε h a w p C b P hε ha hh hw
  · have hg := momentumOutput_graph n ε h a w p C b P hε ha hh hw hb (kineticIndex i)
    fin_cases i <;> exact hg

theorem kinetic_bounds (i : Fin 4) : 0 ≤ R (kineticIndex i) ∧
    R (kineticIndex i) ≤ (1/(4*ε))*E (kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (u (kineticIndex i))

private theorem physical_sum (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (r : Fin 8 → ℝ) :
    (∑ j : Fin 8, ‖energyWeight mass2 quartic vacuum t j‖^2*r j) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) := by
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

theorem physical_energy (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7) := by
  rw [KFCausalReciprocalNeutralHamiltonian.energy_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv E

theorem physical_response (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      (R 0+R 1+R 2)/2+Real.exp (2*t)*((R 3+R 4)/2+mass2/2*R 5+quartic/4*R 6+vacuum*R 7) := by
  rw [KFCausalReciprocalNeutralHamiltonian.response_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv R

theorem clockKinetic_nonnegative (t : ℝ) :
    0 ≤ clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t := by
  unfold clockKineticEnergy factorEnergy
  positivity

theorem unit_full_energy (t : ℝ) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb 1 1 1 t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t+
        Real.exp (2*t)*potentialEnergy n ε h a w p C b P hε ha hh hw hb := by
  rw [KFCausalReciprocalNeutralHamiltonian.energy_decomposition]
  exact KFCausalReciprocalSuperpositionEnergy.unit_weights t E

theorem unit_full_response (t : ℝ) :
    fullResponse n ε h a w p C b P hε ha hh hw hb 1 1 1 t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t+
        Real.exp (2*t)*potentialResponse n ε h a w p C b P hε ha hh hw hb := by
  rw [KFCausalReciprocalNeutralHamiltonian.response_decomposition,
    KFCausalReciprocalSuperpositionEnergy.unit_weights]
  unfold clockKineticResponse potentialResponse factorRate
  norm_num [Complex.add_im,Complex.div_im]
  ring

#print axioms kinetic_response
#print axioms kinetic_bounds
#print axioms physical_energy
#print axioms physical_response
#print axioms clockKinetic_nonnegative
#print axioms unit_full_energy
#print axioms unit_full_response
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralKineticResponse

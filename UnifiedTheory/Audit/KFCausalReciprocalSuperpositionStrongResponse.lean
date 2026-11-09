/- The finite-superposition response estimate is an actual strong
Hamiltonian pairing. Both the state and its actual clock momentum have
proved operator domains; no commutator or evolution premise is used. -/
import UnifiedTheory.Audit.KFCausalReciprocalSuperpositionEnergy
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentumStrongHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalSuperpositionStrongResponse
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSuperpositionFactors
open KFCausalReciprocalSuperpositionEnergy (fullEnergy fullResponse)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalFixedCommonEnergyPairing (fixedLift)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalGaussianVacuumSquare (original_strip)

variable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "f" => state n ε h a w c hε ha hh hw
local notation "b" => momentum n ε h a w c hε ha hh hw
local notation "u" => output n ε h a w c hε ha hh hw hb₀
local notation "v" => momentumOutput n ε h a w c hε ha hh hw hb₀
local notation "hf" => state_zeroSector n ε h a w c hε ha hh hw
local notation "hu" => output_graph n ε h a w c hε ha hh hw hb₀

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  ∑ i, c i • KFCausalReciprocalGaussianStrongHamiltonian.output ε (a i) h (w i)
    hε (ha i) hh (hw i) hb mass2 quartic vacuum t

theorem hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (f,hamiltonianOutput n ε h a w c hε ha hh hw hb mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  KFCausalReciprocalGaussianStrongHamiltonian.finite_sum_graph ε h hε hh hb n a w ha hw c mass2 quartic vacuum t

theorem hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    f ∈ (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph n ε h a w c hε ha hh hw hb mass2 quartic vacuum t)

theorem hamiltonian_action (mass2 quartic vacuum t : ℝ) :
    hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t
      ⟨f,hamiltonian_domain n ε h a w c hε ha hh hw hb mass2 quartic vacuum t⟩ =
        hamiltonianOutput n ε h a w c hε ha hh hw hb mass2 quartic vacuum t := by
  exact (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).mem_graph_snd_inj'
    ((hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).mem_graph
      ⟨f,hamiltonian_domain n ε h a w c hε ha hh hw hb mass2 quartic vacuum t⟩)
    (hamiltonian_graph n ε h a w c hε ha hh hw hb mass2 quartic vacuum t) rfl

theorem momentum_hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    b ∈ (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).domain :=
  KFCausalReciprocalGaussianMomentumStrongHamiltonian.finite_sum_domain ε h hε hh hb n a w ha hw c mass2 quartic vacuum t

theorem factor_pairing (mass2 quartic vacuum t : ℝ) (g : Hilbert) (hg : g ∈ zeroSector h hh)
    (z : Fin 8 → Hilbert) (hz : ∀ j, (g,z j) ∈ (energyFactor ε hε h modelDirections pointField j).graph) :
    (∑ j : Fin 8, inner ℂ (energyWeight mass2 quartic vacuum t j • u j)
      (energyWeight mass2 quartic vacuum t j • z j)) =
        inner ℂ (hamiltonianOutput n ε h a w c hε ha hh hw hb mass2 quartic vacuum t) g := by
  have hp := (KFCausalClockFloorAveragedHamiltonian.hamiltonian_domain_characterization ε hε h hh hb₀
    mass2 quartic vacuum t (fixedLift ε h hε hh hb₀ mass2 quartic vacuum t f hf u hu)
      (hamiltonianOutput n ε h a w c hε ha hh hw hb mass2 quartic vacuum t)).mp
        ⟨hamiltonian_domain n ε h a w c hε ha hh hw hb mass2 quartic vacuum t,
          hamiltonian_action n ε h a w c hε ha hh hw hb mass2 quartic vacuum t⟩
        (fixedLift ε h hε hh hb₀ mass2 quartic vacuum t g hg z hz)
  exact (KFCausalFixedCommonEnergyPairing.fixedLift_pairing ε h hε hh hb₀
    mass2 quartic vacuum t f hf u hu g hg z hz).symm.trans hp

theorem energy_identity (t : ℝ) : fullEnergy n ε h a w c hε ha hh hw hb₀ t =
    (inner ℂ (hamiltonianOutput n ε h a w c hε ha hh hw hb 1 1 1 t) f).re := by
  have hp := congrArg Complex.re (factor_pairing n ε h a w c hε ha hh hw hb 1 1 1 t f hf u hu)
  have hr (x : Hilbert) : (inner ℂ x x).re = ‖x‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Complex.re_sum,hr,norm_smul,mul_pow] using hp

theorem response_identity (t : ℝ) : fullResponse n ε h a w c hε ha hh hw hb₀ t =
    (-2/h)*(inner ℂ (hamiltonianOutput n ε h a w c hε ha hh hw hb 1 1 1 t) b).im := by
  have hp := congrArg (fun z : ℂ => (-2/h)*z.im)
    (factor_pairing n ε h a w c hε ha hh hw hb 1 1 1 t b
      (momentum_zeroSector n ε h a w c hε ha hh hw) v
      (momentumOutput_graph n ε h a w c hε ha hh hw hb₀))
  simp only [Complex.im_sum,Finset.mul_sum,KFCausalFullMomentumRateDecomposition.weighted_inner_im] at hp
  refine Eq.trans ?_ hp
  unfold fullResponse factorRate
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exists_uniform_strong_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      let ψ := state n ε h a w c hε ha hh hw;
      let Bψ := momentum n ε h a w c hε ha hh hw;
      let Hψ := hamiltonian ε hε h hh (original_strip ε h hε hb) 1 1 1 t
        ⟨ψ,hamiltonian_domain n ε h a w c hε ha hh hw hb 1 1 1 t⟩;
      -((C+2)/ε)*(inner ℂ Hψ ψ).re ≤ (-2/h)*(inner ℂ Hψ Bψ).im := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalSuperpositionEnergy.exists_uniform_full_response
  refine ⟨C,hC,?_⟩
  intro n ε h a w c hε ha hh hw hb t
  dsimp only
  rw [hamiltonian_action n ε h a w c hε ha hh hw hb]
  have hi := hbound n ε h a w c hε ha hh hw hb t
  rwa [energy_identity n ε h a w c hε ha hh hw hb,
    response_identity n ε h a w c hε ha hh hw hb] at hi

#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms hamiltonian_action
#print axioms momentum_hamiltonian_domain
#print axioms factor_pairing
#print axioms energy_identity
#print axioms response_identity
#print axioms exists_uniform_strong_response
end
end UnifiedTheory.Audit.KFCausalReciprocalSuperpositionStrongResponse

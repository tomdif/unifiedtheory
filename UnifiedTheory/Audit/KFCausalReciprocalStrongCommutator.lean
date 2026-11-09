/- Both operator compositions H_t B and B H_t are now defined on each
finite reciprocal superposition. The actual commutator expectation equals
the proved strong response; no evolution regularity is asserted. -/
import UnifiedTheory.Audit.KFCausalReciprocalHamiltonianPureDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalStrongCommutator
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalSelfAdjointCoreWeakGraph (graph_iff_weak)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian hamiltonian_selfAdjoint)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalSuperpositionFactors (state momentum momentum_graph)
open KFCausalReciprocalSuperpositionStrongResponse
  (hamiltonianOutput hamiltonian_graph hamiltonian_domain hamiltonian_action momentum_hamiltonian_domain)

theorem commutator_response (H B : Hilbert →ₗ.[ℂ] Hilbert) (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B)
    (ψ Hψ Bψ HBψ BHψ : Hilbert) (h : ℝ)
    (hHψ : (ψ,Hψ) ∈ H.graph) (hBψ : (ψ,Bψ) ∈ B.graph)
    (hHB : (Bψ,HBψ) ∈ H.graph) (hBH : (Hψ,BHψ) ∈ B.graph) :
    ((Complex.I/(h:ℂ))*inner ℂ ψ (HBψ-BHψ)).re = (-2/h)*(inner ℂ Hψ Bψ).im := by
  have h1 := (graph_iff_weak H hH Bψ HBψ).mp hHB ψ Hψ hHψ
  have h2 := (graph_iff_weak B hB Hψ BHψ).mp hBH ψ Bψ hBψ
  rw [inner_sub_right,← h1,← h2]
  have hc : Complex.I/(h:ℂ) = ((1/h:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [hc]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,Complex.sub_im]
  have hs := inner_im_symm (𝕜 := ℂ) Bψ Hψ
  simp only [RCLike.im_eq_complex_im] at hs
  rw [hs]
  ring

variable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "B" => pureMomentum ε hε h
local notation "H" => hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t
local notation "ψ" => state n ε h a w c hε ha hh hw
local notation "Bψ" => momentum n ε h a w c hε ha hh hw
local notation "Hψ" => hamiltonianOutput n ε h a w c hε ha hh hw hb mass2 quartic vacuum t

def momentumAfterHamiltonian : Hilbert := B ⟨Hψ,
  KFCausalReciprocalHamiltonianPureDomain.finite_output_domain ε h hε hh hb n a w c ha hw mass2 quartic vacuum t⟩
def hamiltonianAfterMomentum : Hilbert := H ⟨Bψ,
  momentum_hamiltonian_domain n ε h a w c hε ha hh hw hb mass2 quartic vacuum t⟩
def commutator : Hilbert := hamiltonianAfterMomentum n ε h a w c hε ha hh hw hb mass2 quartic vacuum t-
  momentumAfterHamiltonian n ε h a w c hε ha hh hw hb mass2 quartic vacuum t

theorem momentum_after_graph :
    (Hψ,momentumAfterHamiltonian n ε h a w c hε ha hh hw hb mass2 quartic vacuum t) ∈ (B).graph :=
  (B).mem_graph ⟨Hψ,KFCausalReciprocalHamiltonianPureDomain.finite_output_domain ε h hε hh hb
    n a w c ha hw mass2 quartic vacuum t⟩

theorem hamiltonian_after_graph :
    (Bψ,hamiltonianAfterMomentum n ε h a w c hε ha hh hw hb mass2 quartic vacuum t) ∈ (H).graph :=
  (H).mem_graph ⟨Bψ,momentum_hamiltonian_domain n ε h a w c hε ha hh hw hb mass2 quartic vacuum t⟩

theorem expectation_identity :
    ((Complex.I/(h:ℂ))*inner ℂ ψ (commutator n ε h a w c hε ha hh hw hb mass2 quartic vacuum t)).re =
      (-2/h)*(inner ℂ Hψ Bψ).im :=
  commutator_response H B (hamiltonian_selfAdjoint ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t)
    (pure_selfAdjoint ε hε h hh) ψ Hψ Bψ _ _ h
    (hamiltonian_graph n ε h a w c hε ha hh hw hb mass2 quartic vacuum t)
    (momentum_graph n ε h a w c hε ha hh hw)
    (hamiltonian_after_graph n ε h a w c hε ha hh hw hb mass2 quartic vacuum t)
    (momentum_after_graph n ε h a w c hε ha hh hw hb mass2 quartic vacuum t)

theorem exists_uniform_commutator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      -((C+2)/ε)*(inner ℂ (hamiltonianOutput n ε h a w c hε ha hh hw hb 1 1 1 t)
        (state n ε h a w c hε ha hh hw)).re ≤
      ((Complex.I/(h:ℂ))*inner ℂ (state n ε h a w c hε ha hh hw)
        (commutator n ε h a w c hε ha hh hw hb 1 1 1 t)).re := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalSuperpositionStrongResponse.exists_uniform_strong_response
  refine ⟨C,hC,?_⟩
  intro n ε h a w c hε ha hh hw hb t
  rw [expectation_identity n ε h a w c hε ha hh hw hb]
  have hi := hbound n ε h a w c hε ha hh hw hb t
  dsimp only at hi
  rwa [hamiltonian_action n ε h a w c hε ha hh hw hb] at hi

#print axioms commutator_response
#print axioms momentum_after_graph
#print axioms hamiltonian_after_graph
#print axioms expectation_identity
#print axioms exists_uniform_commutator_bound
end
end UnifiedTheory.Audit.KFCausalReciprocalStrongCommutator

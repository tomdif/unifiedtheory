/- Completed Bose sectors for every particle number and their maximal
Hilbert direct-sum Hamiltonian, formed from the actual tensor-domain sum. -/
import UnifiedTheory.Audit.KFCausalBosonicSectorHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicFock
noncomputable section
open KFCausalClosedGraphForm
open KFCausalTensorParticleSectors (Model fromForm vacuumModel)
open KFCausalBosonicSectorHamiltonian (bosonForm)

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def sector (D : Data H K) : ℕ → Model
  | 0 => vacuumModel
  | n + 1 => fromForm (bosonForm D n)

def sectorHamiltonian (D : Data H K) (n : ℕ) :
    (sector D n).State →ₗ.[ℂ] (sector D n).State := hamiltonian (sector D n).form

theorem sector_selfAdjoint (D : Data H K) (n : ℕ) : IsSelfAdjoint (sectorHamiltonian D n) :=
  hamiltonian_selfAdjoint _

theorem vacuum_graph (D : Data H K) (c : ℂ) : (c, 0) ∈ (sectorHamiltonian D 0).graph := by
  exact KFCausalEnergyCoreClosure.core_graph (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (0 : ℂ →ₗ[ℂ] ℂ) (0 : ℂ →ₗ[ℂ] ℂ)
    Function.surjective_id.denseRange (by intro u v; simp) c

theorem sector_positive (D : Data H K) (n : ℕ) (u : (sectorHamiltonian D n).domain) :
    0 ≤ (inner ℂ (sectorHamiltonian D n u) (u : (sector D n).State)).re :=
  hamiltonian_positive _ u

abbrev BosonFock (D : Data H K) := lp (fun n => (sector D n).State) 2

def fullHamiltonian (D : Data H K) : BosonFock D →ₗ.[ℂ] BosonFock D :=
  KFCausalHilbertDirectSumHamiltonian.operator (sectorHamiltonian D)

theorem full_selfAdjoint (D : Data H K) : IsSelfAdjoint (fullHamiltonian D) :=
  KFCausalHilbertDirectSumHamiltonian.selfAdjoint _ (sector_selfAdjoint D)

theorem full_positive (D : Data H K) (u : (fullHamiltonian D).domain) :
    0 ≤ (inner ℂ (fullHamiltonian D u) (u : BosonFock D)).re :=
  KFCausalHilbertDirectSumHamiltonian.positive _ (sector_positive D) u

theorem full_graph (D : Data H K) (x y : BosonFock D) :
    (x, y) ∈ (fullHamiltonian D).graph ↔
      ∀ n, (x n, y n) ∈ (sectorHamiltonian D n).graph :=
  KFCausalHilbertDirectSumHamiltonian.graph_iff _ x y

theorem full_domain (D : Data H K) (x : BosonFock D) :
    x ∈ (fullHamiltonian D).domain ↔
      ∃ (hx : ∀ n, x n ∈ (sectorHamiltonian D n).domain),
        Memℓp (fun n => sectorHamiltonian D n ⟨x n, hx n⟩) 2 :=
  KFCausalHilbertDirectSumHamiltonian.domain_iff _ x

def vacuum (D : Data H K) : BosonFock D := lp.single 2 0 (1 : ℂ)

theorem vacuum_stationary (D : Data H K) : (vacuum D, 0) ∈ (fullHamiltonian D).graph := by
  rw [full_graph]
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [vacuum] using vacuum_graph D 1
  · simpa [vacuum, lp.single_apply, hn] using (sectorHamiltonian D n).graph.zero_mem

theorem vacuum_norm (D : Data H K) : ‖vacuum D‖ = 1 := by
  rw [vacuum, lp.norm_single (by norm_num)]
  change ‖(1 : ℂ)‖ = 1
  exact norm_one


end
end UnifiedTheory.Audit.KFCausalBosonicFock

/- The autonomous group of the actual full averaged self-adjoint Hamiltonian
preserves its natural square domain.  Its second strong derivative is the
evolved Hamiltonian square.  The physical Hamiltonian parameter is frozen;
this does not assert square-domain invariance for the nonautonomous propagator. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenEvolution
import UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenSquareEvolution
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorFrozenEvolution
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum r η : ℝ)
local notation "T" => hamiltonian ε hε h hne hb mass2 quartic vacuum r
local notation "U" => evolution ε hε h hne hb mass2 quartic vacuum r η
local notation "c" => (-Complex.I*(η:ℂ))

theorem evolution_graph (x y : Hilbert) (hxy : (x,y) ∈ (T).graph) (t : ℝ) :
    (U t x,U t y) ∈ (T).graph := by
  obtain ⟨v,hx,hy⟩ := (T).mem_graph_iff.mp hxy
  dsimp only at hx hy
  rw [← hx,← hy]
  exact (T).mem_graph_iff.mpr
    ⟨domainEvolution ε hε h hne hb mass2 quartic vacuum r η t v,
      domainEvolution_coe ε hε h hne hb mass2 quartic vacuum r η t v,
      hamiltonian_commutes ε hε h hne hb mass2 quartic vacuum r η t v⟩

theorem evolution_square_graph (x z : Hilbert)
    (hxz : (x,z) ∈ (composition T T).graph) (t : ℝ) :
    (U t x,U t z) ∈ (composition T T).graph := by
  obtain ⟨y,hxy,hyz⟩ := (composition_graph T T x z).mp hxz
  exact (composition_graph T T _ _).mpr ⟨U t y,
    evolution_graph ε hε h hne hb mass2 quartic vacuum r η x y hxy t,
    evolution_graph ε hε h hne hb mass2 quartic vacuum r η y z hyz t⟩

theorem evolution_square_domain (x : (composition T T).domain) (t : ℝ) :
    U t (x:Hilbert) ∈ (composition T T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (evolution_square_graph ε hε h hne hb mass2 quartic vacuum r η
      x ((composition T T) x) ((composition T T).mem_graph x) t)

theorem first_derivative_of_graph (x y : Hilbert) (hxy : (x,y) ∈ (T).graph) (t : ℝ) :
    HasDerivAt (fun s => U s x) (c • U t y) t := by
  obtain ⟨v,hx,hy⟩ := (T).mem_graph_iff.mp hxy
  dsimp only at hx hy
  rw [← hx,← hy]
  simpa only [hamiltonian_commutes] using
    schrodinger ε hε h hne hb mass2 quartic vacuum r η v t

theorem second_derivative_of_graph_pair (x y z : Hilbert)
    (hxy : (x,y) ∈ (T).graph) (hyz : (y,z) ∈ (T).graph) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun v => U v x) s)
      (((-(η^2):ℝ):ℂ) • U t z) t := by
  have hd : deriv (fun v => U v x) = fun s => c • U s y :=
    funext (fun s => (first_derivative_of_graph ε hε h hne hb
      mass2 quartic vacuum r η x y hxy s).deriv)
  rw [hd]
  have hc : c*c = ((-(η^2):ℝ):ℂ) := by
    rw [← pow_two,mul_pow]
    simp
  simpa only [smul_smul,hc] using
    (first_derivative_of_graph ε hε h hne hb mass2 quartic vacuum r η y z hyz t).const_smul c

theorem second_derivative_continuous (x y z : Hilbert)
    (hxy : (x,y) ∈ (T).graph) (hyz : (y,z) ∈ (T).graph) :
    Continuous (fun t => deriv (fun s => deriv (fun v => U v x) s) t) := by
  have hd : (fun t => deriv (fun s => deriv (fun v => U v x) s) t) =
      fun t => (((-(η^2):ℝ):ℂ) • U t z) :=
    funext (fun t => (second_derivative_of_graph_pair ε hε h hne hb
      mass2 quartic vacuum r η x y z hxy hyz t).deriv)
  rw [hd]
  exact (evolution_continuous ε hε h hne hb mass2 quartic vacuum r η z).const_smul _

#print axioms evolution_graph
#print axioms evolution_square_graph
#print axioms evolution_square_domain
#print axioms first_derivative_of_graph
#print axioms second_derivative_of_graph_pair
#print axioms second_derivative_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenSquareEvolution

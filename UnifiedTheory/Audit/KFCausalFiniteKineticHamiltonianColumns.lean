/- The four projected kinetic outputs of the original finite sourced
family lie in the actual interacting Hamiltonian domain. The neutral
second derivative and both inverse half-clock factors are retained. -/
import UnifiedTheory.Audit.KFCausalFiniteSecondHamiltonianColumns
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentHamiltonian
import UnifiedTheory.Audit.KFCausalIndependentRadialKineticOutputIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalFiniteKineticHamiltonianColumns
noncomputable section
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalIndependentRadialPackets (state)
open KFCausalIndependentRadialKineticOutputIdentity (kineticCombination)
open KFCausalIndependentRadialPolynomialKinetic (kineticIndex)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)

section Single
variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
  (hb : |h| ≤ ε/10) (hstrip : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "H" => hamiltonian ε hε h hh hstrip mass2 quartic vacuum t

include hb in
theorem single_inverse_domain :
    inverseL ε hε (inverseL ε hε (state ε a h wL wR C p b P hε ha hh hL hR)) ∈ (H).domain := by
  have hd := KFCausalNaturalSecondHamiltonianGraph.hamiltonian_domain ε h hε hh hstrip
    mass2 quartic vacuum t _
    (KFCausalClockWeightedIndependentHamiltonian.singleState_zeroSector
      ε h a wL wR C p b P hε hh ha hL hR hb true) _
    (KFCausalClockWeightedIndependentHamiltonian.singleComponent_graph
      ε h a wL wR C p b P hε hh ha hL hR hb true)
  have he := (KFCausalClockMixedClockGraph.clockOperator_inverse_iff ε hε _ _).mp
    (KFCausalClockWeightedIndependentHamiltonian.single_inverse_clock_graph
      ε h a wL wR C p b P hε hh ha hL hR hb)
  rwa [he] at hd

include hb in
theorem kinetic_combination_domain (i : Fin 4) :
    inverseL ε hε (inverseL ε hε
      (kineticCombination ε a h wL wR C p b P hε ha hh hL hR i)) ∈ (H).domain := by
  have hbase (Q : Polynomial ℂ) := single_inverse_domain
    ε a h wL wR C p b Q hε ha hh hL hR hb hstrip mass2 quartic vacuum t
  have hleft := KFCausalIndependentRadialMomentHamiltonian.inverse_hamiltonian_domain
    ε a h wL wR C p b P hε ha hh hL hR hb false hstrip mass2 quartic vacuum t
  have hright := KFCausalIndependentRadialMomentHamiltonian.inverse_hamiltonian_domain
    ε a h wL wR C p b P hε ha hh hL hR hb true hstrip mass2 quartic vacuum t
  fin_cases i
  · change inverseL ε hε (inverseL ε hε (_ + _)) ∈ (H).domain
    simp only [map_add,map_smul]
    exact (H).domain.add_mem ((H).domain.smul_mem _ (hbase P)) ((H).domain.smul_mem _ hleft)
  · change inverseL ε hε (inverseL ε hε (_ + _ + _)) ∈ (H).domain
    simp only [map_add,map_smul]
    exact (H).domain.add_mem
      ((H).domain.add_mem ((H).domain.smul_mem _ (hbase P)) ((H).domain.smul_mem _ hright))
      ((H).domain.smul_mem _ (hbase _))
  · exact hleft
  · exact hright
end Single

section Diagonal
variable (ε a h w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ ε/10)
local notation "hb₀" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb

theorem projected_single_eq (i : Fin 4) :
    zeroProjection h hh (KFCausalReciprocalNeutralSecondFactors.second
      ε a h w hε ha hh hw hb₀ C p b P (kineticIndex i)) =
    inverseL ε hε (inverseL ε hε
      (kineticCombination ε a h w w C p b P hε ha hh hw hw i)) := by
  have hg := KFCausalIndependentRadialKineticOutputIdentity.raw_graph
    ε a h w w C p b P hε ha hh hw hw i
  rw [KFCausalIndependentRadialPackets.state_diagonal] at hg
  have he := (component ε hε h (kineticIndex i)).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSecondFactors.second_graph ε a h w hε ha hh hw hb₀ C p b P (kineticIndex i))
    hg rfl
  dsimp only at he
  rw [he]
  exact KFCausalIndependentRadialKineticOutputIdentity.projected_raw ε a h w w C p b P hε ha hh hw hw i

theorem projected_single_domain (mass2 quartic vacuum t : ℝ) (i : Fin 4) :
    zeroProjection h hh (KFCausalReciprocalNeutralSecondFactors.second
      ε a h w hε ha hh hw hb₀ C p b P (kineticIndex i)) ∈
      (hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t).domain := by
  rw [projected_single_eq ε a h w C p b P hε ha hh hw hb i]
  exact kinetic_combination_domain ε a h w w C p b P hε ha hh hw hw hb
    (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t i
end Diagonal

section Finite
variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ j, 0 < a j)
  (hh : h ≠ 0) (hw : ∀ j, 1 ≤ w j) (hb : |h| ≤ ε/10)

theorem projected_finite_eq (i : Fin 4) :
    zeroProjection h hh (KFCausalFiniteSecondHamiltonianColumns.second
      n ε h a w p C b P hε ha hh hw hb (kineticIndex i)) =
    ∑ j, inverseL ε hε (inverseL ε hε
      (kineticCombination ε (a j) h (w j) (w j) (C j) (p j) (b j) (P j)
        hε (ha j) hh (hw j) (hw j) i)) := by
  simp only [KFCausalFiniteSecondHamiltonianColumns.second,
    KFCausalReciprocalNeutralStrongHamiltonian.seconds,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact projected_single_eq ε (a j) h (w j) (C j) (p j) (b j) (P j) hε (ha j) hh (hw j) hb i

theorem projected_finite_domain (mass2 quartic vacuum t : ℝ) (i : Fin 4) :
    zeroProjection h hh (KFCausalFiniteSecondHamiltonianColumns.second
      n ε h a w p C b P hε ha hh hw hb (kineticIndex i)) ∈
      (hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t).domain := by
  rw [projected_finite_eq]
  apply Submodule.sum_mem
  intro j _
  exact kinetic_combination_domain ε (a j) h (w j) (w j) (C j) (p j) (b j) (P j)
    hε (ha j) hh (hw j) (hw j) hb (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t i
end Finite

#print axioms single_inverse_domain
#print axioms kinetic_combination_domain
#print axioms projected_single_eq
#print axioms projected_single_domain
#print axioms projected_finite_eq
#print axioms projected_finite_domain
end
end UnifiedTheory.Audit.KFCausalFiniteKineticHamiltonianColumns

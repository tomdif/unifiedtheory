/- The actual maximal static Hamiltonian output of every original finite
sourced packet lies in the original ordered-exponential domain. Both
operators and the intermediate vector are identified, not merely a formal
differential expression. No mixed relative bound or evolved-domain claim
is made here. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrderedStaticPacket
import UnifiedTheory.Audit.KFCausalClockFloorStaticOperator
import UnifiedTheory.Audit.KFCausalClockFloorStaticGrowingDecomposition
import UnifiedTheory.Audit.KFCausalFiniteGrowingHamiltonianOutput

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteOrderedStaticOutput
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroProjection zeroProjection_fixes)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteSecondHamiltonianColumns (second)
open KFCausalFiniteHamiltonianSquare (firstOutput)
open KFCausalFiniteGrowingHamiltonianOutput (growingOutput)
open KFCausalFiniteHamiltonianTimeDerivative (coefficient coefficientDerivative outputDerivative)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalOrderedOperatorComposition (composition composition_graph)

private theorem coefficient_static (m g κ : ℝ) (j : Fin 8) :
    coefficient m g κ 0 j-(1/2:ℂ)*coefficientDerivative m g κ 0 j =
      if j.val < 3 then (1/2:ℂ) else 0 := by
  by_cases hj : j.val < 3
  · simp only [coefficientDerivative,hj,ite_true,mul_zero,sub_zero]
    rcases (show j=0 ∨ j=1 ∨ j=2 from by omega) with rfl | rfl | rfl
    all_goals change star ((Real.sqrt (1/2):ℝ):ℂ)*((Real.sqrt (1/2):ℝ):ℂ)=(1/2:ℂ)
    all_goals rw [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,← sq,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
    all_goals norm_num
  · simp only [coefficientDerivative,hj,ite_false]
    ring

private theorem static_sum (m g κ : ℝ) (Z : Fin 8 → Hilbert) :
    (∑ j, coefficient m g κ 0 j • Z j)-
      (2:ℝ)⁻¹ • (∑ j,coefficientDerivative m g κ 0 j • Z j) =
    (1/2:ℂ) • Z 0+(1/2:ℂ) • Z 1+(1/2:ℂ) • Z 2 := by
  rw [← Complex.coe_smul]
  simp only [Complex.ofReal_inv,Complex.ofReal_ofNat,Finset.smul_sum,smul_smul,
    ← Finset.sum_sub_distrib,← sub_smul,show (2:ℂ)⁻¹=1/2 by norm_num,
    coefficient_static]
  simp [Fin.sum_univ_succ,add_assoc]

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i,0<a i)
  (hh : h ≠ 0) (hw : ∀ i,1≤w i) (hb : |h|≤ε/10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Q" => KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h
local notation "Z" => fun j => zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb j)

def staticOutput : Hilbert := ∑ i,
  KFCausalClockFloorOrderedStaticPacket.staticInput
    ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i) hε (ha i) hh (hw i) (hw i) hb

def orderedOutput : Hilbert := ∑ i,
  KFCausalClockFloorOrderedStaticPacket.orderedOutput
    ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i) hε (ha i) hh (hw i) (hw i) hb

theorem static_zeroSector :
    staticOutput n ε h a w p C b P hε ha hh hw hb ∈
      KFCausalStandingChargeOperator.zeroSector h hh := by
  apply Submodule.sum_mem
  intro i _
  unfold KFCausalClockFloorOrderedStaticPacket.staticInput
    KFCausalClockFloorOrderedStaticPacket.combination
  dsimp only
  repeat' apply Submodule.add_mem
  all_goals apply Submodule.smul_mem
  all_goals apply KFCausalIndependentRadialMomentClock.weightedState_zeroSector

theorem projected_clock_eq : Z 0 = ∑ i,
    KFCausalClockWeightedIndependentHamiltonian.singleState
      ε h (a i) (w i) (w i) (C i) (p i) (b i) (P i) hε hh (ha i) (hw i) (hw i) hb false := by
  dsimp only
  rw [KFCausalFiniteSecondHamiltonianColumns.clock_second_eq,
    zeroProjection_fixes h hh _
      (KFCausalClockWeightedOriginalHamiltonian.state_zeroSector ε h hε hh hb n a w p C b P ha hw false)]
  unfold KFCausalClockWeightedOriginalHamiltonian.state
  apply Finset.sum_congr rfl
  intro i _
  unfold KFCausalClockWeightedOriginalHamiltonian.singleState
    KFCausalClockWeightedIndependentHamiltonian.singleState
  rw [KFCausalIndependentRadialPackets.state_diagonal]
  rfl

theorem static_output_eq : staticOutput n ε h a w p C b P hε ha hh hw hb =
    (1/2:ℂ) • Z 0+(1/2:ℂ) • Z 1+(1/2:ℂ) • Z 2 := by
  rw [projected_clock_eq]
  have h1 := KFCausalFiniteKineticHamiltonianColumns.projected_finite_eq n ε h a w p C b P hε ha hh hw hb 0
  have h2 := KFCausalFiniteKineticHamiltonianColumns.projected_finite_eq n ε h a w p C b P hε ha hh hw hb 1
  change Z 1=_ at h1
  change Z 2=_ at h2
  rw [h1,h2]
  simp only [staticOutput,KFCausalClockFloorOrderedStaticPacket.static_input_eq,
    map_add,smul_add,Finset.sum_add_distrib,Finset.smul_sum]
  module

theorem first_sub_growing_eq (m g κ : ℝ) :
    firstOutput n ε h a w p C b P hε ha hh hw hb m g κ 0-
      growingOutput n ε h a w p C b P hε ha hh hw hb m g κ =
        staticOutput n ε h a w p C b P hε ha hh hw hb := by
  rw [static_output_eq]
  unfold firstOutput growingOutput outputDerivative
  rw [KFCausalFiniteSecondHamiltonianColumns.hamiltonianOutput_sum]
  exact static_sum m g κ Z

theorem static_graph : (ψ,staticOutput n ε h a w p C b P hε ha hh hw hb) ∈ (T).graph := by
  have hg := KFCausalClockFloorStaticGrowingDecomposition.static_graph
    ε hε h hh (hamiltonian_strip ε h hε hb) 0 0 0 0 _ _ _
    (KFCausalFiniteHamiltonianSquare.first_graph n ε h a w p C b P hε ha hh hw hb 0 0 0 0)
    (KFCausalFiniteGrowingHamiltonianOutput.growing_graph n ε h a w p C b P hε ha hh hw hb 0 0 0)
  simpa only [mul_zero,Real.exp_zero,one_smul,first_sub_growing_eq] using hg

theorem ordered_graph :
    (staticOutput n ε h a w p C b P hε ha hh hw hb,
      orderedOutput n ε h a w p C b P hε ha hh hw hb) ∈ (Q).graph := by
  have hs := (Q).graph.sum_mem fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    KFCausalClockFloorOrderedStaticPacket.ordered_static_graph
      ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i) hε (ha i) hh (hw i) (hw i) hb
  simpa only [staticOutput,orderedOutput,← prod_mk_sum] using hs

theorem ordered_static_graph :
    (ψ,orderedOutput n ε h a w p C b P hε ha hh hw hb) ∈ (composition Q T).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,static_graph n ε h a w p C b P hε ha hh hw hb,
      ordered_graph n ε h a w p C b P hε ha hh hw hb⟩

include hb in
theorem ordered_static_domain : ψ ∈ (composition Q T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (ordered_static_graph n ε h a w p C b P hε ha hh hw hb)

#print axioms static_zeroSector
#print axioms projected_clock_eq
#print axioms static_output_eq
#print axioms first_sub_growing_eq
#print axioms static_graph
#print axioms ordered_graph
#print axioms ordered_static_graph
#print axioms ordered_static_domain
end
end UnifiedTheory.Audit.KFCausalFiniteOrderedStaticOutput

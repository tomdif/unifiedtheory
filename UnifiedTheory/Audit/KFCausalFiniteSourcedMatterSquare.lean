/- The original finite sourced state admits vacuum-after-matter graphs
for both actual Hamiltonian matter components, with charge averaging
and independently conjugated inner and outer operators. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterProjected
import UnifiedTheory.Audit.KFCausalFiniteSourcedMixedVacuum
import UnifiedTheory.Audit.KFCausalChargeConjugatedInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalFiniteSourcedMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFiniteSourcedMixedVacuum (widthCap width_le_cap action_state)
open KFCausalSourcedWidthMatterSquare (matterSecond)
open KFCausalSingleGaussianTwoAngleSquare (squareAt)
open KFCausalChargeConjugatedInsertion (operatorAt)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (j : Fin 2) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "S" => matterSecond ε h j hε
local notation "W" => widthCap n w
local notation "hW" => width_le_cap n w hw

def firstOutput : Hilbert := ∑ i,
  KFCausalSourcedWidthMatterSquare.firstOutput ε h (a i) (w i) (C i) (p i) (b i) (P i) j
    hε hh (ha i) (hw i) hb

def secondOutput (θ : ℝ) : Hilbert := ∑ i,
  KFCausalSourcedWidthMatterSquare.secondOutput ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
    hε hh (ha i) (hw i) (hW i) hb θ

def projectedOutput : Hilbert := ∑ i,
  KFCausalSourcedWidthMatterProjected.projectedOutput ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
    hε hh (ha i) (hw i) (hW i) hb

local notation "u" => firstOutput n ε h a w p C b P j hε ha hh hw hb
local notation "v" => secondOutput n ε h a w p C b P j hε ha hh hw hb
local notation "z" => projectedOutput n ε h a w p C b P j hε ha hh hw hb

theorem first_graph : (ψ,u) ∈ (S).graph := by
  have hs := (S).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthMatterSquare.first_graph ε h (a i) (w i) (C i) (p i) (b i) (P i) j
        hε hh (ha i) (hw i) hb)
  simpa only [← prod_mk_sum,state,firstOutput,KFCausalSourcedWidthSecondInput.state] using hs

theorem mixed_graph (θ : ℝ) : (action h hh θ u,v θ) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthMatterSquare.mixed_square_graph ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
        hε hh (ha i) (hw i) (hW i) hb θ)
  simpa only [← prod_mk_sum,firstOutput,secondOutput,map_sum] using hs

theorem mixed_domain (θ : ℝ) : action h hh θ u ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_graph n ε h a w p C b P j hε ha hh hw hb θ)

theorem projected_graph : (zeroProjection h hh u,z) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthMatterProjected.projected_square_graph ε h (a i) W (w i) (C i) (p i) (b i) (P i) j
        hε hh (ha i) (hw i) (hW i) hb)
  simpa only [← prod_mk_sum,firstOutput,projectedOutput,map_sum] using hs

theorem projected_domain : zeroProjection h hh u ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_graph n ε h a w p C b P j hε ha hh hw hb)

theorem square_matter_graph : (ψ,v 0) ∈ (composition (square ε hε h) S).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨u,first_graph n ε h a w p C b P j hε ha hh hw hb,?_⟩
  simpa only [KFCausalPhysicalCircleAction.action_zero] using
    mixed_graph n ε h a w p C b P j hε ha hh hw hb 0

include hb in
theorem square_matter_domain : ψ ∈ (composition (square ε hε h) S).domain :=
  LinearPMap.mem_domain_of_mem_graph (square_matter_graph n ε h a w p C b P j hε ha hh hw hb)

theorem secondOutput_continuous : Continuous v := by
  apply continuous_finset_sum
  intro i _
  exact KFCausalSourcedWidthMatterContinuity.secondOutput_continuous
    ε h (a i) W (w i) (C i) (p i) (b i) (P i) j hε hh (ha i) (hw i) (hW i) hb

theorem two_angle_graph (θ φ : ℝ) :
    (ψ,action h hh (-φ) (v (φ-θ))) ∈
      (composition (squareAt ε hε h hh φ) (operatorAt h hh S θ)).graph :=
  KFCausalChargeConjugatedInsertion.two_angle_graph h hh S ε hε ψ u v
    (action_state n ε h a w p C b P hε ha hh hw)
    (first_graph n ε h a w p C b P j hε ha hh hw hb)
    (mixed_graph n ε h a w p C b P j hε ha hh hw hb) θ φ

include hb in
theorem two_angle_domain (θ φ : ℝ) :
    ψ ∈ (composition (squareAt ε hε h hh φ) (operatorAt h hh S θ)).domain :=
  LinearPMap.mem_domain_of_mem_graph (two_angle_graph n ε h a w p C b P j hε ha hh hw hb θ φ)

#print axioms first_graph
#print axioms mixed_graph
#print axioms mixed_domain
#print axioms projected_graph
#print axioms projected_domain
#print axioms square_matter_graph
#print axioms square_matter_domain
#print axioms secondOutput_continuous
#print axioms two_angle_graph
#print axioms two_angle_domain
end
end UnifiedTheory.Audit.KFCausalFiniteSourcedMatterSquare

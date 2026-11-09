/- The original arbitrary finite sourced reciprocal packet family has
mixed and charge-projected second vacuum-square graphs. The width cap
is derived from the finite family, and all sums precede the operator
action. No lower bound on the norm of a cancelling sum is assumed. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthProjectedSquare
import UnifiedTheory.Audit.KFCausalSingleGaussianTwoAngleSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalFiniteSourcedMixedVacuum
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action action_compose)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalSingleGaussianTwoAngleSquare (squareAt squareAt_graph)
open KFCausalSingleGaussianMixedSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state state_zeroSector)

def widthCap (n : ℕ) (w : Fin n → ℝ) : ℝ := 1+∑ i, w i

theorem widthCap_positive (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 1 ≤ w i) :
    0 < widthCap n w := by
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (zero_le_one.trans (hw i)))
  unfold widthCap
  linarith

theorem width_le_cap (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 1 ≤ w i) (i : Fin n) :
    w i ≤ widthCap n w := by
  have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    (zero_le_one.trans (hw j))) (Finset.mem_univ i)
  unfold widthCap
  linarith

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "hb₀" => original_strip ε h hε hb
local notation "W" => widthCap n w
local notation "hW" => width_le_cap n w hw

def firstOutput : Hilbert := ∑ i,
  KFCausalSourcedWidthSecondInput.firstOutput ε h (a i) (w i) (C i) (p i) (b i) (P i)
    hε hh (ha i) (hw i) hb₀

def secondOutput (θ : ℝ) : Hilbert := ∑ i,
  KFCausalSourcedWidthMixedSquare.secondOutput ε h (a i) W (w i) (C i) (p i) (b i) (P i)
    hε hh (ha i) (hw i) (hW i) hb θ

def projectedOutput : Hilbert := ∑ i,
  KFCausalSourcedWidthProjectedSquare.projectedOutput ε h (a i) W (w i) (C i) (p i) (b i) (P i)
    hε hh (ha i) (hw i) (hW i) hb

local notation "u" => firstOutput n ε h a w p C b P hε ha hh hw hb
local notation "v" => secondOutput n ε h a w p C b P hε ha hh hw hb
local notation "z" => projectedOutput n ε h a w p C b P hε ha hh hw hb

theorem action_state (θ : ℝ) : action h hh θ ψ=ψ :=
  state_zeroSector n ε h a w p C b P hε ha hh hw θ

theorem first_graph : (ψ,u) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthSecondInput.first_graph ε h (a i) (w i) (C i) (p i) (b i) (P i)
        hε hh (ha i) (hw i) hb₀)
  simpa only [← prod_mk_sum,state,firstOutput,KFCausalSourcedWidthSecondInput.state] using hs

theorem mixed_graph (θ : ℝ) : (action h hh θ u,v θ) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthMixedSquare.mixed_square_graph ε h (a i) W (w i) (C i) (p i) (b i) (P i)
        hε hh (ha i) (hw i) (hW i) hb θ)
  simpa only [← prod_mk_sum,firstOutput,secondOutput,map_sum] using hs

theorem projected_graph : (zeroProjection h hh u,z) ∈ (square ε hε h).graph := by
  have hs := (square ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthProjectedSquare.projected_square_graph ε h (a i) W (w i) (C i) (p i) (b i) (P i)
        hε hh (ha i) (hw i) (hW i) hb)
  simpa only [← prod_mk_sum,firstOutput,projectedOutput,map_sum] using hs

theorem projected_domain : zeroProjection h hh u ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_graph n ε h a w p C b P hε ha hh hw hb)

def firstAt (θ : ℝ) : Hilbert := action h hh (-θ) u
def secondAt (θ φ : ℝ) : Hilbert := action h hh (-φ) (v (φ-θ))

theorem firstAt_graph (θ : ℝ) :
    (ψ,firstAt n ε h a w p C b P hε ha hh hw hb θ) ∈ (squareAt ε hε h hh θ).graph := by
  apply (squareAt_graph ε hε h hh θ _ _).mpr
  rw [action_state n ε h a w p C b P hε ha hh hw θ]
  unfold firstAt
  rw [action_compose,neg_add_cancel,KFCausalPhysicalCircleAction.action_zero]
  exact first_graph n ε h a w p C b P hε ha hh hw hb

theorem secondAt_graph (θ φ : ℝ) :
    (firstAt n ε h a w p C b P hε ha hh hw hb θ,
      secondAt n ε h a w p C b P hε ha hh hw hb θ φ) ∈ (squareAt ε hε h hh φ).graph := by
  apply (squareAt_graph ε hε h hh φ _ _).mpr
  unfold firstAt secondAt
  rw [action_compose,action_compose,neg_add_cancel,KFCausalPhysicalCircleAction.action_zero]
  simpa only [show -θ+φ=φ-θ by ring] using mixed_graph n ε h a w p C b P hε ha hh hw hb (φ-θ)

theorem two_angle_graph (θ φ : ℝ) :
    (ψ,secondAt n ε h a w p C b P hε ha hh hw hb θ φ) ∈
      (composition (squareAt ε hε h hh φ) (squareAt ε hε h hh θ)).graph :=
  (composition_graph _ _ _ _).mpr ⟨firstAt n ε h a w p C b P hε ha hh hw hb θ,
    firstAt_graph n ε h a w p C b P hε ha hh hw hb θ,
    secondAt_graph n ε h a w p C b P hε ha hh hw hb θ φ⟩

include hb in
theorem two_angle_domain (θ φ : ℝ) :
    ψ ∈ (composition (squareAt ε hε h hh φ) (squareAt ε hε h hh θ)).domain :=
  LinearPMap.mem_domain_of_mem_graph (two_angle_graph n ε h a w p C b P hε ha hh hw hb θ φ)

#print axioms widthCap_positive
#print axioms width_le_cap
#print axioms action_state
#print axioms first_graph
#print axioms mixed_graph
#print axioms projected_graph
#print axioms projected_domain
#print axioms firstAt_graph
#print axioms secondAt_graph
#print axioms two_angle_graph
#print axioms two_angle_domain
end
end UnifiedTheory.Audit.KFCausalFiniteSourcedMixedVacuum

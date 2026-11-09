/- The linear field and field square have explicit physical L2 outputs
on the dense repaired trial family. These outputs lie in the actual
reversed exponential/clock composition domain. -/
import UnifiedTheory.Audit.KFCausalPhysicalField
import UnifiedTheory.Audit.KFCausalClockFloorFieldPolynomials
import UnifiedTheory.Audit.KFCausalClockFloorWeightedProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFieldGraphs
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorCoreStates
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalFieldPolynomialPackets
open UnifiedTheory.Audit.KFCausalClockFloorFieldPolynomials
open UnifiedTheory.Audit.KFCausalClockFloorWeightedProducts
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain

def monomialState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (l : Transverse →L[ℝ] ℝ) (i j : ℕ) (ψ : SchwartzMap TailSpace ℂ) : Hilbert :=
  weightedState ε a j p 0 hε ha (Nat.cast_nonneg j) (zero_shift_bound ε hε) (polynomialPacket l i j ψ)

theorem monomialState_coe (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (l : Transverse →L[ℝ] ℝ) (i j : ℕ) (ψ : SchwartzMap TailSpace ℂ) :
    monomialState ε a p hε ha l i j ψ =ᵐ[volume]
      weightedFunction ε hε (monomialFunction ε a p l i j ψ) :=
  weightedState_coe ε a j p 0 hε ha (Nat.cast_nonneg j) (zero_shift_bound ε hε) _

def linearState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (l : Transverse →L[ℝ] ℝ) (ψ : SchwartzMap TailSpace ℂ) : Hilbert :=
  monomialState ε a p hε ha l 1 0 ψ+monomialState ε a p hε ha l 0 1 ψ

def quadraticState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (l : Transverse →L[ℝ] ℝ) (ψ : SchwartzMap TailSpace ℂ) : Hilbert :=
  monomialState ε a p hε ha l 2 0 ψ+(2:ℂ) • monomialState ε a p hε ha l 1 1 ψ+
    monomialState ε a p hε ha l 0 2 ψ

theorem trial_physicalField_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (l : Transverse →L[ℝ] ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    (trialState ε a p hε ha ψ (ψ.memLp 2 volume),linearState ε a p hε ha l ψ) ∈
      (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  unfold linearState
  filter_upwards [Lp.coeFn_add (monomialState ε a p hε ha l 1 0 ψ) (monomialState ε a p hε ha l 0 1 ψ),
    monomialState_coe ε a p hε ha l 1 0 ψ,monomialState_coe ε a p hε ha l 0 1 ψ,
    trialState_coe ε a p hε ha ψ (ψ.memLp 2 volume)] with z hs h₀ h₁ ht
  simp only [Pi.add_apply] at hs
  rw [hs,h₀,h₁,ht,trialFunction_eq_weighted]
  exact weighted_linear_polynomial ε a p hε l ψ z

theorem trial_fieldSquare_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (l : Transverse →L[ℝ] ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    (trialState ε a p hε ha ψ (ψ.memLp 2 volume),quadraticState ε a p hε ha l ψ) ∈
      (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  unfold quadraticState
  filter_upwards [Lp.coeFn_add
      (monomialState ε a p hε ha l 2 0 ψ+(2:ℂ) • monomialState ε a p hε ha l 1 1 ψ)
      (monomialState ε a p hε ha l 0 2 ψ),
    Lp.coeFn_add (monomialState ε a p hε ha l 2 0 ψ) ((2:ℂ) • monomialState ε a p hε ha l 1 1 ψ),
    Lp.coeFn_smul (2:ℂ) (monomialState ε a p hε ha l 1 1 ψ),
    monomialState_coe ε a p hε ha l 2 0 ψ,monomialState_coe ε a p hε ha l 1 1 ψ,
    monomialState_coe ε a p hε ha l 0 2 ψ,
    trialState_coe ε a p hε ha ψ (ψ.memLp 2 volume)] with z hs ht hm h₀ h₁ h₂ hf
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hs ht hm
  rw [hs,ht,hm,h₀,h₁,h₂,hf,trialFunction_eq_weighted]
  exact weighted_quadratic_polynomial ε a p hε l ψ z

theorem monomialState_mem_reversedExponential (ε a p hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) (i j : ℕ) (ψ : SchwartzMap TailSpace ℂ) :
    monomialState ε a p hε ha l i j ψ ∈ (reversedExponential ε hε hbar).domain :=
  weightedState_mem_reversedExponential ε a j p hbar hε ha (Nat.cast_nonneg j) hh _

theorem linearState_mem_reversedExponential (ε a p hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    linearState ε a p hε ha l ψ ∈ (reversedExponential ε hε hbar).domain :=
  (reversedExponential ε hε hbar).domain.add_mem
    (monomialState_mem_reversedExponential ε a p hbar hε ha hh l 1 0 ψ)
    (monomialState_mem_reversedExponential ε a p hbar hε ha hh l 0 1 ψ)

theorem quadraticState_mem_reversedExponential (ε a p hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hh : |hbar| ≤ Real.pi*ε)
    (l : Transverse →L[ℝ] ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    quadraticState ε a p hε ha l ψ ∈ (reversedExponential ε hε hbar).domain :=
  (reversedExponential ε hε hbar).domain.add_mem
    ((reversedExponential ε hε hbar).domain.add_mem
      (monomialState_mem_reversedExponential ε a p hbar hε ha hh l 2 0 ψ)
      ((reversedExponential ε hε hbar).domain.smul_mem (2:ℂ)
        (monomialState_mem_reversedExponential ε a p hbar hε ha hh l 1 1 ψ)))
    (monomialState_mem_reversedExponential ε a p hbar hε ha hh l 0 2 ψ)

#print axioms monomialState_coe
#print axioms trial_physicalField_graph
#print axioms trial_fieldSquare_graph
#print axioms monomialState_mem_reversedExponential
#print axioms linearState_mem_reversedExponential
#print axioms quadraticState_mem_reversedExponential

end
end UnifiedTheory.Audit.KFCausalClockFloorFieldGraphs

/- The actual clock and inverse-clock multiples of every original
finite sourced packet lie in the interacting averaged Hamiltonian domain.
All natural second graphs are constructed from primitive clock transports;
the clock action itself is identified by its maximal physical graph. -/
import UnifiedTheory.Audit.KFCausalAnalyticClockSecondTransport
import UnifiedTheory.Audit.KFCausalGaussianHolomorphicClockWeight
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSecondFactors
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition
import UnifiedTheory.Audit.KFCausalClockMixedClockGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalClockWeightedOriginalHamiltonian
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroSector zeroProjection zeroProjection_fixes)
open KFCausalGaussianHolomorphicClockWeight (multiplier bound bound_nonnegative
  multiplier_analytic multiplier_bound physicalPower profile_split)
open KFCausalAnalyticClockSecondTransport (operator secondShift)
open KFCausalClockFloorClockOperator (clockOperator clockOperator_graph)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)

variable (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w) (hb : |h| ≤ ε/10)

private theorem packet_strip (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10) :
    |h| ≤ Real.pi*ε/3 := by
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

def clockAction (inverse : Bool) (y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  operator (multiplier ε a inverse) h (bound ε h a inverse)
    (multiplier_analytic ε h a inverse hε hb)
    (bound_nonnegative ε h a inverse hε)
    (multiplier_bound ε h a inverse hε hb ha) ε y hy

def singleState (inverse : Bool) : Hilbert :=
  clockAction ε h a hε ha hb inverse 0 (by simp)
    (KFCausalReciprocalNeutralPackets.state ε (a/2) h w hε (by positivity) hh hw C p b P)

def singleComponent (inverse : Bool) (j : Fin 8) : Hilbert :=
  clockAction ε h a hε ha hb inverse (secondShift h j)
    (by unfold secondShift; split_ifs <;> simp)
    (KFCausalReciprocalNeutralSecondFactors.second ε (a/2) h w hε (by positivity) hh hw
      (packet_strip ε h hε hb) C p b P j)

theorem singleState_coe (inverse : Bool) :
    singleState ε h a w C p b P hε hh ha hw hb inverse =ᵐ[volume]
      fun x => physicalPower ε inverse x.1*KFCausalReciprocalNeutralPackets.profile ε a h w C p b P x := by
  filter_upwards [KFCausalAnalyticClockSecondTransport.operator_coe
    (multiplier ε a inverse) h (bound ε h a inverse)
    (multiplier_analytic ε h a inverse hε hb) (bound_nonnegative ε h a inverse hε)
    (multiplier_bound ε h a inverse hε hb ha) ε 0 (by simp)
    (KFCausalReciprocalNeutralPackets.state ε (a/2) h w hε (by positivity) hh hw C p b P),
    KFCausalReciprocalNeutralPackets.state_coe ε (a/2) h w hε (by positivity) hh hw C p b P]
    with x hm hs
  change singleState ε h a w C p b P hε hh ha hw hb inverse x = _ at hm
  rw [hm,hs]
  simpa only [KFCausalAnalyticClockSecondTransport.line,Complex.ofReal_zero,zero_mul,add_zero] using
    profile_split ε a h w C p b P inverse hε x

theorem singleState_zeroSector (inverse : Bool) :
    singleState ε h a w C p b P hε hh ha hw hb inverse ∈ zeroSector h hh := by
  intro θ
  change KFCausalPhysicalCircleAction.action h hh θ
      (singleState ε h a w C p b P hε hh ha hw hb inverse) =
    singleState ε h a w C p b P hε hh ha hw hb inverse
  unfold singleState clockAction
  rw [← KFCausalAnalyticClockSecondTransport.operator_charge]
  exact congrArg _ (KFCausalReciprocalNeutralCharge.state_zeroSector
    ε (a/2) h w hε (by positivity) hh hw C p b P θ)

theorem singleComponent_graph (inverse : Bool) (j : Fin 8) :
    (singleState ε h a w C p b P hε hh ha hw hb inverse,
      singleComponent ε h a w C p b P hε hh ha hw hb inverse j) ∈
      (component ε hε h j).graph :=
  KFCausalAnalyticClockSecondTransport.second_graph
    (multiplier ε a inverse) h (bound ε h a inverse)
    (multiplier_analytic ε h a inverse hε hb) (bound_nonnegative ε h a inverse hε)
    (multiplier_bound ε h a inverse hε hb ha) ε hε hh j _ _
    (KFCausalReciprocalNeutralSecondFactors.second_graph ε (a/2) h w hε (by positivity) hh hw
      (packet_strip ε h hε hb) C p b P j)

theorem single_clock_graph :
    (KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P,
      singleState ε h a w C p b P hε hh ha hw hb false) ∈ (clockOperator ε hε).graph := by
  apply (clockOperator_graph ε hε _ _).mpr
  filter_upwards [singleState_coe ε h a w C p b P hε hh ha hw hb false,
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P] with x hm hs
  rw [hm,hs]
  rfl

theorem single_inverse_clock_graph :
    (singleState ε h a w C p b P hε hh ha hw hb true,
      KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P) ∈ (clockOperator ε hε).graph := by
  apply (clockOperator_graph ε hε _ _).mpr
  filter_upwards [singleState_coe ε h a w C p b P hε hh ha hw hb true,
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P] with x hm hs
  rw [hm,hs]
  simp only [physicalPower,ite_true,KFCausalClockFloorFlow.clock]
  rw [← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (by positivity)),one_mul]

variable (n : ℕ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
  (ha : ∀ t, 0 < a t) (hw : ∀ t, 1 ≤ w t)

def state (inverse : Bool) : Hilbert := ∑ t,
  singleState ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb inverse

def componentOutputs (inverse : Bool) (j : Fin 8) : Hilbert := ∑ t,
  singleComponent ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb inverse j

theorem state_zeroSector (inverse : Bool) :
    state ε h hε hh hb n a w p C b P ha hw inverse ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem fun t _ =>
    singleState_zeroSector ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb inverse

theorem component_graphs (inverse : Bool) (j : Fin 8) :
    (state ε h hε hh hb n a w p C b P ha hw inverse,
      componentOutputs ε h hε hh hb n a w p C b P ha hw inverse j) ∈ (component ε hε h j).graph := by
  have hs := (component ε hε h j).graph.sum_mem fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
    singleComponent_graph ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb inverse j
  simpa only [state,componentOutputs,← prod_mk_sum] using hs

theorem clock_graph :
    (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw,
      state ε h hε hh hb n a w p C b P ha hw false) ∈ (clockOperator ε hε).graph := by
  have hs := (clockOperator ε hε).graph.sum_mem fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
    single_clock_graph ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb
  simpa only [state,KFCausalReciprocalNeutralSuperposition.state,← prod_mk_sum] using hs

theorem inverse_clock_graph :
    (state ε h hε hh hb n a w p C b P ha hw true,
      KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw) ∈ (clockOperator ε hε).graph := by
  have hs := (clockOperator ε hε).graph.sum_mem fun t (_ : t ∈ (Finset.univ : Finset (Fin n))) =>
    single_inverse_clock_graph ε h (a t) (w t) (C t) (p t) (b t) (P t) hε hh (ha t) (hw t) hb
  simpa only [state,KFCausalReciprocalNeutralSuperposition.state,← prod_mk_sum] using hs

theorem inverse_state_eq :
    state ε h hε hh hb n a w p C b P ha hw true =
      KFCausalClockFloorBoundedInverse.inverseL ε hε
        (KFCausalClockFloorBoundedInverse.inverseL ε hε
          (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw)) :=
  (KFCausalClockMixedClockGraph.clockOperator_inverse_iff ε hε _ _).mp
    (inverse_clock_graph ε h hε hh hb n a w p C b P ha hw)

def hamiltonianOutput (inverse : Bool) (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (componentOutputs ε h hε hh hb n a w p C b P ha hw inverse))

theorem hamiltonian_graph (inverse : Bool) (mass2 quartic vacuum t : ℝ)
    (hstrip : |h| ≤ 2*Real.pi*ε/3) :
    (state ε h hε hh hb n a w p C b P ha hw inverse,
      hamiltonianOutput ε h hε hh hb n a w p C b P ha hw inverse mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).graph :=
  KFCausalNaturalSecondHamiltonianGraph.hamiltonian_graph ε h hε hh hstrip mass2 quartic vacuum t _
    (state_zeroSector ε h hε hh hb n a w p C b P ha hw inverse)
    (componentOutputs ε h hε hh hb n a w p C b P ha hw inverse)
    (component_graphs ε h hε hh hb n a w p C b P ha hw inverse)

theorem projected_hamiltonian_domain (inverse : Bool) (mass2 quartic vacuum t : ℝ)
    (hstrip : |h| ≤ 2*Real.pi*ε/3) :
    zeroProjection h hh (state ε h hε hh hb n a w p C b P ha hw inverse) ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).domain := by
  rw [zeroProjection_fixes h hh _ (state_zeroSector ε h hε hh hb n a w p C b P ha hw inverse)]
  exact LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε h hε hh hb n a w p C b P ha hw inverse mass2 quartic vacuum t hstrip)

include hb in
theorem inverse_hamiltonian_domain (mass2 quartic vacuum t : ℝ)
    (hstrip : |h| ≤ 2*Real.pi*ε/3) :
    KFCausalClockFloorBoundedInverse.inverseL ε hε
      (KFCausalClockFloorBoundedInverse.inverseL ε hε
        (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw)) ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).domain := by
  rw [← inverse_state_eq ε h hε hh hb n a w p C b P ha hw]
  exact LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε h hε hh hb n a w p C b P ha hw true mass2 quartic vacuum t hstrip)

#print axioms singleState_coe
#print axioms singleState_zeroSector
#print axioms singleComponent_graph
#print axioms single_clock_graph
#print axioms single_inverse_clock_graph
#print axioms state_zeroSector
#print axioms component_graphs
#print axioms clock_graph
#print axioms inverse_clock_graph
#print axioms inverse_state_eq
#print axioms hamiltonian_graph
#print axioms projected_hamiltonian_domain
#print axioms inverse_hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalClockWeightedOriginalHamiltonian

/- Finite superpositions with independently chosen reciprocal widths,
clock widths and frequencies, neutral sources, and neutral polynomials.
Both the state and its actual clock momentum have all natural factor
graphs and zero charge. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralCharge
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)

def state : Hilbert := ∑ i,
  KFCausalReciprocalNeutralPackets.state ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i)
def momentum : Hilbert := ∑ i,
  KFCausalReciprocalNeutralPackets.momentum ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i)

theorem state_zeroSector : state n ε h a w p C b P hε ha hh hw ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem fun i _ =>
    KFCausalReciprocalNeutralCharge.state_zeroSector ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i)

theorem momentum_zeroSector : momentum n ε h a w p C b P hε ha hh hw ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem fun i _ =>
    KFCausalReciprocalNeutralCharge.momentum_zeroSector ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i)

theorem momentum_graph :
    (state n ε h a w p C b P hε ha hh hw,momentum n ε h a w p C b P hε ha hh hw) ∈
      (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    KFCausalReciprocalNeutralPackets.momentum_graph ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i)
  simpa only [state,momentum,← prod_mk_sum] using hs

omit p b P in
theorem state_reciprocal :
    state n ε h a w (fun _ => 0) C (fun _ => 0) (fun _ => 1) hε ha hh hw =
      KFCausalReciprocalSuperpositionFactors.state n ε h a w C hε ha hh hw := by
  unfold state KFCausalReciprocalSuperpositionFactors.state
  apply Finset.sum_congr rfl
  intro i _
  apply Lp.ext
  filter_upwards [KFCausalReciprocalNeutralPackets.state_coe ε (a i) h (w i)
    hε (ha i) hh (hw i) (C i) 0 0 1,
    Lp.coeFn_smul (C i) (KFCausalReciprocalGaussianCharge.state ε (a i) h (w i)
      hε (ha i) hh (by have := hw i; linarith)),
    KFCausalReciprocalGaussianCharge.state_configuration_coe ε (a i) h (w i)
      hε (ha i) hh (by have := hw i; linarith)] with x hs hc hg
  rw [hs,hc,Pi.smul_apply,smul_eq_mul,hg]
  simp [KFCausalReciprocalNeutralPackets.profile,KFCausalClockFloorCoherentStrip.clockPhase]

omit w hw in
theorem state_neutral :
    state n ε h a (fun _ => 1) p C b P hε ha hh (fun _ => by norm_num) =
      KFCausalNeutralMixedClockState.state ε h hε hh n a p ha b C P := by
  simp only [state,KFCausalReciprocalNeutralCharge.one_eq_neutral,KFCausalNeutralMixedClockState.state]

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (j : Fin 8) : Hilbert := ∑ i,
  KFCausalReciprocalNeutralPackets.output ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i) hb j
def momentumOutput (j : Fin 8) : Hilbert := ∑ i,
  KFCausalReciprocalNeutralPackets.momentumOutput ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i) hb j

theorem output_graph (j : Fin 8) :
    (state n ε h a w p C b P hε ha hh hw,output n ε h a w p C b P hε ha hh hw hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField j).graph.sum_mem
    fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralPackets.output_graph ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i) hb j
  simpa only [state,output,← prod_mk_sum] using hs

theorem momentumOutput_graph (j : Fin 8) :
    (momentum n ε h a w p C b P hε ha hh hw,momentumOutput n ε h a w p C b P hε ha hh hw hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField j).graph.sum_mem
    fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralPackets.momentumOutput_graph ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P i) hb j
  simpa only [momentum,momentumOutput,← prod_mk_sum] using hs

include hb in
theorem common_domains :
    state n ε h a w p C b P hε ha hh hw ∈ commonEnergyDomain ε hε h modelDirections pointField ∧
      momentum n ε h a w p C b P hε ha hh hw ∈ commonEnergyDomain ε hε h modelDirections pointField :=
  ⟨(commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr fun j =>
    LinearPMap.mem_domain_of_mem_graph (output_graph n ε h a w p C b P hε ha hh hw hb j),
   (commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr fun j =>
    LinearPMap.mem_domain_of_mem_graph (momentumOutput_graph n ε h a w p C b P hε ha hh hw hb j)⟩

#print axioms state_zeroSector
#print axioms momentum_zeroSector
#print axioms momentum_graph
#print axioms state_reciprocal
#print axioms state_neutral
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms common_domains
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition

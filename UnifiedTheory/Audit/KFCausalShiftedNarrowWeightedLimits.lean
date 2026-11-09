/- Dominated joint L2 convergence for the charged quotient and charged
jet with arbitrary controlled polynomial coefficients and L2 clock data. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedProfiles
import UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedLimits
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers (Controlled)
open KFCausalShiftedNarrowWeightedProfiles

variable (α β ε y : ℝ) (b : ℂ) (c : ℝ → ℂ) (U : Configuration → ℂ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hc : Continuous c) (hc2 : MemLp c 2 volume) (hU : Controlled U) (n : ℕ)

def vector (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  (weighted_memLp α β ε y b c U hα hβ hw hε hy hc hc2 hU n δ hδ).toLp
    (weighted α β ε y b c U n δ) else 0
def jetVector (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  (weightedJet_memLp α β ε y b c U hα hβ hw hε hy hc hc2 hU n δ hδ).toLp
    (weightedJet α β ε y b c U n δ) else 0

omit hc in
def limitVector : Hilbert := (moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n).toLp
  (moment α β ε y b c U n)
omit hc in
def limitJetVector : Hilbert := (limitJet_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n).toLp
  (limitJet α β ε y b c U n)

theorem vector_coe (δ : ℝ) (hδ : 0 < δ) :
    vector α β ε y b c U hα hβ hw hε hy hc hc2 hU n δ =ᵐ[volume] weighted α β ε y b c U n δ := by
  rw [vector,dif_pos hδ]
  exact MemLp.coeFn_toLp _

theorem jetVector_coe (δ : ℝ) (hδ : 0 < δ) :
    jetVector α β ε y b c U hα hβ hw hε hy hc hc2 hU n δ =ᵐ[volume] weightedJet α β ε y b c U n δ := by
  rw [jetVector,dif_pos hδ]
  exact MemLp.coeFn_toLp _

omit hc in
theorem limitVector_coe :
    limitVector α β ε y b c U hα hβ hw hε hy hc2 hU n =ᵐ[volume] moment α β ε y b c U n :=
  MemLp.coeFn_toLp _

omit hc in
theorem limitJetVector_coe :
    limitJetVector α β ε y b c U hα hβ hw hε hy hc2 hU n =ᵐ[volume] limitJet α β ε y b c U n :=
  MemLp.coeFn_toLp _

theorem vector_tendsto :
    Tendsto (vector α β ε y b c U hα hβ hw hε hy hc hc2 hU n) (𝓝[>] 0)
      (𝓝 (limitVector α β ε y b c U hα hβ hw hε hy hc2 hU n)) := by
  apply KFCausalDominatedRepresentedL2Limit.represented_tendsto _ _ _ _
    (fun x => ‖moment α β ε y b c U n x‖)
    (moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n).norm
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact vector_coe α β ε y b c U hα hβ hw hε hy hc hc2 hU n δ hδ
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs,abs_norm] using weighted_bound α β ε y b c U hα hε hy n δ hδ x
  · exact Eventually.of_forall (weighted_tendsto α β ε y b c U n)

theorem jetVector_tendsto :
    Tendsto (jetVector α β ε y b c U hα hβ hw hε hy hc hc2 hU n) (𝓝[>] 0)
      (𝓝 (limitJetVector α β ε y b c U hα hβ hw hε hy hc2 hU n)) := by
  apply KFCausalDominatedRepresentedL2Limit.represented_tendsto _ _ _ _
    (fun x => (n:ℝ)*‖moment α β ε y b c U (n-1) x‖+‖moment α β ε y b c U n x‖)
    ((((moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU (n-1)).norm).const_mul (n:ℝ)).add
      (moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n).norm)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact jetVector_coe α β ε y b c U hα hβ hw hε hy hc hc2 hU n δ hδ
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with x
    have hn : 0 ≤ (n:ℝ)*‖moment α β ε y b c U (n-1) x‖+‖moment α β ε y b c U n x‖ := by positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using weightedJet_bound α β ε y b c U hα hε hy n δ hδ x
  · exact Eventually.of_forall (weightedJet_tendsto α β ε y b c U n)

#print axioms vector_coe
#print axioms jetVector_coe
#print axioms limitVector_coe
#print axioms limitJetVector_coe
#print axioms vector_tendsto
#print axioms jetVector_tendsto
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedLimits

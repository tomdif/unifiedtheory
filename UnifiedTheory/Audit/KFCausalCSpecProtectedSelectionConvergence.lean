/-
  Protected selection: lower-bound certificates and actual census recovery.

  This module uses the existing order-derived bridgeCensusDefect. It proves
  convergence of repeated selection on transport candidates, not emergence
  of a spacetime-like causal order under maximal births.
-/

import UnifiedTheory.Audit.KFCausalBornProtectedSelection
import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecProtectedSelectionConvergence
noncomputable section
open scoped BigOperators
open Filter Topology
open KFCausalBornProtectedSelection
open KFCausalCSpecBridgeDefectObservable
open KFCausalCSpecCensusRecovery
open KFCausalCSpecContinuationProfile
open KFCausalCSpecOverlapScore
open KFCausalCSpecGlobalization

section ProtectedBounds
variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

def SameRecordLaw (p q : ι → ℝ) (H : ι → κ) : Prop :=
  ∀ k, ∑ i ∈ recordFiber H k, q i = ∑ i ∈ recordFiber H k, p i

theorem sameRecordLaw_expectation (p q : ι → ℝ) (H : ι → κ)
    (h : SameRecordLaw p q H) (f : κ → ℝ) :
    ∑ i, q i * f (H i) = ∑ i, p i * f (H i) := by
  have hcenter : ∀ k, ∑ i ∈ recordFiber H k, (1 : ℝ) * (q i - p i) = 0 := by
    intro k
    simp only [one_mul, Finset.sum_sub_distrib, h k, sub_self]
  have hz := centered_annihilates_record_observable
    (fun _ => 1) (fun i => q i - p i) H hcenter f
  simp only [one_mul, sub_mul, Finset.sum_sub_distrib] at hz
  exact sub_eq_zero.mp hz

/-- Any lower bound that depends only on the protected record is an
unavoidable expected-defect floor for every allowed selector. -/
theorem protected_expectation_lower_bound (p q G : ι → ℝ) (H : ι → κ)
    (h : SameRecordLaw p q H) (hq : ∀ i, 0 ≤ q i)
    (lower : κ → ℝ) (hlower : ∀ i, lower (H i) ≤ G i) :
    ∑ i, p i * lower (H i) ≤ ∑ i, q i * G i := by
  rw [← sameRecordLaw_expectation p q H h lower]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlower i) (hq i)

theorem protected_floor_excludes_growth_descent (p q G : ι → ℝ) (H : ι → κ)
    (h : SameRecordLaw p q H) (hq : ∀ i, 0 ≤ q i)
    (lower : κ → ℝ) (hlower : ∀ i, lower (H i) ≤ G i)
    (parentDefect : ℝ) (hfloor : parentDefect ≤ ∑ i, p i * lower (H i)) :
    parentDefect ≤ ∑ i, q i * G i :=
  hfloor.trans (protected_expectation_lower_bound p q G H h hq lower hlower)

/-- Full support cannot attain a lower envelope if any child lies strictly
above it. It may nevertheless approach that envelope arbitrarily closely. -/
theorem protected_expectation_strict_lower_bound (p q G : ι → ℝ) (H : ι → κ)
    (h : SameRecordLaw p q H) (hq : ∀ i, 0 < q i)
    (lower : κ → ℝ) (hlower : ∀ i, lower (H i) ≤ G i)
    (hstrict : ∃ i, lower (H i) < G i) :
    ∑ i, p i * lower (H i) < ∑ i, q i * G i := by
  rw [← sameRecordLaw_expectation p q H h lower]
  apply Finset.sum_lt_sum
  · intro i _
    exact mul_le_mul_of_nonneg_left (hlower i) (hq i).le
  · obtain ⟨i, hi⟩ := hstrict
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hq i)⟩
end ProtectedBounds

abbrev Candidate := Equiv.Perm Direction

theorem bridgeCensusDefect_le_twentySeven (e : E4) (tau : Candidate) :
    bridgeCensusDefect e tau ≤ 27 := by
  unfold bridgeCensusDefect
  rw [permScore_shift, gram_permScore_closed bprof bgram]
  have h0 : (-3 : ℝ) ≤ if ((fourState.perm e)⁻¹ * tau) 0 = 0 then 6 else -3 := by
    split <;> norm_num
  have h1 : (-3 : ℝ) ≤ if ((fourState.perm e)⁻¹ * tau) 1 = 1 then 6 else -3 := by
    split <;> norm_num
  have h2 : (-3 : ℝ) ≤ if ((fourState.perm e)⁻¹ * tau) 2 = 2 then 6 else -3 := by
    split <;> norm_num
  linarith

/-- A protected record separating a candidate from the canonical matching
forces at least the existing census gap on that record's probability mass. -/
theorem protected_bridge_record_floor {κ : Type*} [DecidableEq κ]
    (e : E4) (p q : Candidate → ℝ) (H : Candidate → κ)
    (h : SameRecordLaw p q H) (hq : ∀ tau, 0 ≤ q tau) :
    ∑ tau, p tau * (if H tau = H (fourState.perm e) then 0 else 18) ≤
      ∑ tau, q tau * bridgeCensusDefect e tau := by
  apply protected_expectation_lower_bound p q (bridgeCensusDefect e) H h hq
    (fun k => if k = H (fourState.perm e) then 0 else 18)
  intro tau
  split
  · exact bridgeCensusDefect_nonneg e tau
  · apply bridgeCensusDefect_wrong_floor e tau
    intro heq
    subst tau
    contradiction

/-- A conservative positive selection weight. The factor 36 is an algorithmic
choice justified by the [0,27] defect bound, not a derived physical coupling. -/
def censusSelectionWeight (e : E4) (tau : Candidate) : ℝ :=
  1 - bridgeCensusDefect e tau / 36

theorem censusSelectionWeight_bounds (e : E4) (tau : Candidate) :
    1 / 4 ≤ censusSelectionWeight e tau ∧ censusSelectionWeight e tau ≤ 1 := by
  have hlo := bridgeCensusDefect_nonneg e tau
  have hhi := bridgeCensusDefect_le_twentySeven e tau
  unfold censusSelectionWeight
  constructor <;> linarith

@[simp] theorem censusSelectionWeight_canonical (e : E4) :
    censusSelectionWeight e (fourState.perm e) = 1 := by
  simp [censusSelectionWeight, bridgeCensusDefect_canonical_zero]

theorem censusSelectionWeight_wrong_le_half (e : E4) (tau : Candidate)
    (htau : tau ≠ fourState.perm e) : censusSelectionWeight e tau ≤ 1 / 2 := by
  have h := bridgeCensusDefect_wrong_floor e tau htau
  unfold censusSelectionWeight
  linarith

def censusPartition (e : E4) (p : Candidate → ℝ) (k : ℕ) : ℝ :=
  ∑ tau, p tau * censusSelectionWeight e tau ^ k

def censusPosterior (e : E4) (p : Candidate → ℝ) (k : ℕ) (tau : Candidate) : ℝ :=
  p tau * censusSelectionWeight e tau ^ k / censusPartition e p k

def wrongCandidates (e : E4) : Finset Candidate := Finset.univ.erase (fourState.perm e)

def censusWrongProbability (e : E4) (p : Candidate → ℝ) (k : ℕ) : ℝ :=
  ∑ tau ∈ wrongCandidates e, censusPosterior e p k tau

def initialCensusOdds (e : E4) (p : Candidate → ℝ) : ℝ :=
  (∑ tau ∈ wrongCandidates e, p tau) / p (fourState.perm e)

theorem censusPartition_lower (e : E4) (p : Candidate → ℝ) (k : ℕ)
    (hp : ∀ tau, 0 ≤ p tau) : p (fourState.perm e) ≤ censusPartition e p k := by
  have h := Finset.single_le_sum
    (fun tau (_ : tau ∈ (Finset.univ : Finset Candidate)) =>
      mul_nonneg (hp tau) (pow_nonneg (by linarith [(censusSelectionWeight_bounds e tau).1]) k))
    (Finset.mem_univ (fourState.perm e))
  simpa [censusPartition] using h

theorem censusPosterior_pos (e : E4) (p : Candidate → ℝ) (k : ℕ)
    (hp : ∀ tau, 0 < p tau) (tau : Candidate) : 0 < censusPosterior e p k tau := by
  apply div_pos
  · exact mul_pos (hp tau) (pow_pos (by linarith [(censusSelectionWeight_bounds e tau).1]) k)
  · exact lt_of_lt_of_le (hp _) (censusPartition_lower e p k (fun tau => (hp tau).le))

theorem censusPosterior_normalized (e : E4) (p : Candidate → ℝ) (k : ℕ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    ∑ tau, censusPosterior e p k tau = 1 := by
  have hz : 0 < censusPartition e p k :=
    lt_of_lt_of_le hcanonical (censusPartition_lower e p k hp)
  simp only [censusPosterior, ← Finset.sum_div]
  exact div_self (ne_of_gt hz)

theorem censusWrongProbability_nonneg (e : E4) (p : Candidate → ℝ) (k : ℕ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    0 ≤ censusWrongProbability e p k := by
  apply Finset.sum_nonneg
  intro tau _
  exact div_nonneg (mul_nonneg (hp tau)
    (pow_nonneg (by linarith [(censusSelectionWeight_bounds e tau).1]) k))
    ((censusPartition_lower e p k hp).trans' hcanonical.le)

/-- An explicit rate for the actual bridge-census defect: wrong posterior
mass is bounded by initial odds times 2^(-k). No descent-rate premise. -/
theorem censusWrongProbability_le_geometric (e : E4) (p : Candidate → ℝ) (k : ℕ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    censusWrongProbability e p k ≤ initialCensusOdds e p * (1 / 2 : ℝ) ^ k := by
  have hnum : 0 ≤ ∑ tau ∈ wrongCandidates e, p tau * censusSelectionWeight e tau ^ k :=
    Finset.sum_nonneg fun tau _ => mul_nonneg (hp tau)
      (pow_nonneg (by linarith [(censusSelectionWeight_bounds e tau).1]) k)
  have hbound : (∑ tau ∈ wrongCandidates e, p tau * censusSelectionWeight e tau ^ k) ≤
      (∑ tau ∈ wrongCandidates e, p tau) * (1 / 2 : ℝ) ^ k := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro tau htau
    apply mul_le_mul_of_nonneg_left _ (hp tau)
    exact pow_le_pow_left₀ (by linarith [(censusSelectionWeight_bounds e tau).1])
      (censusSelectionWeight_wrong_le_half e tau (Finset.mem_erase.mp htau).1) k
  unfold censusWrongProbability censusPosterior
  rw [← Finset.sum_div]
  calc
    _ ≤ (∑ tau ∈ wrongCandidates e, p tau * censusSelectionWeight e tau ^ k) /
        p (fourState.perm e) :=
      div_le_div_of_nonneg_left hnum hcanonical (censusPartition_lower e p k hp)
    _ ≤ ((∑ tau ∈ wrongCandidates e, p tau) * (1 / 2 : ℝ) ^ k) /
        p (fourState.perm e) := div_le_div_of_nonneg_right hbound hcanonical.le
    _ = _ := by unfold initialCensusOdds; ring

theorem censusWrongProbability_tendsto_zero (e : E4) (p : Candidate → ℝ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    Tendsto (censusWrongProbability e p) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => censusWrongProbability_nonneg e p k hp hcanonical)
    (fun k => censusWrongProbability_le_geometric e p k hp hcanonical)
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using hpow.const_mul (initialCensusOdds e p)

def censusMeanDefect (e : E4) (p : Candidate → ℝ) (k : ℕ) : ℝ :=
  ∑ tau, censusPosterior e p k tau * bridgeCensusDefect e tau

theorem censusMeanDefect_bounds (e : E4) (p : Candidate → ℝ) (k : ℕ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    0 ≤ censusMeanDefect e p k ∧
      censusMeanDefect e p k ≤ 27 * censusWrongProbability e p k := by
  have hpost : ∀ tau, 0 ≤ censusPosterior e p k tau := by
    intro tau
    exact div_nonneg (mul_nonneg (hp tau)
      (pow_nonneg (by linarith [(censusSelectionWeight_bounds e tau).1]) k))
      ((censusPartition_lower e p k hp).trans' hcanonical.le)
  constructor
  · exact Finset.sum_nonneg fun tau _ =>
      mul_nonneg (hpost tau) (bridgeCensusDefect_nonneg e tau)
  · have herase := Finset.sum_erase_add (Finset.univ : Finset Candidate)
      (fun tau => censusPosterior e p k tau * bridgeCensusDefect e tau)
      (Finset.mem_univ (fourState.perm e))
    have heq : censusMeanDefect e p k =
        ∑ tau ∈ wrongCandidates e, censusPosterior e p k tau * bridgeCensusDefect e tau := by
      simp [censusMeanDefect, wrongCandidates, bridgeCensusDefect_canonical_zero] at herase ⊢
    rw [heq, censusWrongProbability, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro tau _
    calc
      _ ≤ censusPosterior e p k tau * 27 :=
        mul_le_mul_of_nonneg_left (bridgeCensusDefect_le_twentySeven e tau) (hpost tau)
      _ = _ := mul_comm _ _

theorem censusMeanDefect_tendsto_zero (e : E4) (p : Candidate → ℝ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    Tendsto (censusMeanDefect e p) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => (censusMeanDefect_bounds e p k hp hcanonical).1)
    (fun k => (censusMeanDefect_bounds e p k hp hcanonical).2)
  simpa using (censusWrongProbability_tendsto_zero e p hp hcanonical).const_mul 27

/-- An age bank contains one copy of each posterior age 0,...,N-1. This
models adding one record and updating every old record once per stage.
It is an inference schedule, not an identification with causal births. -/
def censusAgeBankWrongTotal (e : E4) (p : Candidate → ℝ) (N : ℕ) : ℝ :=
  ∑ age ∈ Finset.range N, censusWrongProbability e p age

theorem censusAgeBankWrongTotal_bounds (e : E4) (p : Candidate → ℝ) (N : ℕ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    0 ≤ censusAgeBankWrongTotal e p N ∧
      censusAgeBankWrongTotal e p N ≤ 2 * initialCensusOdds e p := by
  have hodds : 0 ≤ initialCensusOdds e p :=
    div_nonneg (Finset.sum_nonneg fun tau _ => hp tau) hcanonical.le
  constructor
  · exact Finset.sum_nonneg fun age _ => censusWrongProbability_nonneg e p age hp hcanonical
  · calc
      _ ≤ ∑ age ∈ Finset.range N, initialCensusOdds e p * (1 / 2 : ℝ) ^ age :=
        Finset.sum_le_sum fun age _ => censusWrongProbability_le_geometric e p age hp hcanonical
      _ = initialCensusOdds e p * (2 * (1 - (1 / 2 : ℝ) ^ N)) := by
        rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        ring
      _ ≤ _ := by nlinarith [mul_nonneg hodds (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N)]

/-- Expected wrong-record density vanishes under the explicit age-bank
schedule. No probability-space or almost-sure assertion is hidden here. -/
theorem censusAgeBankWrongFraction_tendsto_zero (e : E4) (p : Candidate → ℝ)
    (hp : ∀ tau, 0 ≤ p tau) (hcanonical : 0 < p (fourState.perm e)) :
    Tendsto (fun N : ℕ => censusAgeBankWrongTotal e p N / N) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun N => div_nonneg (censusAgeBankWrongTotal_bounds e p N hp hcanonical).1 (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right
      (censusAgeBankWrongTotal_bounds e p N hp hcanonical).2 (Nat.cast_nonneg N))
  exact tendsto_const_div_atTop_nhds_zero_nat (2 * initialCensusOdds e p)

#print axioms protected_expectation_lower_bound
#print axioms protected_bridge_record_floor
#print axioms bridgeCensusDefect_le_twentySeven
#print axioms censusPosterior_normalized
#print axioms censusWrongProbability_le_geometric
#print axioms censusWrongProbability_tendsto_zero
#print axioms censusMeanDefect_tendsto_zero
#print axioms censusAgeBankWrongFraction_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalCSpecProtectedSelectionConvergence

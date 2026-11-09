/- Weak convergence commutes with restriction to a set whose frontier
has zero limiting mass. The proof extracts the two complementary positive
restrictions and identifies their limits by support and additivity. -/
import UnifiedTheory.Audit.KFCausalCompactWeakDomination
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactWeakRestriction
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [MetricSpace E] [CompactSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [Nonempty E]

omit [CompactSpace E] [SecondCountableTopology E] [Nonempty E] in
theorem closed_support_limit (μ : ℕ → FiniteMeasure E) (ν : FiniteMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν)) (S : Set E) (hS : IsClosed S)
    (hs : ∀ n, (μ n : Measure E) Sᶜ = 0) : (ν : Measure E) Sᶜ = 0 := by
  have he (n : ℕ) : (μ n : Measure E) S = (μ n : Measure E) univ := by
    simpa only [hs n,add_zero] using measure_add_measure_compl hS.measurableSet (μ := (μ n:Measure E))
  have ht : Tendsto (fun n => (μ n : Measure E) S) atTop (𝓝 ((ν:Measure E) univ)) := by
    simp_rw [he,← FiniteMeasure.ennreal_mass]
    exact (ENNReal.continuous_coe.tendsto ν.mass).comp hμ.mass
  have hb := FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ hS
  rw [ht.limsup_eq] at hb
  rw [measure_compl hS.measurableSet (measure_ne_top _ _),tsub_eq_zero_iff_le.mpr hb]

omit [CompactSpace E] [SecondCountableTopology E] [Nonempty E] in
theorem restrict_closure_compl_zero (μ : FiniteMeasure E) (S : Set E) :
    (μ.restrict S : Measure E) (closure S)ᶜ = 0 := by
  rw [FiniteMeasure.restrict_measure_eq,Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  have he : (closure S)ᶜ ∩ S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (subset_closure hx.2)
  rw [he,measure_empty]

omit [CompactSpace E] [SecondCountableTopology E] [BorelSpace E] [Nonempty E] in
theorem decomposition_restrict (P N ν : FiniteMeasure E) (S : Set E)
    (he : P+N = ν) (hP : (P:Measure E) (closure S)ᶜ = 0)
    (hN : (N:Measure E) (closure Sᶜ)ᶜ = 0) (hb : (ν:Measure E) (frontier S) = 0) :
    P = ν.restrict S := by
  have hPν : (P:Measure E) ≤ (ν:Measure E) := by
    rw [← he,FiniteMeasure.toMeasure_add]
    exact Measure.le_add_right le_rfl
  have hNν : (N:Measure E) ≤ (ν:Measure E) := by
    rw [← he,FiniteMeasure.toMeasure_add]
    exact Measure.le_add_left le_rfl
  have hpF : (P:Measure E) (frontier S) = 0 := le_antisymm ((hPν _).trans_eq hb) (zero_le _)
  have hnF : (N:Measure E) (frontier S) = 0 := le_antisymm ((hNν _).trans_eq hb) (zero_le _)
  have hpC : (P:Measure E) Sᶜ = 0 := by
    apply measure_mono_null _ (measure_union_null hpF hP)
    intro x hx
    by_cases hc : x ∈ closure S
    · exact Or.inl (by rw [frontier_eq_closure_inter_closure]; exact ⟨hc,subset_closure hx⟩)
    · exact Or.inr hc
  have hnS : (N:Measure E) S = 0 := by
    apply measure_mono_null _ (measure_union_null hnF hN)
    intro x hx
    by_cases hc : x ∈ closure Sᶜ
    · exact Or.inl (by rw [frontier_eq_closure_inter_closure]; exact ⟨subset_closure hx,hc⟩)
    · exact Or.inr hc
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.restrict_measure_eq,← he,FiniteMeasure.toMeasure_add,Measure.restrict_add,
    Measure.restrict_eq_zero.mpr hnS,add_zero]
  exact (Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff] using hpC)).symm

theorem weak_restrict (μ : ℕ → FiniteMeasure E) (ν : FiniteMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν)) (S : Set E) (hS : MeasurableSet S)
    (hb : (ν:Measure E) (frontier S) = 0) :
    Tendsto (fun n => (μ n).restrict S) atTop (𝓝 (ν.restrict S)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let M (n : ℕ) (j : Bool) := (μ (ns n)).restrict (if j then S else Sᶜ)
  have hm := (NNReal.continuous_coe.tendsto ν.mass).comp (hμ.comp hns).mass
  have hmB : ∀ᶠ n in atTop, ((μ (ns n)).mass:ℝ) ≤ (ν.mass:ℝ)+1 :=
    hm.eventually_le_const (by linarith)
  have hM : ∀ j, ∃ C : ℝ, ∀ᶠ n in atTop, ((M n j).mass:ℝ) ≤ C := by
    intro j
    refine ⟨(ν.mass:ℝ)+1,hmB.mono (fun n hn => le_trans ?_ hn)⟩
    dsimp only [M]
    have hh : ((μ (ns n)).restrict (if j then S else Sᶜ)).mass ≤ (μ (ns n)).mass := by
      rw [FiniteMeasure.restrict_mass]
      exact (μ (ns n)).apply_mono (subset_univ _)
    exact_mod_cast hh
  obtain ⟨φ,hφ,L,hL⟩ := KFCausalCompactFiniteMeasureSubsequence.common_subsequence M hM
  have hp : Tendsto (fun n => (μ (ns (φ n))).restrict S) atTop (𝓝 (L true)) := by
    simpa only [M,if_true] using hL true
  have hn : Tendsto (fun n => (μ (ns (φ n))).restrict Sᶜ) atTop (𝓝 (L false)) := by
    simpa only [M,Bool.false_eq_true,if_false] using hL false
  have he : L true+L false = ν := by
    apply tendsto_nhds_unique (hp.add hn)
    convert hμ.comp (hns.comp hφ.tendsto_atTop) using 1
    funext n
    apply FiniteMeasure.toMeasure_injective
    exact Measure.restrict_add_restrict_compl hS
  have hpS := closed_support_limit _ _ hp (closure S) isClosed_closure
    (fun n => restrict_closure_compl_zero (μ (ns (φ n))) S)
  have hnS := closed_support_limit _ _ hn (closure Sᶜ) isClosed_closure
    (fun n => restrict_closure_compl_zero (μ (ns (φ n))) Sᶜ)
  have hident := decomposition_restrict (L true) (L false) ν S he hpS hnS hb
  exact ⟨φ,hident ▸ hp⟩

#print axioms closed_support_limit
#print axioms restrict_closure_compl_zero
#print axioms decomposition_restrict
#print axioms weak_restrict
end
end UnifiedTheory.Audit.KFCausalCompactWeakRestriction

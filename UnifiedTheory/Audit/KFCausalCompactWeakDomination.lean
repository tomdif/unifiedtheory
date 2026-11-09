/- A fixed finite-measure upper bound survives weak convergence on a
compact metric space. Positive complementary measures supply the proof. -/
import UnifiedTheory.Audit.KFCausalCompactFiniteMeasureSubsequence
import Mathlib.MeasureTheory.Measure.Sub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactWeakDomination
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {E : Type*} [MetricSpace E] [CompactSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [Nonempty E]

theorem weak_limit_le (μ : ℕ → FiniteMeasure E) (ν D : FiniteMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν))
    (hb : ∀ᶠ n in atTop, (μ n : Measure E) ≤ (D : Measure E)) :
    (ν : Measure E) ≤ (D : Measure E) := by
  let δ (n : ℕ) : FiniteMeasure E := ⟨(D:Measure E)-(μ n:Measure E),inferInstance⟩
  have hd (n : ℕ) : ((δ n).mass:ℝ) ≤ (D.mass:ℝ) := by
    change ((D:Measure E)-(μ n:Measure E)).real Set.univ ≤ (D:Measure E).real Set.univ
    exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.sub_le Set.univ)
  obtain ⟨φ,hφ,Δ,hΔ⟩ := KFCausalCompactFiniteMeasureSubsequence.common_subsequence
    (fun n (_ : Unit) => δ n) (fun _ => ⟨D.mass,Eventually.of_forall hd⟩)
  have he : ∀ᶠ n in atTop, δ n+μ n = D := hb.mono (fun n hn => by
    apply FiniteMeasure.toMeasure_injective
    exact Measure.sub_add_cancel_of_le hn)
  have hs := (hΔ ()).add (hμ.comp hφ.tendsto_atTop)
  have hconst : Tendsto (fun n => δ (φ n)+μ (φ n)) atTop (𝓝 D) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hφ.tendsto_atTop.eventually he] with n hn
      exact hn.symm)
  have heq : Δ ()+ν = D := tendsto_nhds_unique hs hconst
  rw [← heq,FiniteMeasure.toMeasure_add]
  exact Measure.le_add_left le_rfl

#print axioms weak_limit_le
end
end UnifiedTheory.Audit.KFCausalCompactWeakDomination

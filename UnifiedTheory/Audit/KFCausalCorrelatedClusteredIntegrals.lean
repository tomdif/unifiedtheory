/- Compact clock envelopes and width-spacing integral limits for all
finite correlated blocks, including independently chosen neutral sources. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredIntegrals
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalCorrelatedClusteredBounds
open KFCausalReciprocalGaussianCoordinates (area)

variable {m : ℕ} (f : Family m)

theorem blockBound_envelope {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (k : ℕ) (α β q : ℝ) (r v : X → ℂ) (hr : Continuous r) (hv : Continuous v)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ s ∈ K, q ≤ α*area (r s))
    (hc : ∀ s ∈ K, q ≤ α*area (r s)-8*β*(r s).im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ s ∈ K, ∀ p, 0 ≤ p.2 → blockBound f k α β (r s) (v s) p ≤ D p := by
  choose D hDi hD0 hD using fun i => KFCausalClusteredClockCompactEnvelope.componentBound_envelope
    K hK (f.degree i) k α β q r v hr hv (f.source i) (f.polynomial i) hβ hq ha hc
  refine ⟨fun p => (m:ℝ)*∑ i, ‖f.amplitude i‖^2*D i p,
    (integrable_finset_sum Finset.univ (fun i _ => (hDi i).const_mul _)).const_mul _, ?_, ?_⟩
  · intro p
    exact mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hD0 i p)))
  · intro s hs p hp
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hD i s hs p hp) (sq_nonneg _))) (Nat.cast_nonneg m)

theorem common_envelope {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (α β q : ℝ) (r v : X → ℂ) (hr : Continuous r) (hv : Continuous v)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ s ∈ K, q ≤ α*area (r s))
    (hc : ∀ s ∈ K, q ≤ α*area (r s)-8*β*(r s).im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ s ∈ K, ∀ p, 0 ≤ p.2 →
        (∀ δ : ℝ, 0 < δ → ‖density f α β δ (r s) p‖ ≤ D p ∧ ‖response f α β δ (r s) (v s) p‖ ≤ D p) ∧
        ‖limitDensity f α β (r s) p‖ ≤ D p ∧ ‖limitResponse f α β (r s) (v s) p‖ ≤ D p := by
  obtain ⟨A,hAi,hA0,hA⟩ := blockBound_envelope f K hK 0 α β q r v hr hv hβ hq ha hc
  obtain ⟨B,hBi,hB0,hB⟩ := blockBound_envelope f K hK 1 α β q r v hr hv hβ hq ha hc
  obtain ⟨C,hCi,hC0,hC⟩ := blockBound_envelope f K hK 2 α β q r v hr hv hβ hq ha hc
  let D := fun p => A p+B p/2+C p/4
  have hD (s : X) (hs : s ∈ K) (p : Joint) (hp : 0 ≤ p.2) : fullBound f α β (r s) (v s) p ≤ D p :=
    add_le_add (add_le_add (hA s hs p hp) (div_le_div_of_nonneg_right (hB s hs p hp) (by norm_num)))
      (div_le_div_of_nonneg_right (hC s hs p hp) (by norm_num))
  refine ⟨D,(hAi.add (hBi.div_const 2)).add (hCi.div_const 4),?_,?_⟩
  · intro p
    have := hA0 p; have := hB0 p; have := hC0 p
    dsimp [D]; positivity
  · intro s hs p hp
    have he (δ : ℝ) (hδ : 0 < δ) := (density_norm_le f α β δ hδ (r s) (v s)
      (hq.le.trans (ha s hs)) p hp).trans (hD s hs p hp)
    have hr' (δ : ℝ) (hδ : 0 < δ) := (response_norm_le f α β δ hδ (r s) (v s)
      (hq.le.trans (ha s hs)) p hp).trans (hD s hs p hp)
    refine ⟨fun δ hδ => ⟨he δ hδ,hr' δ hδ⟩,?_,?_⟩
    · apply le_of_tendsto (density_tendsto f α β (r s) p).norm
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact he δ hδ
    · apply le_of_tendsto (response_tendsto f α β (r s) (v s) p).norm
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact hr' δ hδ

theorem fixed_envelope (α β : ℝ) (r v : ℂ) (hβ : 0 < β)
    (ha : 0 < α*area r) (hc : 0 < α*area r-8*β*r.im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ p, 0 ≤ p.2 →
        (∀ δ : ℝ, 0 < δ → ‖density f α β δ r p‖ ≤ D p ∧ ‖response f α β δ r v p‖ ≤ D p) ∧
        ‖limitDensity f α β r p‖ ≤ D p ∧ ‖limitResponse f α β r v p‖ ≤ D p := by
  obtain ⟨D,hDi,hD0,hD⟩ := common_envelope f ({0}:Set ℝ) isCompact_singleton α β
    (min (α*area r) (α*area r-8*β*r.im^2)) (fun _ => r) (fun _ => v) continuous_const continuous_const
    hβ (lt_min ha hc) (fun _ _ => min_le_left _ _) (fun _ _ => min_le_right _ _)
  exact ⟨D,hDi,hD0,hD 0 (by simp)⟩

theorem integrability (α β δ : ℝ) (hδ : 0 < δ) (r v : ℂ) (hβ : 0 < β)
    (ha : 0 < α*area r) (hc : 0 < α*area r-8*β*r.im^2) :
    Integrable (density f α β δ r) jointMeasure ∧ Integrable (response f α β δ r v) jointMeasure ∧
    Integrable (limitDensity f α β r) jointMeasure ∧ Integrable (limitResponse f α β r v) jointMeasure := by
  obtain ⟨D,hDi,_,hD⟩ := fixed_envelope f α β r v hβ ha hc
  refine ⟨hDi.mono' (density_continuous f α β δ r).aestronglyMeasurable ?_,
    hDi.mono' (response_continuous f α β δ r v).aestronglyMeasurable ?_,
    hDi.mono' (limitDensity_continuous f α β r).aestronglyMeasurable ?_,
    hDi.mono' (limitResponse_continuous f α β r v).aestronglyMeasurable ?_⟩
  all_goals filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  · exact ((hD p hp).1 δ hδ).1
  · exact ((hD p hp).1 δ hδ).2
  · exact (hD p hp).2.1
  · exact (hD p hp).2.2

theorem density_integral_tendsto (α β : ℝ) (r : ℂ) (hβ : 0 < β)
    (ha : 0 < α*area r) (hc : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ => ∫ p, density f α β δ r p ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ p, limitDensity f α β r p ∂jointMeasure)) := by
  obtain ⟨D,hDi,_,hD⟩ := fixed_envelope f α β r 0 hβ ha hc
  apply tendsto_integral_filter_of_dominated_convergence D
  · exact Filter.Eventually.of_forall (fun δ => (density_continuous f α β δ r).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact ((hD p hp).1 δ hδ).1
  · exact hDi
  · exact Filter.Eventually.of_forall (density_tendsto f α β r)

theorem response_integral_tendsto (α β : ℝ) (r v : ℂ) (hβ : 0 < β)
    (ha : 0 < α*area r) (hc : 0 < α*area r-8*β*r.im^2) :
    Tendsto (fun δ => ∫ p, response f α β δ r v p ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ p, limitResponse f α β r v p ∂jointMeasure)) := by
  obtain ⟨D,hDi,_,hD⟩ := fixed_envelope f α β r v hβ ha hc
  apply tendsto_integral_filter_of_dominated_convergence D
  · exact Filter.Eventually.of_forall (fun δ => (response_continuous f α β δ r v).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    exact ((hD p hp).1 δ hδ).2
  · exact hDi
  · exact Filter.Eventually.of_forall (response_tendsto f α β r v)

#print axioms blockBound_envelope
#print axioms common_envelope
#print axioms fixed_envelope
#print axioms integrability
#print axioms density_integral_tendsto
#print axioms response_integral_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredIntegrals

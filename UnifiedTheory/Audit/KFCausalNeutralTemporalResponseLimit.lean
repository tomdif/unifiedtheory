/- A derived all-time neutral probability curve, its exact initial point
mass, and the limit of the actual linear-response integrals. This gives
subsequential probability dynamics, but not a closed classical force law. -/
import UnifiedTheory.Audit.KFCausalNeutralTemporalProbability
import UnifiedTheory.Audit.KFCausalNeutralInitialProbability
import UnifiedTheory.Audit.KFCausalNeutralResolventLinearLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralTemporalResponseLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve joint_equicontinuity)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability initial_probability_limit)
open UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl (speedConstant)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n : ℕ => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "M" => fun n : ℕ => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "L" => fun n : ℕ =>
  KFCausalDisplacedNeutralResolventDynamics.linearRate ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem response_integral_moving_limit (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ν : ℝ → ProbabilityMeasure ℝ)
    (hc : ∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (T V : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrtop : Tendsto r atTop atTop)
    (v b c : ℕ → ℝ) (hv : ∀ n, |v n| ≤ V)
    (hb : ∀ n, |b n-s| ≤ T) (hc' : ∀ n, |c n-s| ≤ T)
    (v₀ b₀ c₀ : ℝ) (hvlim : Tendsto v atTop (𝓝 v₀))
    (hblim : Tendsto b atTop (𝓝 b₀)) (hclim : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun n => ∫ t in b n..c n, L (φ n) (r n) t (v n)) atTop
      (𝓝 (charFun (ν c₀ : Measure ℝ) v₀-charFun (ν b₀ : Measure ℝ) v₀)) := by
  have he := joint_equicontinuity ε a hε ha m g k s p hm hg hk h hne hh hz
  have hleft := KFCausalCharacteristicCompactUniformity.moving_frequency_limit F he φ hφ
    (fun z : ℝ × ℝ => charFun (ν z.1 : Measure ℝ) z.2) hc
    (b₀,v₀) (fun n => (b n,v n)) (hblim.prodMk_nhds hvlim)
  have hright := KFCausalCharacteristicCompactUniformity.moving_frequency_limit F he φ hφ
    (fun z : ℝ × ℝ => charFun (ν z.1 : Measure ℝ) z.2) hc
    (c₀,v₀) (fun n => (c n,v n)) (hclim.prodMk_nhds hvlim)
  have herr := KFCausalNeutralResolventLinearLimit.residual_tendsto ε a hε ha m g k s p hm hg hk
    (fun n => h (φ n)) (fun n => hne (φ n)) (fun n => hh (φ n)) (hz.comp hφ.tendsto_atTop)
    T V r hr hrtop v b c hv hb hc'
  simpa only [KFCausalDisplacedNeutralResolventDynamics.residual,curve,sub_add_cancel,zero_add]
    using herr.add (hright.sub hleft)

theorem response_integral_limit (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ν : ℝ → ProbabilityMeasure ℝ)
    (hc : ∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrtop : Tendsto r atTop atTop) (v b c : ℝ) :
    Tendsto (fun n => ∫ t in b..c, L (φ n) (r n) t v) atTop
      (𝓝 (charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v)) :=
  response_integral_moving_limit ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ ν hc
    (|b-s|+|c-s|) |v| r hr hrtop (fun _ => v) (fun _ => b) (fun _ => c)
    (fun _ => le_rfl) (fun _ => by linarith [abs_nonneg (c-s)])
    (fun _ => by linarith [abs_nonneg (b-s)]) v b c
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds

theorem exists_probability_dynamics :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (fun n => F (φ n))
        (fun z => charFun (ν z.1 : Measure ℝ) z.2) atTop S) ∧
      (∀ T v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
        ‖charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v‖ ≤
          speedConstant ε a m g k s T p v*|c-b|) ∧
      (∀ u : ℕ → ℝ, ∀ t : ℝ, Tendsto u atTop (𝓝 t) →
        Tendsto (fun n => M (φ n) (u n)) atTop (𝓝 (ν t))) ∧
      (∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop atTop → ∀ v b c : ℝ,
        Tendsto (fun n => ∫ t in b..c, L (φ n) (r n) t v) atTop
          (𝓝 (charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v))) := by
  obtain ⟨φ,hφ,ν,hν,hc,hu,hl,hw⟩ :=
    KFCausalNeutralTemporalProbability.exists_probability_curve ε a hε ha m g k s p hm hg hk h hne hh hz
  refine ⟨φ,hφ,ν,hν,?_,hc,hu,hl,hw,?_⟩
  · exact tendsto_nhds_unique (hw (fun _ => s) s tendsto_const_nhds)
      ((initial_probability_limit ε a hε ha m g k s p h hne hh hz).comp hφ.tendsto_atTop)
  · exact response_integral_limit ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ ν hc

#print axioms response_integral_moving_limit
#print axioms response_integral_limit
#print axioms exists_probability_dynamics
end
end UnifiedTheory.Audit.KFCausalNeutralTemporalResponseLimit

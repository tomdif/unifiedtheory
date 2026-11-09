/- One subsequence of the actual neutral-position characteristics
converges at all real times and frequencies, uniformly on compact sets.
The limit is continuous; no derivative or classical dynamics is asserted. -/
import UnifiedTheory.Audit.KFCausalJointCharacteristicModulus
import UnifiedTheory.Audit.KFCausalNeutralPositionFrequencyControl
import UnifiedTheory.Audit.KFCausalNeutralPositionTimeContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionTemporalCompactness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
open UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

section Fixed
variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)

def curve (z : ℝ × ℝ) : ℂ :=
  charFun (snapshot ε a h hε ha hne hh m g k s p z.1 : Measure ℝ) z.2

theorem curve_bound (z : ℝ × ℝ) : ‖curve ε a h hε ha hne hh m g k s p z‖ ≤ 1 :=
  norm_charFun_le_one _

theorem curve_zero (t : ℝ) : curve ε a h hε ha hne hh m g k s p (t,0) = 1 := by
  simp [curve]
end Fixed

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem joint_equicontinuity : EventuallyLocallyEquicontinuous F := by
  apply KFCausalJointCharacteristicModulus.joint_equicontinuity F s
  · intro T η hη
    simpa only [curve,snapshot_characteristic] using
      KFCausalNeutralPositionFrequencyControl.frequency_window ε a hε ha m g k s p
        hm hg hk h hne hh hz T η hη
  · intro T v η hη
    obtain ⟨ρ,hρ,N,hN⟩ := KFCausalNeutralPositionTimeContinuity.time_equicontinuity
      ε a hε ha m g k s p hm hg hk h hne hh hz T |v| η hη
    refine ⟨ρ,hρ,N,?_⟩
    intro n hn b c hb hc hbc
    simpa only [curve,snapshot_characteristic] using hN n hn v b c le_rfl hb hc hbc

theorem limit_time_modulus (φ : ℕ → ℕ) (hφ : StrictMono φ) (χ : ℝ × ℝ → ℂ)
    (hc : ∀ z, Tendsto (fun n => F (φ n) z) atTop (𝓝 (χ z)))
    (T V η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v b c : ℝ, |v| ≤ V → |b-s| ≤ T → |c-s| ≤ T → |c-b| < ρ →
      ‖χ (c,v)-χ (b,v)‖ < η := by
  obtain ⟨ρ,hρ,N,hN⟩ := KFCausalNeutralPositionTimeContinuity.time_equicontinuity
    ε a hε ha m g k s p hm hg hk h hne hh hz T V (η/2) (by positivity)
  refine ⟨ρ,hρ,?_⟩
  intro v b c hv hb hc' hbc
  have hbound : ‖χ (c,v)-χ (b,v)‖ ≤ η/2 := by
    apply le_of_tendsto (((hc (c,v)).sub (hc (b,v))).norm)
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [curve,snapshot_characteristic] using
      (hN (φ n) (hn.trans (hφ.id_le n)) v b c hv hb hc' hbc).le
  linarith

theorem exists_characteristic_limit :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : ℝ × ℝ → ℂ,
      Continuous χ ∧ (∀ z, ‖χ z‖ ≤ 1) ∧ (∀ t, χ (t,0) = 1) ∧
      (∀ z, Tendsto (fun n => F (φ n) z) atTop (𝓝 (χ z))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (fun n => F (φ n)) χ atTop S) ∧
      (∀ T V η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ v b c : ℝ,
        |v| ≤ V → |b-s| ≤ T → |c-s| ≤ T → |c-b| < ρ → ‖χ (c,v)-χ (b,v)‖ < η) := by
  have he := joint_equicontinuity ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨φ,hφ,χ,hχ,hc,hb⟩ := exists_continuous_subsequence F
    (fun n z => curve_bound ε a (h n) hε ha (hne n) (hh n) m g k s p z) he
  refine ⟨φ,hφ,χ,hχ,hb,?_,hc,?_,?_⟩
  · intro t
    have ht := hc (t,0)
    simp only [curve_zero] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  · exact compact_uniform_convergence F he φ hφ χ hc
  · exact limit_time_modulus ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ χ hc

#print axioms curve_bound
#print axioms curve_zero
#print axioms joint_equicontinuity
#print axioms limit_time_modulus
#print axioms exists_characteristic_limit

end
end UnifiedTheory.Audit.KFCausalNeutralPositionTemporalCompactness

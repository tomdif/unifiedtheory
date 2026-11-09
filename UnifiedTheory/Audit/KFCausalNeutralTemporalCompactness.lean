/- One subsequence of actual neutral characteristics converges jointly in
all real times and frequencies, uniformly on compact sets. The limit
retains the derived finite-window time Lipschitz bound. -/
import UnifiedTheory.Audit.KFCausalJointCharacteristicEquicontinuity
import UnifiedTheory.Audit.KFCausalNeutralCharacteristicControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState_norm)
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
open UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity
open UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl (speedConstant speedConstant_nonneg)

section Fixed
variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)

def curve (z : ℝ × ℝ) : ℂ :=
  KFCausalDisplacedNeutralDynamics.characteristic ε a h hε ha hne hh m g k s p z.2 z.1

theorem curve_bound (z : ℝ × ℝ) : ‖curve ε a h hε ha hne hh m g k s p z‖ ≤ 1 :=
  KFCausalDisplacedNeutralDynamics.characteristic_bound ε a h hε ha hne hh m g k s p z.2 z.1

theorem curve_zero (t : ℝ) : curve ε a h hε ha hne hh m g k s p (t,0) = 1 :=
  KFCausalNeutralCharacteristicControl.characteristic_zero h _
    (evolvedState_norm ε a h hε ha hne hh m g k s p t)
end Fixed

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n : ℕ => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem joint_equicontinuity : EventuallyLocallyEquicontinuous F := by
  apply KFCausalJointCharacteristicEquicontinuity.joint_equicontinuity F s
  · intro T η hη
    exact KFCausalNeutralCharacteristicControl.frequency_window ε a hε ha m g k s p
      hm.le hg.le hk.le h hne hh hz T η hη
  · intro T v
    refine ⟨speedConstant ε a m g k s T p v,speedConstant_nonneg ε a m g k s T p v,?_⟩
    filter_upwards [KFCausalDisplacedNeutralTimeControl.characteristic_window_lipschitz
      ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
    intro t u ht hu
    exact hn v u t hu ht

theorem limit_time_lipschitz (φ : ℕ → ℕ) (hφ : StrictMono φ) (χ : ℝ × ℝ → ℂ)
    (hc : ∀ z, Tendsto (fun n => F (φ n) z) atTop (𝓝 (χ z)))
    (T v b c : ℝ) (hb : |b-s| ≤ T) (hc' : |c-s| ≤ T) :
    ‖χ (c,v)-χ (b,v)‖ ≤ speedConstant ε a m g k s T p v*|c-b| := by
  apply le_of_tendsto (((hc (c,v)).sub (hc (b,v))).norm)
  filter_upwards [hφ.tendsto_atTop.eventually
    (KFCausalDisplacedNeutralTimeControl.characteristic_window_lipschitz
      ε a hε ha m g k s p hm hg hk h hne hh hz T)] with n hn
  exact hn v b c hb hc'

theorem exists_characteristic_limit :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ : ℝ × ℝ → ℂ,
      Continuous χ ∧ (∀ z, ‖χ z‖ ≤ 1) ∧ (∀ t, χ (t,0) = 1) ∧
      (∀ z, Tendsto (fun n => F (φ n) z) atTop (𝓝 (χ z))) ∧
      (∀ S, IsCompact S → TendstoUniformlyOn (fun n => F (φ n)) χ atTop S) ∧
      (∀ T v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
        ‖χ (c,v)-χ (b,v)‖ ≤ speedConstant ε a m g k s T p v*|c-b|) := by
  have he := joint_equicontinuity ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨φ,hφ,χ,hχ,hc,hb⟩ := exists_continuous_subsequence F
    (fun n z => curve_bound ε a (h n) hε ha (hne n) (hh n) m g k s p z) he
  refine ⟨φ,hφ,χ,hχ,hb,?_,hc,?_,?_⟩
  · intro t
    have ht := hc (t,0)
    simp only [curve_zero] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  · exact compact_uniform_convergence F he φ hφ χ hc
  · exact limit_time_lipschitz ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ χ hc

#print axioms curve_bound
#print axioms curve_zero
#print axioms joint_equicontinuity
#print axioms limit_time_lipschitz
#print axioms exists_characteristic_limit
end
end UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness

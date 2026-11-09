/- The cutoff may tend to infinity while the final time tends to any
fixed time. Scalar time-regularity and the pairing against the limiting
form state give strong convergence without assuming a norm modulus. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRealConvergence
import UnifiedTheory.Audit.KFCausalNormPairingStrongLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedJointTimeLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakPairing
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRealConvergence
open UnifiedTheory.Audit.KFCausalDenseIsometryLimit
open UnifiedTheory.Audit.KFCausalNormPairingStrongLimit

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "A" => approximation ε hε hbar hh hbound mass2 quartic vacuum
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum

theorem approximation_norm (a s t : ℝ) (f : Hilbert) : ‖A a s t f‖ = ‖f‖ := by
  by_cases ha : 0 < a
  · rw [approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum a ha]
    exact dynamics_norm ε hε hbar hh hbound mass2 quartic vacuum a ha s t f
  · simp only [approximation,dif_neg ha,ContinuousLinearMap.one_apply]

theorem moving_pairing_tendsto (s t : ℝ)
    (w v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Tendsto (fun p : ℝ × ℝ => inner ℂ (A p.1 s p.2 (J w)) (J v))
      (atTop ×ˢ 𝓝 t) (𝓝 (inner ℂ (U s t (J w)) (J v))) := by
  have ht : Tendsto (fun p : ℝ × ℝ => p.2) ((atTop : Filter ℝ) ×ˢ 𝓝 t) (𝓝 t) := tendsto_snd
  have hpos : ∀ᶠ p : ℝ × ℝ in (atTop ×ˢ 𝓝 t), 0 < p.1 :=
    tendsto_fst.eventually (eventually_gt_atTop (0:ℝ))
  have hw : ∀ᶠ z in 𝓝 t, |z| ≤ |t|+1 := by
    have he := (continuous_abs.tendsto t).eventually
      (gt_mem_nhds (show |t| < |t|+1 from by linarith))
    exact he.mono fun z hz => hz.le
  have hb : ∀ᶠ p : ℝ × ℝ in (atTop ×ˢ 𝓝 t),
      ‖inner ℂ (A p.1 s p.2 (J w)) (J v)-inner ℂ (A p.1 s t (J w)) (J v)‖ ≤
      pairingBound ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w v * |p.2-t| := by
    filter_upwards [hpos,ht.eventually hw] with p hp hpw
    have he := weak_pairing_lipschitz ε hε hbar hh hbound mass2 quartic vacuum p.1 hp
      s (|t|+1) t p.2 (by positivity) (by linarith) hpw w v
    simpa only [approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum p.1 hp] using he
  have hc : Tendsto (fun p : ℝ × ℝ =>
      pairingBound ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w v * |p.2-t|)
      (atTop ×ˢ 𝓝 t) (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_zero] using
      ((ht.sub_const t).abs).const_mul (pairingBound ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w v)
  have hn := squeeze_zero' (Eventually.of_forall (fun p : ℝ × ℝ => norm_nonneg
    (inner ℂ (A p.1 s p.2 (J w)) (J v)-inner ℂ (A p.1 s t (J w)) (J v)))) hb hc
  have hz := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hf := ((dynamics_strong_limit ε hε hbar hh hbound mass2 quartic vacuum s t (J w)).comp
    (show Tendsto (fun p : ℝ × ℝ => p.1) (atTop ×ˢ 𝓝 t) atTop from tendsto_fst)).inner
      (𝕜 := ℂ) (tendsto_const_nhds (x := J v))
  simpa only [Function.comp_apply,sub_add_cancel,zero_add] using hz.add hf

theorem dynamics_joint_time_limit_form (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Tendsto (fun p : ℝ × ℝ => A p.1 s p.2 (J w))
      (atTop ×ˢ 𝓝 t) (𝓝 (U s t (J w))) := by
  let v := formFlow ε hε hbar hh hbound mass2 quartic vacuum s t w
  have hv : J v = U s t (J w) :=
    (evolution_embedding ε hε hbar hh hbound mass2 quartic vacuum s t w).symm
  have hp := moving_pairing_tendsto ε hε hbar hh hbound mass2 quartic vacuum s t w v
  have hp' : Tendsto (fun p : ℝ × ℝ => inner ℂ (A p.1 s p.2 (J w)) (U s t (J w)))
      (atTop ×ˢ 𝓝 t) (𝓝 (inner ℂ (U s t (J w)) (U s t (J w)))) :=
    (congrArg (fun y : Hilbert => Tendsto
      (fun p : ℝ × ℝ => inner ℂ (A p.1 s p.2 (J w)) y)
      (atTop ×ˢ 𝓝 t) (𝓝 (inner ℂ (U s t (J w)) y))) hv).mp hp
  have hn : Tendsto (fun p : ℝ × ℝ => ‖A p.1 s p.2 (J w)‖)
      (atTop ×ˢ 𝓝 t) (𝓝 ‖U s t (J w)‖) := by
    simpa only [approximation_norm,evolution_norm] using
      (tendsto_const_nhds (x := ‖J w‖) (f := (atTop : Filter ℝ) ×ˢ 𝓝 t))
  exact strong_of_norm_and_pairing hn hp'

theorem dynamics_joint_time_limit (s t : ℝ) (f : Hilbert) :
    Tendsto (fun p : ℝ × ℝ => A p.1 s p.2 f) (atTop ×ˢ 𝓝 t) (𝓝 (U s t f)) := by
  apply tendsto_of_dense_isometries (J) (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (fun p : ℝ × ℝ => A p.1 s p.2) (U s t)
    (fun p => approximation_isometry ε hε hbar hh hbound mass2 quartic vacuum p.1 s p.2)
    (U s t).isometry (atTop ×ˢ 𝓝 t) _ f
  exact dynamics_joint_time_limit_form ε hε hbar hh hbound mass2 quartic vacuum s t

#print axioms approximation_norm
#print axioms moving_pairing_tendsto
#print axioms dynamics_joint_time_limit_form
#print axioms dynamics_joint_time_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedJointTimeLimit

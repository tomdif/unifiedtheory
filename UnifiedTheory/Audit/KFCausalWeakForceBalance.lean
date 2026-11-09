/- A finite-mass bound and the original Fourier response balance pass to
the local force limit as an integrated continuity equation on Schwartz tests. -/
import UnifiedTheory.Audit.KFCausalSchwartzForceFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalWeakForceBalance
noncomputable section
open MeasureTheory Filter SchwartzMap
open scoped Topology FourierTransform ZeroAtInfty
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalSchwartzForceFourier

theorem force_fourier_bound (F : FluxPair) (v : ℝ) : ‖F.fourier v‖ ≤ F.mass/2 := by
  have hp := norm_charFun_le (μ := F.positive) v
  have hn := norm_charFun_le (μ := F.negative) v
  have hs := norm_sub_le (charFun F.positive v) (charFun F.negative v)
  simp only [FluxPair.fourier,norm_div]
  norm_num only [Complex.norm_ofNat]
  dsimp only [FluxPair.mass]
  linarith

theorem force_fourier_measurable (F : FluxPair) : Measurable F.fourier :=
  (measurable_charFun.sub measurable_charFun).div_const 2

variable (F : ℕ → FluxPair) (J : FluxPair)
  (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (hb : ∃ C : ℝ, ∀ᶠ n in atTop, (F n).mass ≤ C)
  (hl : ∀ q : C₀(ℝ,ℂ), Tendsto (fun n => (F n).evaluate q.toBCF) atTop
    (𝓝 (J.evaluate q.toBCF)))
  (hf : ∀ v : ℝ, Tendsto (fun n => Complex.I*(v:ℂ)*(F n).fourier v) atTop
    (𝓝 (charFun ν v-charFun μ v)))

include hb hf in
theorem fourier_test_limit (f : 𝓢(ℝ,ℂ)) :
    Tendsto (fun n => (F n).evaluate (derivCLM ℂ ℂ (𝓕 f)).toBoundedContinuousFunction)
      atTop (𝓝 ((∫ p, (𝓕 f) p ∂ν)-(∫ p, (𝓕 f) p ∂μ))) := by
  obtain ⟨C,hC⟩ := hb
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := atTop)
    (F := fun n v => multiplier f v * (F n).fourier (frequency v))
    (f := fun v => f v * (charFun ν (frequency v)-charFun μ (frequency v)))
    (fun v => ‖multiplier f v‖ * (C/2))
    (Eventually.of_forall (fun n => (multiplier f).continuous.aestronglyMeasurable.mul
      (((force_fourier_measurable (F n)).comp
        (show Measurable frequency by unfold frequency; fun_prop)).aestronglyMeasurable)))
    (hC.mono (fun n hn => ae_of_all _ (fun v => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((force_fourier_bound (F n) (frequency v)).trans (by linarith)) (norm_nonneg _))))
    ((multiplier f).integrable.norm.mul_const (C/2))
    (ae_of_all _ (fun v => by
      simpa only [multiplier_apply,mul_assoc] using (hf (frequency v)).const_mul (f v)))
  simp only [← force_fourier_pairing,← derivative_fourier] at hlim
  rw [integral_congr_ae (ae_of_all _ (fun v => mul_sub (f v) _ _)),
    integral_sub (characteristic_test_integrable ν f) (characteristic_test_integrable μ f),
    ← measure_fourier_pairing,← measure_fourier_pairing] at hlim
  exact hlim

include hb hl hf in
theorem schwartz_balance (f : 𝓢(ℝ,ℂ)) :
    (∫ p, f p ∂ν)-(∫ p, f p ∂μ) =
      J.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction := by
  have ha := fourier_test_limit F μ ν hb hf (𝓕⁻ f)
  simp only [FourierTransform.fourier_fourierInv_eq] at ha
  have he := hl (derivCLM ℂ ℂ f).toZeroAtInfty
  exact tendsto_nhds_unique ha he

include hb hf in
theorem exists_local_balance :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ J : FluxPair,
      (∀ q : C₀(ℝ,ℂ), Tendsto (fun n => (F (φ n)).evaluate q.toBCF) atTop
        (𝓝 (J.evaluate q.toBCF))) ∧
      (∀ f : 𝓢(ℝ,ℂ), (∫ p, f p ∂ν)-(∫ p, f p ∂μ) =
        J.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) := by
  obtain ⟨φ,hφ,P,N,hP,hN,_⟩ :=
    KFCausalLocalForceMeasure.local_pair_subsequence (fun n (_ : Unit) => F n) (fun _ => hb)
  let J := KFCausalLocalForceMeasure.finitePair (P ()) (N ())
  have hj (q : C₀(ℝ,ℂ)) : Tendsto (fun n => (F (φ n)).evaluate q.toBCF) atTop
      (𝓝 (J.evaluate q.toBCF)) :=
    KFCausalVanishingForceTests.zero_test_of_compact_limits (fun n => F (φ n))
      (P ()) (N ()) (hP ()) (hN ()) q
  refine ⟨φ,hφ,J,hj,?_⟩
  apply schwartz_balance (fun n => F (φ n)) J μ ν _ hj
    (fun v => (hf v).comp hφ.tendsto_atTop)
  obtain ⟨C,hC⟩ := hb
  exact ⟨C,hφ.tendsto_atTop.eventually hC⟩

#print axioms force_fourier_bound
#print axioms force_fourier_measurable
#print axioms fourier_test_limit
#print axioms schwartz_balance
#print axioms exists_local_balance
end
end UnifiedTheory.Audit.KFCausalWeakForceBalance

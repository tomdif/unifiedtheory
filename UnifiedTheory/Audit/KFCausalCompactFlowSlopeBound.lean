/- A compactly supported C1 function along a continuous reversible flow
has locally uniformly supported and bounded time derivatives. The mean
value theorem gives a compact L2 majorant for its difference quotients. -/
import UnifiedTheory.Audit.KFCausalDominatedL2Derivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalCompactFlowSlopeBound
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tube (Φ : ℝ → E → E) (f : E → ℂ) : Set E :=
  (fun p : ℝ × E => Φ (-p.1) p.2) '' (Icc (-1:ℝ) 1 ×ˢ tsupport f)

omit [NormedSpace ℝ E] in
theorem tube_compact (Φ : ℝ → E → E) (hΦ : Continuous (fun p : ℝ × E => Φ p.1 p.2))
    (f : E → ℂ) (hf : HasCompactSupport f) : IsCompact (tube Φ f) :=
  (isCompact_Icc.prod hf).image (hΦ.comp (continuous_fst.neg.prodMk continuous_snd))

def orbitDerivative (Φ : ℝ → E → E) (v : E → E) (f : E → ℂ) (t : ℝ) (x : E) : ℂ :=
  (fderiv ℝ f (Φ t x)) (v (Φ t x))

theorem derivative_outside_tube (Φ : ℝ → E → E)
    (hr : ∀ t x, Φ (-t) (Φ t x) = x) (v : E → E) (f : E → ℂ)
    (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) (x : E) (hx : x ∉ tube Φ f) :
    orbitDerivative Φ v f t x = 0 := by
  have hn : Φ t x ∉ tsupport f := by
    intro hf
    exact hx ⟨(t,Φ t x),⟨ht,hf⟩,hr t x⟩
  rw [orbitDerivative,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]

theorem derivative_bound (Φ : ℝ → E → E)
    (hΦ : Continuous (fun p : ℝ × E => Φ p.1 p.2))
    (hr : ∀ t x, Φ (-t) (Φ t x) = x) (v : E → E) (hv : Continuous v)
    (f : E → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (-1:ℝ) 1, ∀ x,
      ‖orbitDerivative Φ v f t x‖ ≤ (tube Φ f).indicator (fun _ => M) x := by
  have hd : Continuous (fun p : ℝ × E => orbitDerivative Φ v f p.1 p.2) :=
    ((hf.continuous_fderiv (by norm_num)).comp hΦ).clm_apply (hv.comp hΦ)
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (tube_compact Φ hΦ f hc)).exists_bound_of_continuousOn hd.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro t ht x
  by_cases hx : x ∈ tube Φ f
  · rw [indicator_of_mem hx]
    exact (hB (t,x) ⟨ht,hx⟩).trans (le_max_left _ _)
  · rw [indicator_of_notMem hx,derivative_outside_tube Φ hr v f t ht x hx,norm_zero]

theorem slope_bound (Φ : ℝ → E → E) (v : E → E) (f : E → ℂ)
    (hf : Differentiable ℝ f)
    (hd : ∀ t x, HasDerivAt (fun s => Φ s x) (v (Φ t x)) t)
    (M : ℝ) (hb : ∀ t ∈ Icc (-1:ℝ) 1, ∀ x,
      ‖orbitDerivative Φ v f t x‖ ≤ (tube Φ f).indicator (fun _ => M) x)
    (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) (hnt : t ≠ 0) (x : E) :
    ‖t⁻¹ • (f (Φ t x)-f (Φ 0 x))‖ ≤ (tube Φ f).indicator (fun _ => M) x := by
  have hs := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := (0:ℝ)) (y := t)
    (f := fun s => f (Φ s x)) (f' := fun s => orbitDerivative Φ v f s x)
    (fun s _ => ((hf (Φ s x)).hasFDerivAt.comp_hasDerivAt s (hd s x)).hasDerivWithinAt)
    (fun s h => hb s h x) (convex_Icc (-1:ℝ) 1) (by constructor <;> norm_num) ht
  rw [sub_zero] at hs
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  have hn : 0 < |t| := abs_pos.mpr hnt
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
  have he : |t|⁻¹*((tube Φ f).indicator (fun _ => M) x*‖t‖) =
      (tube Φ f).indicator (fun _ => M) x := by
    rw [Real.norm_eq_abs,mul_left_comm,inv_mul_cancel₀ hn.ne',mul_one]
  rw [he] at hh
  exact hh

def initialDerivative (v : E → E) (f : E → ℂ) (x : E) : ℂ := (fderiv ℝ f x) (v x)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

theorem initial_memLp (v : E → E) (hv : Continuous v) (f : E → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) : MemLp (initialDerivative v f) 2 μ := by
  have hs : HasCompactSupport (initialDerivative v f) := by
    apply hc.mono'
    intro x hx
    by_contra hn
    exact hx (by simp only [initialDerivative,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply])
  exact ((hf.continuous_fderiv (by norm_num)).clm_apply hv).memLp_of_hasCompactSupport hs

theorem strong_derivative (Φ : ℝ → E → E)
    (hΦ : Continuous (fun p : ℝ × E => Φ p.1 p.2))
    (h0 : ∀ x, Φ 0 x = x) (hr : ∀ t x, Φ (-t) (Φ t x) = x)
    (v : E → E) (hv : Continuous v)
    (hd : ∀ t x, HasDerivAt (fun s => Φ s x) (v (Φ t x)) t)
    (f : E → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (u : ℝ → Lp ℂ 2 μ) (hu : ∀ t, u t =ᵐ[μ] fun x => f (Φ t x)) :
    HasDerivAt u ((initial_memLp μ v hv f hf hc).toLp (initialDerivative v f)) 0 := by
  obtain ⟨M,_,hM⟩ := derivative_bound Φ hΦ hr v hv f hf hc
  let b := (tube Φ f).indicator (fun _ => M)
  have hK := tube_compact Φ hΦ f hc
  have hb : MemLp b 2 μ := memLp_indicator_const 2 hK.measurableSet M (Or.inr hK.measure_lt_top.ne)
  have hb2 : Integrable (fun x => b x^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  apply KFCausalDominatedL2Derivative.hasDerivAt_represented u (fun t x => f (Φ t x)) hu
    (initialDerivative v f) (initial_memLp μ v hv f hf hc) b hb2
  · have hI : ∀ᶠ t in 𝓝[≠] (0:ℝ), t ∈ Ioo (-1:ℝ) 1 :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hI,self_mem_nhdsWithin] with t ht hnt
    exact Eventually.of_forall (fun x => slope_bound Φ v f (hf.differentiable (by norm_num)) hd
      M hM t ⟨ht.1.le,ht.2.le⟩ (by simpa only [mem_compl_iff,mem_singleton_iff] using hnt) x)
  · exact Eventually.of_forall (fun x => by
      simpa only [h0,initialDerivative] using
        ((hf.differentiable (by norm_num)) (Φ 0 x)).hasFDerivAt.comp_hasDerivAt 0 (hd 0 x))

#print axioms tube_compact
#print axioms derivative_outside_tube
#print axioms derivative_bound
#print axioms slope_bound
#print axioms initial_memLp
#print axioms strong_derivative
end
end UnifiedTheory.Audit.KFCausalCompactFlowSlopeBound

/-
  Audit/KFCausalMinkowski4DVarianceRate.lean — THE DIAGONAL VARIANCE RATE
  (fluctuation campaign, rung b: the masses and the generic substitution)

  The diagonal (Campbell) variance object at profile level is
  `√a·∬ (v−u)²·f4Dsq(au²v²)·F`.  Splitting `(v−u)² = u² + v² − 2uv`:
  the square channels converge to the fluctuation w-mass `(315/4)√π` times the
  edge integrals `∫u·F(u,0)du`, `∫v·F(0,v)dv`; the cross channel dies as
  `ln a/√a`.  This file provides the kernel-agnostic substitution and the
  `f4Dsq` masses; the channel limits and assembly follow.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder
import UnifiedTheory.Audit.KFCausalMinkowski4DLogRate
import UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
import UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
open UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction

namespace UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate

/-- The kernel-agnostic boost substitution (the `inner_sub` mechanism is pure
change of variables — no property of the kernel is used). -/
theorem inner_sub_generic (h : ℝ → ℝ) (G : ℝ → ℝ) (a u : ℝ)
    (ha : 0 < a) (hu : 0 < u) :
    Real.sqrt a * ∫ v in Ioi (0:ℝ), h (a*u^2*v^2) * G v
      = u⁻¹ * ∫ w in Ioi (0:ℝ), h (w^2) * G (w/(Real.sqrt a * u)) := by
  set c := Real.sqrt a * u with hcdef
  have hc : 0 < c := mul_pos (Real.sqrt_pos.mpr ha) hu
  have hc2 : c^2 = a * u^2 := by rw [hcdef, mul_pow, Real.sq_sqrt ha.le]
  have hcomp := integral_comp_mul_left_Ioi
    (fun w => h (w^2) * G (w/c)) 0 hc
  rw [mul_zero, smul_eq_mul] at hcomp
  have hcancel : (∫ x in Ioi (0:ℝ), (fun w => h (w^2) * G (w/c)) (c * x))
      = ∫ x in Ioi (0:ℝ), h (a*u^2*x^2) * G x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    show h ((c*x)^2) * G ((c*x)/c) = h (a*u^2*x^2) * G x
    rw [mul_div_cancel_left₀ x hc.ne', mul_pow, hc2]
  rw [hcancel] at hcomp
  dsimp only at hcomp
  rw [hcomp, hcdef]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp
  try ring

/-- `f4Dsq(w²)` is integrable on `(0,∞)` (Gaussian-type decay). -/
theorem f4Dsq_sq_integrable :
    IntegrableOn (fun w => f4Dsq (w^2)) (Ioi (0:ℝ)) := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ (0:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (0:ℝ))).integrableOn
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (2:ℝ))).integrableOn
  have h4 : IntegrableOn (fun x : ℝ => x ^ (4:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (4:ℝ))).integrableOn
  have h6 : IntegrableOn (fun x : ℝ => x ^ (6:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (6:ℝ))).integrableOn
  have hsum := ((h0.const_mul 1).add ((h2.const_mul 81).add
    ((h4.const_mul 128).add (h6.const_mul (32/3)))))
  apply MeasureTheory.IntegrableOn.congr_fun hsum ?_ measurableSet_Ioi
  intro w hw
  rw [mem_Ioi] at hw
  have e0 : w ^ (0:ℝ) = 1 := Real.rpow_zero w
  have e2 : w ^ (2:ℝ) = w ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have e4 : w ^ (4:ℝ) = w ^ 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have e6 : w ^ (6:ℝ) = w ^ 6 := by
    rw [show (6:ℝ) = ((6:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  simp only [Pi.add_apply]
  rw [e0, e2, e4, e6]
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
  rw [show -(w^2) = -(1:ℝ) * w^2 from by ring]
  ring

/-- **The fluctuation w-mass**: `∫₀^∞ f4Dsq(w²) dw = (315/4)·√π` — one half of
the (nonzero!) Mellin mass at `s = ½`. -/
theorem f4Dsq_w_mass :
    (∫ w in Ioi (0:ℝ), f4Dsq (w^2)) = (315/4) * Real.sqrt π := by
  have hsub := integral_comp_rpow_Ioi
    (fun ξ => ξ ^ ((1:ℝ)/2 - 1) * f4Dsq ξ) (p := 2) (by norm_num)
  rw [f4Dsq_mass_half] at hsub
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      ((fun ξ => ξ ^ ((1:ℝ)/2 - 1) * f4Dsq ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 2 * f4Dsq (x^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [smul_eq_mul]
    have h21 : x ^ ((2:ℝ)-1) = x := by
      rw [show (2:ℝ)-1 = (1:ℝ) from by norm_num, Real.rpow_one]
    have hpow : (x ^ (2:ℝ)) ^ ((1:ℝ)/2 - 1) = x⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt hx),
        show (2:ℝ) * ((1:ℝ)/2 - 1) = -1 from by norm_num, Real.rpow_neg_one]
    have hx2 : x ^ (2:ℝ) = x^2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    rw [h21, hpow, hx2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp
  rw [key, integral_const_mul] at hsub
  linarith [hsub]

/-- **THE NO-SELF-AVERAGING THEOREM** (universal fluctuation no-go).  For ANY
layer weights with nonvanishing zeroth weight — and the zeroth weight is
forced by the mean's normalization (`layer_uniqueness`) — the variance
kernel's Mellin mass at the critical point `s = ½` is strictly positive:

    M[e^{−ξ}(w₀² + w₁²ξ + (w₂²/2)ξ² + (w₃²/6)ξ³)](½) > 0.

The mean's convergence REQUIRED zeros at `s = ½, 1, 3/2`, achievable only with
signed weights; the variance kernel's coefficients are squares, so its mass
CANNOT vanish — for any weights, in any layer scheme.  With `log_rate`, the
Campbell term of every layer-weighted causal-set d'Alembertian diverges
logarithmically: an intermediate nonlocality (damping) scale is NECESSARY,
not a modeling choice.  Positivity forbids sitting on the critical line. -/
theorem no_self_averaging (w₀ w₁ w₂ w₃ : ℝ) (hw : w₀ ≠ 0) :
    0 < ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) *
      (Real.exp (-ξ) * (w₀^2 + w₁^2 * ξ + (w₂^2/2) * ξ^2 + (w₃^2/6) * ξ^3)) := by
  rw [generic_mellin (1/2) one_half_pos (w₀^2) (w₁^2) (w₂^2) (w₃^2)]
  have g0 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2)
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2 + 1)
  have g2 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2 + 2)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/2 + 3)
  have h0 : 0 < w₀^2 * Real.Gamma (1/2) :=
    mul_pos (by positivity) g0
  have h1 : 0 ≤ w₁^2 * Real.Gamma (1/2 + 1) :=
    mul_nonneg (sq_nonneg _) (le_of_lt g1)
  have h2 : 0 ≤ (w₂^2/2) * Real.Gamma (1/2 + 2) :=
    mul_nonneg (by positivity) (le_of_lt g2)
  have h3 : 0 ≤ (w₃^2/6) * Real.Gamma (1/2 + 3) :=
    mul_nonneg (by positivity) (le_of_lt g3)
  linarith

/-- **THE NO-SELF-AVERAGING THEOREM, GCB CLASS** — the quantifier that matters.
For an ARBITRARY finite family of layer weights (the class containing the
Aslanbeigi–Saravani–Sorkin Generalized Causet Box operators), if any weight is
nonzero then the variance kernel's Mellin mass at the critical point is
strictly positive:

    M[e^{−ξ}·Σₙ wₙ²·ξⁿ/n!](½)  =  Σₙ wₙ²·Γ(n+½)/n!  >  0.

No choice of coefficients — including every GCB member — evades the
fluctuation divergence: squares against positive Γ-values cannot vanish. -/
theorem no_self_averaging_GCB (N : ℕ) (w : ℕ → ℝ)
    (hw : ∃ n, n < N ∧ w n ≠ 0) :
    0 < ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) *
      (Real.exp (-ξ) * ∑ n ∈ Finset.range N,
        (w n)^2 * ξ ^ n / (Nat.factorial n : ℝ)) := by
  -- per-term evaluation: the (n + ½)-moment of the exponential
  have hterm : ∀ n : ℕ, (∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) *
      (Real.exp (-ξ) * ((w n)^2 * ξ ^ n / (Nat.factorial n : ℝ))))
      = (w n)^2 / (Nat.factorial n : ℝ) * Real.Gamma ((n:ℝ) + 1/2) := by
    intro n
    have hpos : (0:ℝ) < (n:ℝ) + 1/2 := by positivity
    rw [Real.Gamma_eq_integral hpos, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ hξ
    rw [mem_Ioi] at hξ
    have hmerge : ξ ^ ((1/2:ℝ) - 1) * ξ ^ n = ξ ^ (((n:ℝ) + 1/2) - 1) := by
      rw [← Real.rpow_natCast ξ n, ← Real.rpow_add hξ]
      congr 1
      ring
    dsimp only
    rw [← hmerge]
    ring
  -- per-term integrability
  have hint : ∀ n : ℕ, IntegrableOn (fun ξ => ξ ^ ((1/2:ℝ) - 1) *
      (Real.exp (-ξ) * ((w n)^2 * ξ ^ n / (Nat.factorial n : ℝ))))
      (Ioi (0:ℝ)) := by
    intro n
    have hpos : (0:ℝ) < (n:ℝ) + 1/2 := by positivity
    have hg := (Real.GammaIntegral_convergent hpos).const_mul
      ((w n)^2 / (Nat.factorial n : ℝ))
    apply MeasureTheory.IntegrableOn.congr_fun hg ?_ measurableSet_Ioi
    intro ξ hξ
    rw [mem_Ioi] at hξ
    have hmerge : ξ ^ ((1/2:ℝ) - 1) * ξ ^ n = ξ ^ (((n:ℝ) + 1/2) - 1) := by
      rw [← Real.rpow_natCast ξ n, ← Real.rpow_add hξ]
      congr 1
      ring
    dsimp only
    rw [← hmerge]
    ring
  -- expand the sum through the integral
  have hexpand : (∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) *
      (Real.exp (-ξ) * ∑ n ∈ Finset.range N,
        (w n)^2 * ξ ^ n / (Nat.factorial n : ℝ)))
      = ∑ n ∈ Finset.range N,
        (w n)^2 / (Nat.factorial n : ℝ) * Real.Gamma ((n:ℝ) + 1/2) := by
    rw [show (fun ξ => ξ ^ ((1/2:ℝ) - 1) *
        (Real.exp (-ξ) * ∑ n ∈ Finset.range N,
          (w n)^2 * ξ ^ n / (Nat.factorial n : ℝ)))
        = fun ξ => ∑ n ∈ Finset.range N, ξ ^ ((1/2:ℝ) - 1) *
          (Real.exp (-ξ) * ((w n)^2 * ξ ^ n / (Nat.factorial n : ℝ))) from by
      funext ξ
      rw [Finset.mul_sum, Finset.mul_sum]]
    rw [MeasureTheory.integral_finset_sum _ (fun n _ => hint n)]
    exact Finset.sum_congr rfl (fun n _ => hterm n)
  rw [hexpand]
  obtain ⟨n₀, hn₀, hw₀⟩ := hw
  apply Finset.sum_pos' ?_ ⟨n₀, Finset.mem_range.mpr hn₀, ?_⟩
  · intro n _
    have hg := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < (n:ℝ) + 1/2)
    positivity
  · have hg := Real.Gamma_pos_of_pos (by positivity : (0:ℝ) < (n₀:ℝ) + 1/2)
    have hfac : (0:ℝ) < (Nat.factorial n₀ : ℝ) := by positivity
    positivity

/-- `f4Dsq` is nonnegative — the variance kernel has a sign. -/
theorem f4Dsq_nonneg (ξ : ℝ) (hξ : 0 ≤ ξ) : 0 ≤ f4Dsq ξ := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
  have := Real.exp_pos (-ξ)
  positivity

/-- **The square-channel limit** (the u²-leg of the variance rate): after the
boost substitution, the channel converges to the fluctuation w-mass times the
u-edge integral:

    √a·∬ u²·f4Dsq(au²v²)·g  ⟶  (∫₀^∞ f4Dsq(w²)dw)·∫₀^∞ u·g(u,0) du. -/
theorem square_channel (g : ℝ → ℝ → ℝ) (Cg A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0) :
    Filter.Tendsto (fun a : ℝ => ∫ u in Ioi (0:ℝ), u * ∫ w in Ioi (0:ℝ),
        f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))
      Filter.atTop
      (𝓝 ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * ∫ u in Ioi (0:ℝ), u * g u 0)) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb 0 0)
  have hmw := f4Dsq_sq_integrable
  -- inner limit, per u > 0
  have hinner : ∀ u : ℝ, 0 < u → Filter.Tendsto (fun a : ℝ =>
      ∫ w in Ioi (0:ℝ), f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))
      Filter.atTop (𝓝 (∫ w in Ioi (0:ℝ), f4Dsq (w^2) * g u 0)) := by
    intro u hu
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun w => f4Dsq (w^2) * Cg)
    · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with a ha
      have hy : Measurable (fun w : ℝ => w/(Real.sqrt a * u)) := by fun_prop
      have hK : Continuous (fun w : ℝ => f4Dsq (w^2)) := by
        unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
        fun_prop
      exact (hK.measurable.mul (hgc.measurable.comp
        (measurable_const.prodMk hy))).aestronglyMeasurable
    · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with a ha
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (f4Dsq_nonneg _ (sq_nonneg w))]
      exact mul_le_mul_of_nonneg_left (hgb u _) (f4Dsq_nonneg _ (sq_nonneg w))
    · exact hmw.mul_const Cg
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      apply Filter.Tendsto.const_mul
      have harg : Filter.Tendsto (fun a : ℝ => w/(Real.sqrt a * u))
          Filter.atTop (𝓝 0) := by
        apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
        exact (Real.tendsto_sqrt_atTop.atTop_mul_const hu)
      have hcont : Continuous (fun y => g u y) :=
        hgc.comp (continuous_const.prodMk continuous_id)
      exact (hcont.tendsto 0).comp harg
  -- outer DCT over u
  have hDCT : Filter.Tendsto (fun a : ℝ => ∫ u in Ioi (0:ℝ), u *
      ∫ w in Ioi (0:ℝ), f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))
      Filter.atTop
      (𝓝 (∫ u in Ioi (0:ℝ), u * ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * g u 0))) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u => (Ioc (0:ℝ) A).indicator
        (fun _ => A * ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * Cg)) u)
    · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with a ha
      have hK : Continuous (fun w : ℝ => f4Dsq (w^2)) := by
        unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
        fun_prop
      have hFm : Measurable (Function.uncurry (fun u w =>
          f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))) := by
        have hy : Measurable (fun p : ℝ × ℝ => p.2/(Real.sqrt a * p.1)) := by
          fun_prop
        exact ((hK.measurable.comp measurable_snd).mul
          (hgc.measurable.comp (measurable_fst.prodMk hy)))
      exact (measurable_id.mul
        (hFm.stronglyMeasurable.integral_prod_right').measurable
        ).aestronglyMeasurable
    · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with a ha
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro u hu
      rw [mem_Ioi] at hu
      rcases le_or_gt u A with huA | huA
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu, huA⟩), Real.norm_eq_abs,
          abs_mul, abs_of_pos hu]
        have hib : |∫ w in Ioi (0:ℝ), f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
            ≤ (∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * Cg := by
          rw [← Real.norm_eq_abs, ← integral_mul_const]
          apply norm_integral_le_of_norm_le (hmw.mul_const Cg)
          apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
          intro w _
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (f4Dsq_nonneg _ (sq_nonneg w))]
          exact mul_le_mul_of_nonneg_left (hgb u _)
            (f4Dsq_nonneg _ (sq_nonneg w))
        calc u * |∫ w in Ioi (0:ℝ), f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
            ≤ u * ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * Cg) :=
              mul_le_mul_of_nonneg_left hib (le_of_lt hu)
          _ ≤ A * ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * Cg) := by
              apply mul_le_mul_of_nonneg_right huA
              have h1 : (0:ℝ) ≤ ∫ w in Ioi (0:ℝ), f4Dsq (w^2) :=
                MeasureTheory.setIntegral_nonneg measurableSet_Ioi
                  (fun w _ => f4Dsq_nonneg _ (sq_nonneg w))
              positivity
      · have hz : (∫ w in Ioi (0:ℝ),
            f4Dsq (w^2) * g u (w/(Real.sqrt a * u))) = 0 := by
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            (fun w _ => by rw [hsuppU u _ (le_of_lt huA), mul_zero]),
            MeasureTheory.integral_zero]
        rw [hz, mul_zero, norm_zero]
        apply Set.indicator_nonneg
        intro x _
        have h1 : (0:ℝ) ≤ ∫ w in Ioi (0:ℝ), f4Dsq (w^2) :=
          MeasureTheory.setIntegral_nonneg measurableSet_Ioi
            (fun w _ => f4Dsq_nonneg _ (sq_nonneg w))
        positivity
    · apply MeasureTheory.Integrable.integrableOn
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
      exact MeasureTheory.integrableOn_const
        (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro u hu
      rw [mem_Ioi] at hu
      have hlim := (hinner u hu).const_mul u
      have hval : (∫ w in Ioi (0:ℝ), f4Dsq (w^2) * g u 0)
          = (∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * g u 0 := by
        rw [← integral_mul_const]
      rw [hval] at hlim
      exact hlim
  have hfinal : (∫ u in Ioi (0:ℝ), u * ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * g u 0))
      = (∫ w in Ioi (0:ℝ), f4Dsq (w^2)) * ∫ u in Ioi (0:ℝ), u * g u 0 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  rwa [hfinal] at hDCT

/-- The quartic exponential lower bound (extends the cubic). -/
theorem exp_quartic_lower (z : ℝ) (hz : 0 ≤ z) :
    1 + z + z^2/2 + z^3/6 + z^4/24 ≤ Real.exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 5
  simp [Finset.sum_range_succ] at h
  nlinarith [h]

/-- The variance kernel is bounded: `f4Dsq ≤ 300` (coefficient-wise against
the quartic exponential). -/
theorem f4Dsq_le (ξ : ℝ) (hξ : 0 ≤ ξ) : f4Dsq ξ ≤ 300 := by
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
  have he := exp_quartic_lower ξ hξ
  have hep : 0 < Real.exp ξ := Real.exp_pos ξ
  rw [Real.exp_neg]
  rw [inv_mul_le_iff₀ hep]
  nlinarith [he, mul_nonneg hξ hξ, mul_nonneg (mul_nonneg hξ hξ) hξ,
    mul_nonneg (mul_nonneg (mul_nonneg hξ hξ) hξ) hξ]

/-- `w·f4Dsq(w²)` is integrable on `(0,∞)`. -/
theorem f4Dsq_w1_integrable :
    IntegrableOn (fun w => w * f4Dsq (w^2)) (Ioi (0:ℝ)) := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (1:ℝ))).integrableOn
  have h3 : IntegrableOn (fun x : ℝ => x ^ (3:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (3:ℝ))).integrableOn
  have h5 : IntegrableOn (fun x : ℝ => x ^ (5:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (5:ℝ))).integrableOn
  have h7 : IntegrableOn (fun x : ℝ => x ^ (7:ℝ) * Real.exp (-(1:ℝ) * x ^ 2))
      (Ioi 0) :=
    (integrable_rpow_mul_exp_neg_mul_sq one_pos
      (by norm_num : (-1:ℝ) < (7:ℝ))).integrableOn
  have hsum := ((h1.const_mul 1).add ((h3.const_mul 81).add
    ((h5.const_mul 128).add (h7.const_mul (32/3)))))
  apply MeasureTheory.IntegrableOn.congr_fun hsum ?_ measurableSet_Ioi
  intro w hw
  rw [mem_Ioi] at hw
  have e1 : w ^ (1:ℝ) = w := Real.rpow_one w
  have e3 : w ^ (3:ℝ) = w ^ 3 := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have e5 : w ^ (5:ℝ) = w ^ 5 := by
    rw [show (5:ℝ) = ((5:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  have e7 : w ^ (7:ℝ) = w ^ 7 := by
    rw [show (7:ℝ) = ((7:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  simp only [Pi.add_apply]
  rw [e1, e3, e5, e7]
  unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
  rw [show -(w^2) = -(1:ℝ) * w^2 from by ring]
  ring

/-- **The second fluctuation mass**: `∫₀^∞ w·f4Dsq(w²) dw = 201` — half the
`s = 1` Mellin value `402`. -/
theorem f4Dsq_w1_mass :
    (∫ w in Ioi (0:ℝ), w * f4Dsq (w^2)) = 201 := by
  have hM1 : (∫ ξ in Ioi (0:ℝ), f4Dsq ξ) = 402 := by
    have h := f4Dsq_mellin 1 one_pos
    simp only [show (1:ℝ) - 1 = 0 from by norm_num, Real.rpow_zero,
      one_mul] at h
    rw [h, Real.Gamma_one,
      show (1:ℝ) + 1 = 2 from by norm_num,
      show (1:ℝ) + 2 = 3 from by norm_num,
      show (1:ℝ) + 3 = 4 from by norm_num]
    rw [show Real.Gamma 2 = 1 from by
        rw [show (2:ℝ) = 1 + 1 from by norm_num,
          Real.Gamma_add_one one_ne_zero, Real.Gamma_one]; ring,
      show Real.Gamma 3 = 2 from by
        rw [show (3:ℝ) = 2 + 1 from by norm_num,
          Real.Gamma_add_one two_ne_zero,
          show (2:ℝ) = 1 + 1 from by norm_num,
          Real.Gamma_add_one one_ne_zero, Real.Gamma_one]; ring,
      show Real.Gamma 4 = 6 from by
        rw [show (4:ℝ) = 3 + 1 from by norm_num,
          Real.Gamma_add_one (by norm_num : (3:ℝ) ≠ 0),
          show (3:ℝ) = 2 + 1 from by norm_num,
          Real.Gamma_add_one two_ne_zero,
          show (2:ℝ) = 1 + 1 from by norm_num,
          Real.Gamma_add_one one_ne_zero, Real.Gamma_one]; ring]
    ring
  have hsub := integral_comp_rpow_Ioi (fun ξ => f4Dsq ξ) (p := 2) (by norm_num)
  rw [hM1] at hsub
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      ((fun ξ => f4Dsq ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 2 * (x * f4Dsq (x^2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [smul_eq_mul]
    have h21 : x ^ ((2:ℝ)-1) = x := by
      rw [show (2:ℝ)-1 = (1:ℝ) from by norm_num, Real.rpow_one]
    have hx2 : x ^ (2:ℝ) = x^2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    rw [h21, hx2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  rw [key, integral_const_mul] at hsub
  linarith [hsub]

/-- **The cross-channel bound**: the `uv`-leg's boost profile is `O(ln a)` —
two-piece dominator split at `u = (√a)⁻¹`: quadratic small-`u` bound from the
support-truncated inner integral, global mass `201` above. -/
theorem cross_channel_bound (g : ℝ → ℝ → ℝ) (Cg A B : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0)
    (a : ℝ) (ha : 0 < a) (haA : (Real.sqrt a)⁻¹ ≤ A) :
    |∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
        w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
      ≤ 75*Cg*B^2 + 201*Cg*(Real.log A + Real.log (Real.sqrt a)) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb 0 0)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set us := (Real.sqrt a)⁻¹ with husdef
  have hus : 0 < us := by positivity
  -- inner-integral bounds
  have hI1 : ∀ u : ℝ, 0 < u →
      |∫ w in Ioi (0:ℝ), w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
      ≤ 201 * Cg := by
    intro u hu
    rw [← Real.norm_eq_abs]
    have hdom : IntegrableOn (fun w => (w * f4Dsq (w^2)) * Cg) (Ioi (0:ℝ)) :=
      f4Dsq_w1_integrable.mul_const Cg
    apply le_trans (norm_integral_le_of_norm_le hdom ?_)
    · rw [integral_mul_const, f4Dsq_w1_mass]
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      have hf0 := f4Dsq_nonneg (w^2) (sq_nonneg w)
      rw [Real.norm_eq_abs, show w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))
          = (w * f4Dsq (w^2)) * g u (w/(Real.sqrt a * u)) from by ring,
        abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hgb u _) (by positivity)
  have hI2 : ∀ u : ℝ, 0 < u →
      |∫ w in Ioi (0:ℝ), w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
      ≤ 150 * Cg * B^2 * a * u^2 := by
    intro u hu
    have hZ : 0 < Real.sqrt a * u * B := by positivity
    have hvan : ∀ w : ℝ, Real.sqrt a * u * B ≤ w →
        w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u)) = 0 := by
      intro w hw
      rw [hsuppV u _ ?_, mul_zero]
      rw [le_div_iff₀ (by positivity)]
      calc B * (Real.sqrt a * u) = Real.sqrt a * u * B := by ring
        _ ≤ w := hw
    rw [← Real.norm_eq_abs]
    have hdom : IntegrableOn ((Ioc (0:ℝ) (Real.sqrt a * u * B)).indicator
        (fun w => 300 * Cg * w)) (Ioi (0:ℝ)) := by
      apply MeasureTheory.Integrable.integrableOn
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
      apply MeasureTheory.Integrable.mono'
        (MeasureTheory.integrableOn_const
          (C := 300 * Cg * (Real.sqrt a * u * B))
          (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        ((by fun_prop :
          Measurable (fun w : ℝ => 300 * Cg * w)).aestronglyMeasurable)
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
      intro w hw
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 300*Cg), abs_of_pos hw.1]
      exact mul_le_mul_of_nonneg_left hw.2 (by positivity)
    apply le_trans (norm_integral_le_of_norm_le hdom ?_)
    · have heval : (∫ w in Ioi (0:ℝ),
          (Ioc (0:ℝ) (Real.sqrt a * u * B)).indicator
            (fun w => 300 * Cg * w) w)
          = 150 * Cg * (Real.sqrt a * u * B)^2 := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict measurableSet_Ioc,
          Set.inter_eq_self_of_subset_left
            (fun x hx => Set.mem_Ioi.mpr hx.1),
          ← intervalIntegral.integral_of_le (le_of_lt hZ),
          intervalIntegral.integral_const_mul, integral_id]
        ring
      rw [heval, show 150 * Cg * (Real.sqrt a * u * B)^2
          = 150 * Cg * B^2 * (Real.sqrt a)^2 * u^2 from by ring,
        Real.sq_sqrt ha.le]
    · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      rw [mem_Ioi] at hw
      have hf0 := f4Dsq_nonneg (w^2) (sq_nonneg w)
      by_cases hmem : w ∈ Ioc (0:ℝ) (Real.sqrt a * u * B)
      · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs,
          show w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))
            = (w * f4Dsq (w^2)) * g u (w/(Real.sqrt a * u)) from by ring,
          abs_mul, abs_of_nonneg (by positivity)]
        calc (w * f4Dsq (w^2)) * |g u (w/(Real.sqrt a * u))|
            ≤ (w * 300) * Cg := by
              apply mul_le_mul ?_ (hgb u _) (abs_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left (f4Dsq_le _ (sq_nonneg w))
                (le_of_lt hw)
          _ = 300 * Cg * w := by ring
      · rw [Set.indicator_of_notMem hmem, hvan w (by
          rcases not_and_or.mp (fun h => hmem (Set.mem_Ioc.mpr h)) with h1 | h2
          · exact absurd hw h1
          · exact le_of_not_ge h2), norm_zero]
  -- the two-piece dominator over u
  have hp1int : Integrable ((Ioc (0:ℝ) us).indicator
      (fun u' => 150*Cg*B^2*a*u')) (volume.restrict (Ioi (0:ℝ))) := by
    apply MeasureTheory.Integrable.integrableOn
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := 150*Cg*B^2*a*us)
        (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      ((by fun_prop :
        Measurable (fun u : ℝ => 150*Cg*B^2*a*u)).aestronglyMeasurable)
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    intro u hu
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 150*Cg*B^2*a), abs_of_pos hu.1]
    exact mul_le_mul_of_nonneg_left hu.2 (by positivity)
  have hp2int : Integrable (fun u =>
      (Ioc us A).indicator (fun _ => 201*Cg) u * u⁻¹)
      (volume.restrict (Ioi (0:ℝ))) := by
    have hmeas : AEStronglyMeasurable
        (fun u => (Ioc us A).indicator (fun _ => 201*Cg) u * u⁻¹)
        (volume.restrict (Ioi (0:ℝ))) :=
      ((measurable_const.indicator measurableSet_Ioc).mul
        measurable_inv).aestronglyMeasurable
    have hDint : Integrable ((Ioc us A).indicator (fun _ => 201*Cg * us⁻¹))
        (volume.restrict (Ioi (0:ℝ))) := by
      apply MeasureTheory.Integrable.integrableOn
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
      exact MeasureTheory.integrableOn_const
        (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    apply MeasureTheory.Integrable.mono' hDint hmeas
    apply Filter.Eventually.of_forall
    intro u
    by_cases hmem : u ∈ Ioc us A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 201*Cg), abs_inv,
        abs_of_pos (lt_trans hus hmem.1)]
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hus hmem.1.le
    · rw [Set.indicator_of_notMem hmem, zero_mul, norm_zero]
      exact Set.indicator_apply_nonneg (fun _ => by positivity)
  -- the pointwise bound and the assembly
  have hdomsum : Integrable (fun u =>
      (Ioc (0:ℝ) us).indicator (fun u' => 150*Cg*B^2*a*u') u
      + (Ioc us A).indicator (fun _ => (201*Cg : ℝ)) u * u⁻¹)
      (volume.restrict (Ioi (0:ℝ))) := hp1int.add hp2int
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_of_norm_le hdomsum ?_)
  · -- evaluate the dominator integral
    have he1 : (∫ u in Ioi (0:ℝ),
        (Ioc (0:ℝ) us).indicator (fun u' => 150*Cg*B^2*a*u') u)
        = 75*Cg*B^2 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left (fun x hx => Set.mem_Ioi.mpr hx.1),
        ← intervalIntegral.integral_of_le (le_of_lt hus),
        intervalIntegral.integral_const_mul, integral_id]
      have hus2 : us^2 = a⁻¹ := by
        rw [husdef, show ((Real.sqrt a)⁻¹)^2 = ((Real.sqrt a)^2)⁻¹ from by
          rw [inv_pow], Real.sq_sqrt ha.le]
      rw [hus2]
      field_simp
      ring
    have he2 : (∫ u in Ioi (0:ℝ),
        (Ioc us A).indicator (fun _ => (201*Cg : ℝ)) u * u⁻¹)
        = 201*Cg*(Real.log A + Real.log (Real.sqrt a)) := by
      rw [show (fun u => (Ioc us A).indicator (fun _ => (201*Cg:ℝ)) u * u⁻¹)
          = (Ioc us A).indicator (fun u => 201*Cg * u⁻¹) from by
        funext u
        by_cases hmem : u ∈ Ioc us A
        · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
            zero_mul]]
      rw [MeasureTheory.integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left
          (fun x hx => Set.mem_Ioi.mpr (lt_trans hus hx.1)),
        ← intervalIntegral.integral_of_le haA,
        intervalIntegral.integral_const_mul]
      have h0notin : (0:ℝ) ∉ uIcc us A := by
        rw [uIcc_of_le haA]
        intro hmem
        exact absurd hmem.1 (not_le.mpr hus)
      rw [integral_inv h0notin,
        show A / us = A * Real.sqrt a from by
          rw [husdef]; field_simp,
        Real.log_mul (ne_of_gt hA) (ne_of_gt hsa)]
    rw [show (∫ u in Ioi (0:ℝ),
        ((Ioc (0:ℝ) us).indicator (fun u' => 150*Cg*B^2*a*u') u
          + (Ioc us A).indicator (fun _ => (201*Cg : ℝ)) u * u⁻¹))
        = (∫ u in Ioi (0:ℝ),
            (Ioc (0:ℝ) us).indicator (fun u' => 150*Cg*B^2*a*u') u)
          + ∫ u in Ioi (0:ℝ),
            (Ioc us A).indicator (fun _ => (201*Cg : ℝ)) u * u⁻¹ from
      MeasureTheory.integral_add hp1int hp2int, he1, he2]
  · apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    rw [mem_Ioi] at hu
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hu]
    rcases le_or_gt u us with hle | hgt
    · have hnot2 : u ∉ Ioc us A := fun hmem =>
        absurd hmem.1 (not_lt.mpr hle)
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu, hle⟩),
        Set.indicator_of_notMem hnot2, zero_mul, add_zero]
      calc u⁻¹ * |∫ w in Ioi (0:ℝ),
            w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
          ≤ u⁻¹ * (150 * Cg * B^2 * a * u^2) :=
            mul_le_mul_of_nonneg_left (hI2 u hu) (by positivity)
        _ = 150*Cg*B^2*a*u := by field_simp
    · have hnot1 : u ∉ Ioc (0:ℝ) us := fun hmem =>
        absurd hmem.2 (not_le.mpr hgt)
      rw [Set.indicator_of_notMem hnot1, zero_add]
      rcases le_or_gt u A with huA | huA
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hgt, huA⟩)]
        rw [mul_comm ((201:ℝ)*Cg) u⁻¹]
        exact mul_le_mul_of_nonneg_left (hI1 u hu) (by positivity)
      · have hz : (∫ w in Ioi (0:ℝ),
            w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))) = 0 := by
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            (fun w _ => by rw [hsuppU u _ (le_of_lt huA), mul_zero]),
            MeasureTheory.integral_zero]
        rw [hz, abs_zero, mul_zero]
        have hnot2 : u ∉ Ioc us A := fun hmem =>
          absurd hmem.2 (not_le.mpr huA)
        rw [Set.indicator_of_notMem hnot2, zero_mul]

#print axioms cross_channel_bound

#print axioms f4Dsq_w1_mass
#print axioms f4Dsq_le

#print axioms square_channel

#print axioms no_self_averaging_GCB

#print axioms no_self_averaging

#print axioms inner_sub_generic
#print axioms f4Dsq_w_mass

/-- **THE DIAGONAL VARIANCE RATE.**  For a bounded continuous box-supported
profile `g`,

    √a · ∬_{(0,∞)²} (v−u)²·f4Dsq(au²v²)·g(u,v)
      ⟶  (∫₀^∞ f4Dsq(w²)dw) · ( ∫₀^∞ u·g(u,0) du + ∫₀^∞ v·g(0,v) dv )

as `a → ∞`, with `∫₀^∞ f4Dsq(w²)dw = (315/4)√π` (`f4Dsq_w_mass`).  Split
`(v−u)² = u² + v² − 2uv`: the `u²`-channel converges by `square_channel`, the
`v²`-channel by Fubini transposition and `square_channel` on the swapped
profile, and the cross channel is `O(ln a/√a)` by `cross_channel_bound`.
The diagonal variance of the causal-set d'Alembertian therefore GROWS as
`√a` times computable edge constants — no self-averaging, with the rate. -/
theorem variance_rate (g : ℝ → ℝ → ℝ) (Cg A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0) :
    Filter.Tendsto (fun a : ℝ => Real.sqrt a * ∫ u in Ioi (0:ℝ),
        ∫ v in Ioi (0:ℝ), (v-u)^2 * f4Dsq (a*u^2*v^2) * g u v)
      Filter.atTop
      (𝓝 ((∫ w in Ioi (0:ℝ), f4Dsq (w^2)) *
        ((∫ u in Ioi (0:ℝ), u * g u 0) + ∫ v in Ioi (0:ℝ), v * g 0 v))) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb 0 0)
  -- the two square-channel limits
  have hchA := square_channel g Cg A B hA hB hgc hgb hsuppU hsuppV
  have hchB := square_channel (fun u v => g v u) Cg B A hB hA
    (hgc.comp continuous_swap) (fun u v => hgb v u)
    (fun u v hu => hsuppV v u hu) (fun u v hv => hsuppU v u hv)
  -- the cross channel dies like ln a/√a
  have hchC : Filter.Tendsto (fun a : ℝ => (Real.sqrt a)⁻¹ *
      ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
        w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))
      Filter.atTop (𝓝 0) := by
    have hmaj : ∀ᶠ a in Filter.atTop,
        ‖(Real.sqrt a)⁻¹ * ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
          w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))‖
        ≤ (75*Cg*B^2 + 201*Cg*(Real.log A + Real.log (Real.sqrt a)))
            / Real.sqrt a := by
      filter_upwards [Filter.eventually_ge_atTop (max 1 (A⁻¹^2))] with a ha
      have ha1 : (1:ℝ) ≤ a := le_trans (le_max_left _ _) ha
      have ha0 : (0:ℝ) < a := lt_of_lt_of_le one_pos ha1
      have haA : (Real.sqrt a)⁻¹ ≤ A := by
        have h1 : A⁻¹^2 ≤ a := le_trans (le_max_right _ _) ha
        have h2 : A⁻¹ ≤ Real.sqrt a := by
          rw [show A⁻¹ = Real.sqrt (A⁻¹^2) from
            (Real.sqrt_sq (by positivity)).symm]
          exact Real.sqrt_le_sqrt h1
        calc (Real.sqrt a)⁻¹ ≤ (A⁻¹)⁻¹ := by
              rw [← one_div, ← one_div]
              exact one_div_le_one_div_of_le (by positivity) h2
          _ = A := inv_inv A
      rw [Real.norm_eq_abs, abs_mul, abs_inv,
        abs_of_pos (Real.sqrt_pos.mpr ha0)]
      calc (Real.sqrt a)⁻¹ * |∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
            w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u))|
          ≤ (Real.sqrt a)⁻¹ *
            (75*Cg*B^2 + 201*Cg*(Real.log A + Real.log (Real.sqrt a))) :=
            mul_le_mul_of_nonneg_left
              (cross_channel_bound g Cg A B hA hB hgb hsuppU hsuppV a ha0 haA)
              (by positivity)
        _ = (75*Cg*B^2 + 201*Cg*(Real.log A + Real.log (Real.sqrt a)))
            / Real.sqrt a := by
            rw [div_eq_mul_inv, mul_comm]
    have hglim : Filter.Tendsto (fun a : ℝ =>
        (75*Cg*B^2 + 201*Cg*(Real.log A + Real.log (Real.sqrt a)))
          / Real.sqrt a) Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto
          (fun t : ℝ => (75*Cg*B^2 + 201*Cg*Real.log A) / t)
          Filter.atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Filter.tendsto_id
      have h2 : Filter.Tendsto (fun t : ℝ => 201*Cg*(Real.log t / t))
          Filter.atTop (𝓝 (201*Cg*0)) :=
        (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).const_mul _
      rw [mul_zero] at h2
      have h12 := h1.add h2
      rw [add_zero] at h12
      have hlim : Filter.Tendsto (fun t : ℝ =>
          (75*Cg*B^2 + 201*Cg*(Real.log A + Real.log t)) / t)
          Filter.atTop (𝓝 0) := by
        apply h12.congr'
        filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
        rw [← mul_div_assoc, div_add_div_same]
        congr 1
        ring
      have hcomp := hlim.comp Real.tendsto_sqrt_atTop
      simpa [Function.comp] using hcomp
    exact squeeze_zero_norm' hmaj hglim
  -- combine the three limits
  have hcomb := (hchA.add hchB).sub (hchC.const_mul 2)
  rw [mul_zero, sub_zero, ← mul_add] at hcomb
  apply hcomb.congr'
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with a ha
  show ((∫ u in Ioi (0:ℝ), u * ∫ w in Ioi (0:ℝ),
        f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))
      + ∫ u in Ioi (0:ℝ), u * ∫ w in Ioi (0:ℝ),
        f4Dsq (w^2) * g (w/(Real.sqrt a * u)) u)
      - 2 * ((Real.sqrt a)⁻¹ * ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
        w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u)))
      = Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        (v-u)^2 * f4Dsq (a*u^2*v^2) * g u v
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  -- continuity/measurability of the pieces
  have hK : Continuous (fun ξ : ℝ => f4Dsq ξ) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder.f4Dsq
    fun_prop
  have hkerc : Continuous (fun p : ℝ × ℝ => f4Dsq (a*p.1^2*p.2^2)) :=
    hK.comp (by fun_prop)
  have hm1 : Measurable (Function.uncurry (fun u v : ℝ =>
      u^2 * f4Dsq (a*u^2*v^2) * g u v)) :=
    (((continuous_fst.pow 2).mul hkerc).mul hgc).measurable
  have hm2 : Measurable (Function.uncurry (fun u v : ℝ =>
      v^2 * f4Dsq (a*u^2*v^2) * g u v)) :=
    (((continuous_snd.pow 2).mul hkerc).mul hgc).measurable
  have hm3 : Measurable (Function.uncurry (fun u v : ℝ =>
      u*v * f4Dsq (a*u^2*v^2) * g u v)) :=
    (((continuous_fst.mul continuous_snd).mul hkerc).mul hgc).measurable
  -- pointwise bounds
  have hb1 : ∀ u v : ℝ, 0 < u → 0 < v →
      |u^2 * f4Dsq (a*u^2*v^2) * g u v| ≤ A^2*(300*Cg) := by
    intro u v hu hv
    rcases le_or_gt A u with huA | huA
    · rw [hsuppU u v huA, mul_zero, abs_zero]
      positivity
    · have hz : (0:ℝ) ≤ a*u^2*v^2 := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg u),
        abs_of_nonneg (f4Dsq_nonneg _ hz)]
      have hu2 : u^2 ≤ A^2 := by nlinarith
      calc u^2 * f4Dsq (a*u^2*v^2) * |g u v|
          ≤ (A^2 * 300) * Cg := by
            apply mul_le_mul _ (hgb u v) (abs_nonneg _) (by positivity)
            exact mul_le_mul hu2 (f4Dsq_le _ hz) (f4Dsq_nonneg _ hz)
              (by positivity)
        _ = A^2*(300*Cg) := by ring
  have hb2 : ∀ u v : ℝ, 0 < u → 0 < v →
      |v^2 * f4Dsq (a*u^2*v^2) * g u v| ≤ B^2*(300*Cg) := by
    intro u v hu hv
    rcases le_or_gt B v with hvB | hvB
    · rw [hsuppV u v hvB, mul_zero, abs_zero]
      positivity
    · have hz : (0:ℝ) ≤ a*u^2*v^2 := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg v),
        abs_of_nonneg (f4Dsq_nonneg _ hz)]
      have hv2 : v^2 ≤ B^2 := by nlinarith
      calc v^2 * f4Dsq (a*u^2*v^2) * |g u v|
          ≤ (B^2 * 300) * Cg := by
            apply mul_le_mul _ (hgb u v) (abs_nonneg _) (by positivity)
            exact mul_le_mul hv2 (f4Dsq_le _ hz) (f4Dsq_nonneg _ hz)
              (by positivity)
        _ = B^2*(300*Cg) := by ring
  have hb3 : ∀ u v : ℝ, 0 < u → 0 < v →
      |u*v * f4Dsq (a*u^2*v^2) * g u v| ≤ A*B*(300*Cg) := by
    intro u v hu hv
    rcases le_or_gt A u with huA | huA
    · rw [hsuppU u v huA, mul_zero, abs_zero]
      positivity
    rcases le_or_gt B v with hvB | hvB
    · rw [hsuppV u v hvB, mul_zero, abs_zero]
      positivity
    have hz : (0:ℝ) ≤ a*u^2*v^2 := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ u*v),
      abs_of_nonneg (f4Dsq_nonneg _ hz)]
    have huv : u*v ≤ A*B := by nlinarith
    calc u*v * f4Dsq (a*u^2*v^2) * |g u v|
        ≤ (A*B * 300) * Cg := by
          apply mul_le_mul _ (hgb u v) (abs_nonneg _) (by positivity)
          exact mul_le_mul huv (f4Dsq_le _ hz) (f4Dsq_nonneg _ hz)
            (by positivity)
      _ = A*B*(300*Cg) := by ring
  -- supports
  have hs1U : ∀ u v : ℝ, 0 < v → A ≤ u →
      u^2 * f4Dsq (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hu => by rw [hsuppU u v hu, mul_zero]
  have hs1V : ∀ u v : ℝ, 0 < u → B ≤ v →
      u^2 * f4Dsq (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hv => by rw [hsuppV u v hv, mul_zero]
  have hs2U : ∀ u v : ℝ, 0 < v → A ≤ u →
      v^2 * f4Dsq (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hu => by rw [hsuppU u v hu, mul_zero]
  have hs2V : ∀ u v : ℝ, 0 < u → B ≤ v →
      v^2 * f4Dsq (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hv => by rw [hsuppV u v hv, mul_zero]
  have hs3U : ∀ u v : ℝ, 0 < v → A ≤ u →
      u*v * f4Dsq (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hu => by rw [hsuppU u v hu, mul_zero]
  have hs3V : ∀ u v : ℝ, 0 < u → B ≤ v →
      u*v * f4Dsq (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hv => by rw [hsuppV u v hv, mul_zero]
  -- slice integrability, generic
  have hsl : ∀ (h : ℝ → ℝ → ℝ) (C : ℝ), Measurable (Function.uncurry h) →
      (∀ u v, 0 < u → 0 < v → |h u v| ≤ C) →
      (∀ u v, 0 < u → B ≤ v → h u v = 0) →
      ∀ u : ℝ, 0 < u → IntegrableOn (fun v => h u v) (Ioi (0:ℝ)) := by
    intro h C hm hb hs u hu
    exact integrableOn_Ioi_of_bounded_support (fun v => h u v) C B hB
      ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun v hv => hb u v hu hv) (fun v hv => hs u v hu hv)
  have hsl1 := hsl _ (A^2*(300*Cg)) hm1 hb1 hs1V
  have hsl2 := hsl _ (B^2*(300*Cg)) hm2 hb2 hs2V
  have hsl3 := hsl _ (A*B*(300*Cg)) hm3 hb3 hs3V
  -- marginal integrability, generic
  have hmarg : ∀ (h : ℝ → ℝ → ℝ) (C : ℝ), 0 ≤ C →
      Measurable (Function.uncurry h) →
      (∀ u v, 0 < u → 0 < v → |h u v| ≤ C) →
      (∀ u v, 0 < v → A ≤ u → h u v = 0) →
      (∀ u v, 0 < u → B ≤ v → h u v = 0) →
      MeasureTheory.IntegrableOn (fun u => ∫ v in Ioi (0:ℝ), h u v)
        (Ioi (0:ℝ)) := by
    intro h C hC hm hb hsu hsv
    apply integrableOn_Ioi_of_bounded_support _ (C*B) A hA
    · exact ((hm.stronglyMeasurable.integral_prod_right').measurable
        ).aestronglyMeasurable
    · intro u hu
      have htail := integral_Ioi_sub_interval (fun v => h u v) C B B hC hB
        le_rfl
        ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (fun v hv => hb u v hu hv) (fun v hv => hsv u v hu hv)
      rw [intervalIntegral.integral_same, sub_zero] at htail
      exact htail
    · intro u hu
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun v hv => hsu u v (Set.mem_Ioi.mp hv) hu),
        MeasureTheory.integral_zero]
  have hM1 := hmarg _ (A^2*(300*Cg)) (by positivity) hm1 hb1 hs1U hs1V
  have hM2 := hmarg _ (B^2*(300*Cg)) (by positivity) hm2 hb2 hs2U hs2V
  have hM3 := hmarg _ (A*B*(300*Cg)) (by positivity) hm3 hb3 hs3U hs3V
  -- inner split, per u > 0
  have hinner : ∀ u : ℝ, 0 < u →
      (∫ v in Ioi (0:ℝ), (v-u)^2 * f4Dsq (a*u^2*v^2) * g u v)
      = ((∫ v in Ioi (0:ℝ), u^2 * f4Dsq (a*u^2*v^2) * g u v)
          + ∫ v in Ioi (0:ℝ), v^2 * f4Dsq (a*u^2*v^2) * g u v)
        - 2 * ∫ v in Ioi (0:ℝ), u*v * f4Dsq (a*u^2*v^2) * g u v := by
    intro u hu
    have h12 : MeasureTheory.Integrable (fun v =>
        u^2 * f4Dsq (a*u^2*v^2) * g u v + v^2 * f4Dsq (a*u^2*v^2) * g u v)
        (MeasureTheory.volume.restrict (Ioi (0:ℝ))) :=
      (hsl1 u hu).add (hsl2 u hu)
    have h3 : MeasureTheory.Integrable (fun v =>
        2 * (u*v * f4Dsq (a*u^2*v^2) * g u v))
        (MeasureTheory.volume.restrict (Ioi (0:ℝ))) :=
      MeasureTheory.Integrable.const_mul (hsl3 u hu) 2
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add (hsl1 u hu) (hsl2 u hu),
      ← MeasureTheory.integral_sub h12 h3]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    ring
  -- outer split
  have houter : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      (v-u)^2 * f4Dsq (a*u^2*v^2) * g u v)
      = ((∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
            u^2 * f4Dsq (a*u^2*v^2) * g u v)
          + ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
            v^2 * f4Dsq (a*u^2*v^2) * g u v)
        - 2 * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
            u*v * f4Dsq (a*u^2*v^2) * g u v := by
    have h12 : MeasureTheory.Integrable (fun u =>
        (∫ v in Ioi (0:ℝ), u^2 * f4Dsq (a*u^2*v^2) * g u v)
          + ∫ v in Ioi (0:ℝ), v^2 * f4Dsq (a*u^2*v^2) * g u v)
        (MeasureTheory.volume.restrict (Ioi (0:ℝ))) := hM1.add hM2
    have h3 : MeasureTheory.Integrable (fun u =>
        2 * ∫ v in Ioi (0:ℝ), u*v * f4Dsq (a*u^2*v^2) * g u v)
        (MeasureTheory.volume.restrict (Ioi (0:ℝ))) :=
      MeasureTheory.Integrable.const_mul hM3 2
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add hM1 hM2,
      ← MeasureTheory.integral_sub h12 h3]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact hinner u (Set.mem_Ioi.mp hu)
  -- channel A conversion
  have hT1 : Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      u^2 * f4Dsq (a*u^2*v^2) * g u v
      = ∫ u in Ioi (0:ℝ), u * ∫ w in Ioi (0:ℝ),
          f4Dsq (w^2) * g u (w/(Real.sqrt a * u)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    rw [Set.mem_Ioi] at hu
    dsimp only
    have hpull : (∫ v in Ioi (0:ℝ), u^2 * f4Dsq (a*u^2*v^2) * g u v)
        = u^2 * ∫ v in Ioi (0:ℝ), f4Dsq (a*u^2*v^2) * g u v := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro v _
      ring
    rw [hpull, show Real.sqrt a * (u^2 * ∫ v in Ioi (0:ℝ),
        f4Dsq (a*u^2*v^2) * g u v)
        = u^2 * (Real.sqrt a * ∫ v in Ioi (0:ℝ),
          f4Dsq (a*u^2*v^2) * g u v) from by ring,
      inner_sub_generic f4Dsq (fun v => g u v) a u ha hu,
      ← mul_assoc, show u^2 * u⁻¹ = u from by
        rw [pow_two, mul_assoc, mul_inv_cancel₀ (ne_of_gt hu), mul_one]]
  -- channel B conversion: Fubini transpose, then the substitution
  have hswap : (∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      v^2 * f4Dsq (a*u^2*v^2) * g u v)
      = ∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ),
        v^2 * f4Dsq (a*u^2*v^2) * g u v :=
    MeasureTheory.integral_integral_swap (prod_box_integrable
      (fun u v => v^2 * f4Dsq (a*u^2*v^2) * g u v) (B^2*(300*Cg)) A B
      (by positivity) hA hB hm2 hb2 hs2U hs2V)
  have hT2 : Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      v^2 * f4Dsq (a*u^2*v^2) * g u v
      = ∫ u in Ioi (0:ℝ), u * ∫ w in Ioi (0:ℝ),
          f4Dsq (w^2) * g (w/(Real.sqrt a * u)) u := by
    rw [hswap, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [Set.mem_Ioi] at hx
    dsimp only
    have hpull : (∫ y in Ioi (0:ℝ), x^2 * f4Dsq (a*y^2*x^2) * g y x)
        = x^2 * ∫ y in Ioi (0:ℝ), f4Dsq (a*x^2*y^2) * g y x := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y _
      dsimp only
      rw [show a*y^2*x^2 = a*x^2*y^2 from by ring]
      ring
    rw [hpull, show Real.sqrt a * (x^2 * ∫ y in Ioi (0:ℝ),
        f4Dsq (a*x^2*y^2) * g y x)
        = x^2 * (Real.sqrt a * ∫ y in Ioi (0:ℝ),
          f4Dsq (a*x^2*y^2) * g y x) from by ring,
      inner_sub_generic f4Dsq (fun y => g y x) a x ha hx,
      ← mul_assoc, show x^2 * x⁻¹ = x from by
        rw [pow_two, mul_assoc, mul_inv_cancel₀ (ne_of_gt hx), mul_one]]
  -- channel C conversion
  have hT3 : Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
      u*v * f4Dsq (a*u^2*v^2) * g u v
      = (Real.sqrt a)⁻¹ * ∫ u in Ioi (0:ℝ), u⁻¹ * ∫ w in Ioi (0:ℝ),
          w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u)) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    rw [Set.mem_Ioi] at hu
    dsimp only
    have hpull : (∫ v in Ioi (0:ℝ), u*v * f4Dsq (a*u^2*v^2) * g u v)
        = u * ∫ v in Ioi (0:ℝ), f4Dsq (a*u^2*v^2) * (v * g u v) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      ring
    rw [hpull, show Real.sqrt a * (u * ∫ v in Ioi (0:ℝ),
        f4Dsq (a*u^2*v^2) * (v * g u v))
        = u * (Real.sqrt a * ∫ v in Ioi (0:ℝ),
          f4Dsq (a*u^2*v^2) * (v * g u v)) from by ring,
      inner_sub_generic f4Dsq (fun v => v * g u v) a u ha hu]
    have hw : (∫ w in Ioi (0:ℝ), f4Dsq (w^2) *
        (w/(Real.sqrt a * u) * g u (w/(Real.sqrt a * u))))
        = (Real.sqrt a * u)⁻¹ * ∫ w in Ioi (0:ℝ),
          w * f4Dsq (w^2) * g u (w/(Real.sqrt a * u)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      rw [div_eq_mul_inv]
      ring
    rw [hw, mul_inv]
    field_simp
  -- assemble
  rw [houter, mul_sub, mul_add, mul_left_comm (Real.sqrt a) 2, hT1, hT2, hT3]

#print axioms variance_rate

end UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate

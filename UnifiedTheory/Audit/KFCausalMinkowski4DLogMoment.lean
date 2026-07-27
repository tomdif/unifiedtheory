/-
# The K4 log-moment: C_K = √π/3

The complete K4-corner theorem (KFCausalMinkowski4DCorner) delivers the corner
mass as `−g(0,0)·∫₀^∞ K4(w²)·ln w dw`.  This file evaluates that integral:

  ∫₀^∞ K4(w²)·ln w dw = −√π/3,     i.e.     C_K = √π/3.

Route (the Γ′-chain):
* `Gamma_hasDerivAt_integral` — the derivative of the real Γ-function at `x > 0`
  is the log-Mellin integral `∫ t^{x−1}·ln t·e^{−t} dt`, obtained from Mathlib's
  complex `hasDerivAt_GammaIntegral` through the `ofReal` bridge.
* `Gamma_hasDerivAt_succ` — the derivative recurrence `Γ'(x+1) = Γ(x) + x·Γ'(x)`
  from the functional equation.
* Mathlib's `Real.hasDerivAt_Gamma_one_half`: `Γ'(½) = −√π·(γ + 2 ln 2)`.
* Uniqueness of derivatives pins the three log-moments at `s = ½, 3/2, 5/2`; in
  the combination `⅓[Γ'(½) + 4Γ'(3/2) − 4Γ'(5/2)]` the digamma constant
  `γ + 2 ln 2` cancels — the same `M[K4](½) = 0` Mellin zero that kills the
  kernel mass — leaving `−4√π/3`.
* The substitution `z = w²` converts to the `w`-integral: `∫K4(w²)ln w = −√π/3`.

Combined with the corner theorem this gives the final valued corner limit
`K4_corner_value`: `√a·∬K4(au²v²)g → g(0,0)·√π/3`.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DCorner

open MeasureTheory Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DCorner

namespace UnifiedTheory.Audit.KFCausalMinkowski4DLogMoment

/-- The log-weighted Γ-integrand is integrable for `x > 1/4`: dominate `|ln t|`
by `t + 4t^{−1/4}` (`abs_log_le`) and absorb both terms into Γ-integrands. -/
theorem log_gamma_integrable (x : ℝ) (hx : 1/4 < x) :
    IntegrableOn (fun t => t ^ (x-1) * (Real.log t * Real.exp (-t))) (Ioi (0:ℝ)) := by
  have hdom : Integrable (fun t => Real.exp (-t) * t ^ ((x+1)-1)
      + 4 * (Real.exp (-t) * t ^ ((x - 1/4) - 1))) (volume.restrict (Ioi (0:ℝ))) :=
    (Real.GammaIntegral_convergent (by linarith)).add
      ((Real.GammaIntegral_convergent (by linarith)).const_mul 4)
  apply Integrable.mono' hdom
  · have hcont : ContinuousOn (fun t : ℝ => t ^ (x-1) * (Real.log t * Real.exp (-t)))
        (Ioi (0:ℝ)) := by
      apply ContinuousOn.mul
      · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
      · exact (Real.continuousOn_log.mono (fun t ht => ne_of_gt ht)).mul
          (Real.continuous_exp.comp continuous_neg).continuousOn
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    rw [mem_Ioi] at ht
    have hrp : 0 < t ^ (x-1) := Real.rpow_pos_of_pos ht _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hrp,
      abs_of_pos (Real.exp_pos (-t))]
    have h1 : t ^ (x-1) * t = t ^ ((x+1)-1) := by
      rw [show (x+1)-1 = (x-1)+1 from by ring, Real.rpow_add_one (ne_of_gt ht)]
    have h2 : t ^ (x-1) * t ^ (-(1:ℝ)/4) = t ^ ((x - 1/4) - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc t ^ (x-1) * (|Real.log t| * Real.exp (-t))
        ≤ t ^ (x-1) * ((t + 4 * t ^ (-(1:ℝ)/4)) * Real.exp (-t)) := by
          apply mul_le_mul_of_nonneg_left ?_ (le_of_lt hrp)
          exact mul_le_mul_of_nonneg_right (abs_log_le t ht)
            (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-t) * t ^ ((x+1)-1)
          + 4 * (Real.exp (-t) * t ^ ((x - 1/4) - 1)) := by
          rw [show t ^ (x-1) * ((t + 4 * t ^ (-(1:ℝ)/4)) * Real.exp (-t))
              = (t ^ (x-1) * t) * Real.exp (-t)
                + 4 * ((t ^ (x-1) * t ^ (-(1:ℝ)/4)) * Real.exp (-t)) from by ring,
            h1, h2]
          ring

/-- **The derivative of the real Γ-function is the log-Mellin integral**: for
`x > 0`, `Γ'(x) = ∫₀^∞ t^{x−1}·ln t·e^{−t} dt`.  Complex-to-real bridge of
Mathlib's `hasDerivAt_GammaIntegral`. -/
theorem Gamma_hasDerivAt_integral (x : ℝ) (hx : 0 < x) :
    HasDerivAt Real.Gamma
      (∫ t in Ioi (0:ℝ), t ^ (x-1) * (Real.log t * Real.exp (-t))) x := by
  have hc := Complex.hasDerivAt_GammaIntegral
    (s := (x:ℂ)) (by simpa using hx)
  have hre : ∀ᶠ s : ℂ in 𝓝 (x:ℂ), 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).eventually_mem (by simpa using hx)
  have hev : Complex.Gamma =ᶠ[𝓝 (x:ℂ)] Complex.GammaIntegral := by
    filter_upwards [hre] with s hs using Complex.Gamma_eq_integral hs
  have hg := hc.congr_of_eventuallyEq hev
  have hIc : (∫ t : ℝ in Ioi 0, (t:ℂ) ^ ((x:ℂ) - 1) * (Real.log t * Real.exp (-t)))
      = ((∫ t in Ioi (0:ℝ), t ^ (x-1) * (Real.log t * Real.exp (-t)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [mem_Ioi] at ht
    push_cast
    rw [Complex.ofReal_cpow ht.le]
    norm_cast
  rw [hIc] at hg
  have hr := hg.real_of_complex
  simp only [Complex.ofReal_re] at hr
  exact hr

/-- The derivative recurrence `Γ'(x+1) = Γ(x) + x·Γ'(x)`, from the functional
equation `Γ(s+1) = s·Γ(s)` near `x > 0`. -/
theorem Gamma_hasDerivAt_succ {x d : ℝ} (hx : 0 < x)
    (h : HasDerivAt Real.Gamma d x) :
    HasDerivAt Real.Gamma (Real.Gamma x + x * d) (x + 1) := by
  have hmul : HasDerivAt (fun s => s * Real.Gamma s)
      (1 * Real.Gamma x + x * d) x := (hasDerivAt_id x).mul h
  have hev : (fun s => Real.Gamma (s+1)) =ᶠ[𝓝 x] (fun s => s * Real.Gamma s) := by
    filter_upwards [eventually_ne_nhds (ne_of_gt hx)] with s hs
      using Real.Gamma_add_one hs
  have hcomp : HasDerivAt (fun s => Real.Gamma (s+1))
      (1 * Real.Gamma x + x * d) x := hmul.congr_of_eventuallyEq hev
  have hcomp' : HasDerivAt (fun s => Real.Gamma (s+1))
      (1 * Real.Gamma x + x * d) ((x+1) - 1) := by
    have hxx : x = (x+1) - 1 := by ring
    rw [← hxx]
    exact hcomp
  have hs : HasDerivAt (fun t : ℝ => t - 1) 1 (x+1) :=
    (hasDerivAt_id (x+1)).sub_const 1
  have h2 := hcomp'.comp (x+1) hs
  simp only [Function.comp_def, sub_add_cancel, mul_one, one_mul] at h2
  exact h2

/-- `Γ'(½) = ∫ t^{−½}·ln t·e^{−t} dt = −√π·(γ + 2 ln 2)`. -/
theorem L_half :
    (∫ t in Ioi (0:ℝ), t ^ ((1/2:ℝ)-1) * (Real.log t * Real.exp (-t)))
      = -Real.sqrt Real.pi * (Real.eulerMascheroniConstant + 2 * Real.log 2) :=
  (Gamma_hasDerivAt_integral (1/2) one_half_pos).unique Real.hasDerivAt_Gamma_one_half

/-- `Γ'(3/2) = √π·(2 − γ − 2 ln 2)/2`. -/
theorem L_threehalf :
    (∫ t in Ioi (0:ℝ), t ^ ((3/2:ℝ)-1) * (Real.log t * Real.exp (-t)))
      = Real.sqrt Real.pi * (2 - Real.eulerMascheroniConstant - 2 * Real.log 2) / 2 := by
  have h32 := Gamma_hasDerivAt_succ one_half_pos Real.hasDerivAt_Gamma_one_half
  rw [show (1/2:ℝ)+1 = 3/2 from by norm_num] at h32
  have h := (Gamma_hasDerivAt_integral (3/2) (by norm_num)).unique h32
  rw [h, Real.Gamma_one_half_eq]
  ring

/-- `Γ'(5/2) = √π·(8 − 3γ − 6 ln 2)/4`. -/
theorem L_fivehalf :
    (∫ t in Ioi (0:ℝ), t ^ ((5/2:ℝ)-1) * (Real.log t * Real.exp (-t)))
      = Real.sqrt Real.pi * (8 - 3 * Real.eulerMascheroniConstant - 6 * Real.log 2) / 4 := by
  have h32 := Gamma_hasDerivAt_succ one_half_pos Real.hasDerivAt_Gamma_one_half
  rw [show (1/2:ℝ)+1 = 3/2 from by norm_num] at h32
  have h52 := Gamma_hasDerivAt_succ (by norm_num : (0:ℝ) < 3/2) h32
  rw [show (3/2:ℝ)+1 = 5/2 from by norm_num] at h52
  have h := (Gamma_hasDerivAt_integral (5/2) (by norm_num)).unique h52
  rw [h]
  have hg32 : Real.Gamma (3/2) = Real.sqrt Real.pi / 2 := by
    rw [show (3/2:ℝ) = 1/2 + 1 from by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  rw [hg32, Real.Gamma_one_half_eq]
  ring

/-- The `z`-side log-moment: `∫₀^∞ z^{−½}·K4(z)·ln z dz = −4√π/3`.  The digamma
constant `γ + 2 ln 2` cancels in the layer combination — the `s = ½` Mellin zero
of `K4` scrubbing the transcendental constants. -/
theorem K4_root_log_moment :
    (∫ z in Ioi (0:ℝ), z ^ (-(1:ℝ)/2) * K4 z * Real.log z)
      = -(4/3) * Real.sqrt Real.pi := by
  have i1 := log_gamma_integrable (1/2) (by norm_num)
  have i2 := log_gamma_integrable (3/2) (by norm_num)
  have i3 := log_gamma_integrable (5/2) (by norm_num)
  have hsplit : (∫ z in Ioi (0:ℝ), z ^ (-(1:ℝ)/2) * K4 z * Real.log z)
      = ∫ z in Ioi (0:ℝ),
          ((1/3) * (z ^ ((1/2:ℝ)-1) * (Real.log z * Real.exp (-z)))
            + (4/3) * (z ^ ((3/2:ℝ)-1) * (Real.log z * Real.exp (-z)))
            - (4/3) * (z ^ ((5/2:ℝ)-1) * (Real.log z * Real.exp (-z)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    rw [mem_Ioi] at hz
    have e1 : z ^ ((1/2:ℝ)-1) = z ^ (-(1:ℝ)/2) := by norm_num
    have e2 : z ^ ((3/2:ℝ)-1) = z ^ (-(1:ℝ)/2) * z := by
      rw [← Real.rpow_add_one (ne_of_gt hz)]
      congr 1
      norm_num
    have e3 : z ^ ((5/2:ℝ)-1) = z ^ ((3/2:ℝ)-1) * z := by
      rw [← Real.rpow_add_one (ne_of_gt hz)]
      congr 1
      norm_num
    dsimp only
    rw [e3, e2, e1]
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    ring
  have h1 : Integrable (fun z =>
      (1/3) * (z ^ ((1/2:ℝ)-1) * (Real.log z * Real.exp (-z))))
      (volume.restrict (Ioi (0:ℝ))) := i1.const_mul _
  have h2 : Integrable (fun z =>
      (4/3) * (z ^ ((3/2:ℝ)-1) * (Real.log z * Real.exp (-z))))
      (volume.restrict (Ioi (0:ℝ))) := i2.const_mul _
  have h3 : Integrable (fun z =>
      (4/3) * (z ^ ((5/2:ℝ)-1) * (Real.log z * Real.exp (-z))))
      (volume.restrict (Ioi (0:ℝ))) := i3.const_mul _
  have h12 : Integrable (fun z =>
      (1/3) * (z ^ ((1/2:ℝ)-1) * (Real.log z * Real.exp (-z)))
        + (4/3) * (z ^ ((3/2:ℝ)-1) * (Real.log z * Real.exp (-z))))
      (volume.restrict (Ioi (0:ℝ))) := h1.add h2
  rw [hsplit, integral_sub h12 h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    L_half, L_threehalf, L_fivehalf]
  ring

/-- **The corner constant**: `∫₀^∞ K4(w²)·ln w dw = −√π/3`, i.e. `C_K = √π/3`. -/
theorem K4_log_moment :
    (∫ w in Ioi (0:ℝ), K4 (w^2) * Real.log w) = -Real.sqrt Real.pi / 3 := by
  have hcomp := integral_comp_rpow_Ioi
    (fun ξ => ξ ^ (-(1:ℝ)/2) * K4 ξ * Real.log ξ) (p := 2) (by norm_num)
  rw [K4_root_log_moment] at hcomp
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ)-1)) •
      ((fun ξ => ξ ^ (-(1:ℝ)/2) * K4 ξ * Real.log ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 4 * (K4 (x^2) * Real.log x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    dsimp only
    rw [smul_eq_mul]
    have h21 : x ^ ((2:ℝ)-1) = x := by
      rw [show (2:ℝ)-1 = (1:ℝ) from by norm_num, Real.rpow_one]
    have hpow : (x ^ (2:ℝ)) ^ (-(1:ℝ)/2) = x⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt hx),
        show (2:ℝ) * (-(1:ℝ)/2) = -1 from by norm_num, Real.rpow_neg_one]
    have hlog : Real.log (x ^ (2:ℝ)) = 2 * Real.log x := Real.log_rpow hx 2
    have hx2 : x ^ (2:ℝ) = x^2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
    rw [h21, hpow, hlog, hx2, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp
    ring
  rw [key, integral_const_mul] at hcomp
  linarith [hcomp]

/-- **The valued K4-corner theorem**: the hyperbolic-corner mass of the 4D BDG
operator is exactly `g(0,0)·√π/3`. -/
theorem K4_corner_value (g pdug : ℝ → ℝ → ℝ) (Mu Cg A B : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0) :
    Tendsto (fun a : ℝ => Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        K4 (a*u^2*v^2) * g u v)
      atTop (𝓝 (g 0 0 * (Real.sqrt Real.pi / 3))) := by
  have h := K4_corner_limit g pdug Mu Cg A B hA hB hgc hdu hMu hgb hsuppU hsuppV
  rw [K4_log_moment] at h
  convert h using 2
  ring

#print axioms K4_log_moment
#print axioms K4_corner_value

end UnifiedTheory.Audit.KFCausalMinkowski4DLogMoment

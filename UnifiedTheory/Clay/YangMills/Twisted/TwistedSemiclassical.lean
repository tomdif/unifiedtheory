/- Structure of the semiclassical neutral gap (Milestone A₀ of the twisted program).

Proved here with no open hypothesis:
* `free_spectral`, `free_gap`, `free_gap_lattice`: the free many-mode transfer form has top `Λ`, attained by
  the ground Gaussian, and at most `r Λ` on its orthogonal complement, for every number of modes. There is
  no compactness and no Hermite expansion: coherent vectors are total, the kernel maps `ξ ↦ ρ ξ`, and the rest
  is a positive-definiteness statement. At the lowest twisted stiffness this gives a gap of at least `√2/N`,
  uniform in the number of modes. This is a free model and not the Wilson operator.
* `perturbed_gap`: a relative pointwise kernel bound `|K - c K₀| ≤ δ c K₀` transfers that bound, with `r + δ`.
  Also about the free model, until a `ValleyChart` exists.
* `avg_integral_invariant`, `integral_kernel_invariant`: on gauge-invariant functions the temporal gauge average
  drops out exactly, so `T = w K₀ w` with `K₀` a product of single-link kernels. `norm_le_mass` is the resulting
  Schur bound on `‖T‖`. It is crude: with `norm_lower'` it pins `log ‖T‖` only to within about `6 n³ log β`.
* `kernel_off`, `form_split`, `offError_le_norm`: for `β ≥ A n⁸`, outside the two diagonal valley blocks the kernel
  contributes at most `exp(-n⁴) ‖T‖` to the form of a flip-even function. `offError_le_of_budget` gives the same at
  any level above about `n³ log β / β`.
* `neutralPoincare_explicit`, `gap_explicit`: the first instance of `NeutralPoincare`, with constant
  `exp(72 β n³)`, and an explicit `ρ = 1 - exp(-72 β n³)`. Exponentially far from `n/c`.
* `valleyPoincare_explicit`, `valleyGap_explicit`, `valleyGap_at_threshold`: `ValleyGap` below `‖T‖` at every cutoff,
  with `ψ = η` and a level exponentially close to `‖T‖`. So `ValleyGap` is not open at fixed `n`; what is open is the
  size `exp(-c/n) ‖T‖`, uniformly in `n`.
* `valleyGap_of_contraction`: the converse of `neutral_contraction_of_valley`. A contraction by `B` on the neutral
  complement gives `ValleyGap` at `B + offError`, with `ψ = η`. So `ValleyGap` against the ground state is the neutral
  gap up to `offError`, in both directions: the reduction removes the far field, tunneling and the temporal average,
  and leaves the analytic core entirely in place.
* `eigen_valley_mass`: flip-even eigenfunctions concentrate on the valleys.
* `haar_gnomonic`, `pi_near`: Haar measure on `Q`, and product Haar around a reference field, as the image of Lebesgue
  measure with the explicit density `(2π²)⁻¹ (1 + |t|²)⁻²` per link, in the gnomonic coordinate `q = (1, t)/√(1 + |t|²)`.
  `integral_frame` removes the global rotation by a frame weight in place of a slice, and `integral_off_tree`,
  `integral_tree_chart` give gauge-invariant integrals in these coordinates, with the lower bound on the frame weight on the
  support as a hypothesis. These are exact identities for one field. They are one ingredient of a chart, not a chart: the
  kernel is not treated, and the three frame directions are still in the coordinates.

Conditional, on hypotheses named as open:
* `neutral_contraction_A0`, `neutral_contraction_budget`: `ValleyGap` at the size above gives the contraction half of
  `NeutralWindow`.
* `valleyGap_of_trial`: a local Collatz bound and `ValleyPoincare` for an explicit trial function give `ValleyGap`.
* `second_half_of_observable`, `second_half_of_plane`: the second half of `NeutralWindow`, from a lower bound on the
  variance of a neutral observable under `η²`, or from a Rayleigh bound on a plane of explicit trial functions.
* `neutralWindow_of_trials`: both halves together.
* `valleyGap_of_valleyChart`, `contraction_of_valleyChart`: `ValleyChart`, a Gaussian chart as an actual change of
  variables with a pointwise kernel estimate, gives `ValleyGap` through `free_gap` and `perturbed_gap`. This is the
  harmonic approximation in the form still needed. An earlier `GaussianChart` here asked only for a separate
  representing vector for each observable, which `ValleyGap` itself implies at `d = 1`, so it was not a reduction
  and has been removed.

Not proved: `ValleyGap` at the size `exp(-c/n) ‖T‖` for any `ψ`, `ValleyPoincare` with a usable constant, `ValleyChart`,
either trial bound for the second half, and therefore no cutoff-uniform gap of the Wilson operator on any trajectory. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare
import UnifiedTheory.Clay.YangMills.Twisted.TwistedMehler
import UnifiedTheory.Clay.YangMills.SU2HaarSlice
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Arsinh

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSemiclassical
noncomputable section
open MeasureTheory

/-! ## The free many-mode operator -/

section FreeAlgebra

variable {D Ξ : Type*} [Fintype D]

/-- A `k`-th Hadamard power of a Gram matrix is a sum of squares. -/
theorem pow_gram (s : Finset Ξ) (G : D → ℝ) (ξ : Ξ → D → ℝ) (a : Ξ → ℝ) (k : ℕ) :
    ∑ j ∈ s, ∑ l ∈ s, a j * a l * (∑ i, G i * (ξ j i * ξ l i)) ^ k =
      ∑ p : Fin k → D, (∏ t, G (p t)) * (∑ l ∈ s, a l * ∏ t, ξ l (p t)) ^ 2 := by
  have h (j l : Ξ) : a j * a l * (∑ i, G i * (ξ j i * ξ l i)) ^ k =
      ∑ p : Fin k → D, (∏ t, G (p t)) * ((a j * ∏ t, ξ j (p t)) * (a l * ∏ t, ξ l (p t))) := by
    rw [Fintype.sum_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  simp only [h]
  have hR (p : Fin k → D) : (∏ t, G (p t)) * (∑ l ∈ s, a l * ∏ t, ξ l (p t)) ^ 2 =
      ∑ j ∈ s, ∑ l ∈ s, (∏ t, G (p t)) * ((a j * ∏ t, ξ j (p t)) * (a l * ∏ t, ξ l (p t))) := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  simp only [hR]
  rw [Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm (s := Finset.univ)]

theorem exp_series_form (s : Finset Ξ) (G : D → ℝ) (ξ : Ξ → D → ℝ) (a : Ξ → ℝ) :
    HasSum (fun k : ℕ => (∑ j ∈ s, ∑ l ∈ s, a j * a l * (∑ i, G i * (ξ j i * ξ l i)) ^ k) /
      (k.factorial : ℝ)) (∑ j ∈ s, ∑ l ∈ s, a j * a l * Real.exp (∑ i, G i * (ξ j i * ξ l i))) := by
  have hexp (x : ℝ) : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have := hasSum_sum (s := s) fun j _ => hasSum_sum (s := s) fun l _ =>
    (hexp (∑ i, G i * (ξ j i * ξ l i))).mul_left (a j * a l)
  have e : (fun k : ℕ => (∑ j ∈ s, ∑ l ∈ s, a j * a l * (∑ i, G i * (ξ j i * ξ l i)) ^ k) /
      (k.factorial : ℝ)) = fun k : ℕ => ∑ j ∈ s, ∑ l ∈ s,
        a j * a l * ((∑ i, G i * (ξ j i * ξ l i)) ^ k / (k.factorial : ℝ)) := by
    funext k
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]
  exact this

/-- **The positive-definite comparison.** With `0 ≤ R ≤ ρ ≤ 1`, the kernel
`ρ (exp⟨ξ, Gζ⟩ - 1) - (exp⟨ξ, GRζ⟩ - 1)` is positive semidefinite. This is the whole algebraic content
of the many-mode gap: the constant term is the top level, every other term carries a factor `R`. -/
theorem exp_compare (s : Finset Ξ) (G R : D → ℝ) (hG : ∀ i, 0 ≤ G i) (hR : ∀ i, 0 ≤ R i) (ρ : ℝ)
    (hRρ : ∀ i, R i ≤ ρ) (hρ1 : ρ ≤ 1) (ξ : Ξ → D → ℝ) (a : Ξ → ℝ) :
    ∑ j ∈ s, ∑ l ∈ s, a j * a l * (Real.exp (∑ i, (G i * R i) * (ξ j i * ξ l i)) - 1) ≤
      ρ * ∑ j ∈ s, ∑ l ∈ s, a j * a l * (Real.exp (∑ i, G i * (ξ j i * ξ l i)) - 1) := by
  have hA := exp_series_form s G ξ a
  have hB := exp_series_form s (fun i => G i * R i) ξ a
  have hg := (hA.mul_left ρ).sub hB
  have hterm (k : ℕ) (hk : k ∉ ({0} : Finset ℕ)) :
      0 ≤ ρ * ((∑ j ∈ s, ∑ l ∈ s, a j * a l * (∑ i, G i * (ξ j i * ξ l i)) ^ k) / (k.factorial : ℝ)) -
        (∑ j ∈ s, ∑ l ∈ s, a j * a l * (∑ i, (G i * R i) * (ξ j i * ξ l i)) ^ k) / (k.factorial : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
      refine ⟨k - 1, ?_⟩
      have : k ≠ 0 := by simpa using hk
      omega
    rw [pow_gram, pow_gram, ← mul_div_assoc, ← sub_div]
    apply div_nonneg _ (by positivity)
    rw [Finset.mul_sum, sub_nonneg]
    refine Finset.sum_le_sum fun p _ => ?_
    have hR1 : ∀ i, R i ≤ 1 := fun i => (hRρ i).trans hρ1
    have hprod : ∏ t, R (p t) ≤ ρ := by
      rw [Fin.prod_univ_succ]
      have h1 : ∏ t : Fin m, R (p t.succ) ≤ 1 :=
        Finset.prod_le_one (fun t _ => hR _) (fun t _ => hR1 _)
      have h0 : 0 ≤ ∏ t : Fin m, R (p t.succ) := Finset.prod_nonneg fun t _ => hR _
      calc R (p 0) * ∏ t : Fin m, R (p t.succ) ≤ R (p 0) * 1 :=
            mul_le_mul_of_nonneg_left h1 (hR _)
        _ ≤ ρ := by rw [mul_one]; exact hRρ _
    have hGp : 0 ≤ ∏ t, G (p t) := Finset.prod_nonneg fun t _ => hG _
    have hsq := sq_nonneg (∑ l ∈ s, a l * ∏ t, ξ l (p t))
    rw [Finset.prod_mul_distrib]
    calc (∏ t, G (p t)) * (∏ t, R (p t)) * (∑ l ∈ s, a l * ∏ t, ξ l (p t)) ^ 2
        ≤ (∏ t, G (p t)) * ρ * (∑ l ∈ s, a l * ∏ t, ξ l (p t)) ^ 2 := by
          gcongr
      _ = _ := by ring
  have hle := sum_le_hasSum ({0} : Finset ℕ) hterm hg
  simp only [Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] at hle
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
  linarith only [hle]

end FreeAlgebra

section FreeAbstract
open Complex
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [Fintype D]

/-- **The spectral bound from a total family of coherent vectors.** -/
theorem coherent_bound (e : (D → ℝ) → H)
    (hdense : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤)
    (C Lam ρ : ℝ) (hC : 0 < C) (hLam : 0 ≤ Lam) (G R : D → ℝ) (hG : ∀ i, 0 ≤ G i) (hR : ∀ i, 0 ≤ R i)
    (hRρ : ∀ i, R i ≤ ρ) (hρ1 : ρ ≤ 1)
    (hinner : ∀ ξ ζ, inner ℂ (e ξ) (e ζ) = ((C * Real.exp (∑ i, G i * (ξ i * ζ i)) : ℝ) : ℂ))
    (B : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ) (S : ℝ) (hbd : ∀ f g, ‖B f g‖ ≤ S * ‖f‖ * ‖g‖)
    (hB : ∀ ξ ζ, B (e ξ) (e ζ) = ((C * Lam * Real.exp (∑ i, (G i * R i) * (ξ i * ζ i)) : ℝ) : ℂ))
    (f : H) :
    (B f f).re ≤ ρ * Lam * ‖f‖ ^ 2 + (1 - ρ) * Lam * ‖inner ℂ (e 0) f‖ ^ 2 / C := by
  -- on the span
  have hspan : ∀ f ∈ Submodule.span ℂ (Set.range e),
      (B f f).re ≤ ρ * Lam * ‖f‖ ^ 2 + (1 - ρ) * Lam * ‖inner ℂ (e 0) f‖ ^ 2 / C := by
    intro f hf
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hf
    set s := c.support with hs
    have hsum : (c.sum fun i a => a • e i) = ∑ ξ ∈ s, c ξ • e ξ := rfl
    rw [hsum]
    set F := ∑ ξ ∈ s, c ξ • e ξ with hF
    set w : (D → ℝ) → (D → ℝ) → ℝ := fun j l => (c j).re * (c l).re + (c j).im * (c l).im with hw
    have hre (j l : D → ℝ) (x : ℝ) : ((starRingEnd ℂ) (c j) * c l * (x : ℂ)).re = w j l * x := by
      simp only [hw, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have hnorm : ‖F‖ ^ 2 = C * ∑ j ∈ s, ∑ l ∈ s, w j l * Real.exp (∑ i, G i * (j i * l i)) := by
      have h1 : ‖F‖ ^ 2 = (inner ℂ F F : ℂ).re := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      rw [h1, hF, sum_inner, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [inner_smul_left, inner_smul_right, hinner, ← mul_assoc, hre]
      ring
    have hform : (B F F).re = C * Lam * ∑ j ∈ s, ∑ l ∈ s,
        w j l * Real.exp (∑ i, (G i * R i) * (j i * l i)) := by
      rw [hF]
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        Complex.re_sum, Finset.mul_sum, RingHom.id_apply, hB]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      have hsw : ∑ i, G i * R i * (l i * j i) = ∑ i, G i * R i * (j i * l i) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hsw]
      generalize Real.exp (∑ i, G i * R i * (j i * l i)) = x
      simp only [hw, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hΨ : inner ℂ (e 0) F = ((C : ℝ) : ℂ) * ∑ l ∈ s, c l := by
      rw [hF, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [inner_smul_right, hinner]
      simp only [Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, Real.exp_zero, mul_one]
      ring
    have hΨn : ‖inner ℂ (e 0) F‖ ^ 2 = C ^ 2 * ∑ j ∈ s, ∑ l ∈ s, w j l := by
      rw [hΨ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC, mul_pow,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
      congr 1
      simp only [hw, Finset.sum_add_distrib]
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    have hcmp1 := exp_compare s G R hG hR ρ hRρ hρ1 (fun j => j) (fun j => (c j).re)
    have hcmp2 := exp_compare s G R hG hR ρ hRρ hρ1 (fun j => j) (fun j => (c j).im)
    set SA := ∑ j ∈ s, ∑ l ∈ s, w j l * Real.exp (∑ i, G i * (j i * l i)) with hSA
    set SB := ∑ j ∈ s, ∑ l ∈ s, w j l * Real.exp (∑ i, (G i * R i) * (j i * l i)) with hSB
    set W := ∑ j ∈ s, ∑ l ∈ s, w j l with hW
    have hcmp : SB - W ≤ ρ * (SA - W) := by
      have e1 : SB - W = (∑ j ∈ s, ∑ l ∈ s, (c j).re * (c l).re *
          (Real.exp (∑ i, (G i * R i) * (j i * l i)) - 1)) +
          ∑ j ∈ s, ∑ l ∈ s, (c j).im * (c l).im *
          (Real.exp (∑ i, (G i * R i) * (j i * l i)) - 1) := by
        rw [hSB, hW, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [hw]
        ring
      have e2 : SA - W = (∑ j ∈ s, ∑ l ∈ s, (c j).re * (c l).re *
          (Real.exp (∑ i, G i * (j i * l i)) - 1)) +
          ∑ j ∈ s, ∑ l ∈ s, (c j).im * (c l).im *
          (Real.exp (∑ i, G i * (j i * l i)) - 1) := by
        rw [hSA, hW, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [hw]
        ring
      rw [e1, e2, mul_add]
      exact add_le_add hcmp1 hcmp2
    rw [hform, hnorm, hΨn]
    have hCL : 0 ≤ C * Lam := by positivity
    have h1 := mul_le_mul_of_nonneg_left hcmp hCL
    have e3 : (1 - ρ) * Lam * (C ^ 2 * W) / C = C * Lam * ((1 - ρ) * W) := by
      field_simp
    rw [e3]
    nlinarith only [h1]
  -- extend by continuity
  let B' := LinearMap.mkContinuous₂ B S hbd
  have hB' (a b : H) : B' a b = B a b := rfl
  have hcont : Continuous fun f : H => (B f f).re := by
    have h1 : Continuous fun f : H => B' f f :=
      B'.continuous.clm_apply continuous_id
    exact Complex.continuous_re.comp h1
  have hcl : IsClosed {f : H | (B f f).re ≤ ρ * Lam * ‖f‖ ^ 2 +
      (1 - ρ) * Lam * ‖inner ℂ (e 0) f‖ ^ 2 / C} := by
    refine isClosed_le hcont ?_
    fun_prop
  have hmem : f ∈ closure (Submodule.span ℂ (Set.range e) : Set H) := by
    have : f ∈ (Submodule.span ℂ (Set.range e)).topologicalClosure := by
      rw [hdense]
      exact Submodule.mem_top
    exact this
  exact (closure_minimal (fun g hg => hspan g hg) hcl) hmem

end FreeAbstract
section Schur
open Complex
open scoped ComplexConjugate

variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [SFinite μ]

/-- A nonnegative symmetric kernel with bounded row integrals. -/
structure SchurKernel (μ : Measure V) (K : V × V → ℝ) (S : ℝ) : Prop where
  meas : Measurable K
  nonneg : ∀ p, 0 ≤ K p
  row : ∀ x, Integrable (fun y => K (x, y)) μ
  row_le : ∀ x, ∫ y, K (x, y) ∂μ ≤ S
  symm : ∀ x y, K (x, y) = K (y, x)

variable {K : V × V → ℝ} {S : ℝ}

theorem sq_norm_integrable (h : Lp ℂ 2 μ) : Integrable (fun x => ‖h x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).mp (Lp.memLp h)

theorem sq_norm_eq (h : Lp ℂ 2 μ) : ∫ x, ‖h x‖ ^ 2 ∂μ = ‖h‖ ^ 2 := by
  have h1 : ‖h‖ ^ 2 = (inner ℂ h h : ℂ).re := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1, L2.inner_def]
  have h2 : ∀ a : V, inner ℂ (h a) (h a) = ((‖h a‖ ^ 2 : ℝ) : ℂ) := fun a => by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [h2]
  rw [integral_complex_ofReal]
  rfl

theorem weighted_integrable (hK : SchurKernel μ K S) (h : Lp ℂ 2 μ) :
    Integrable (fun p : V × V => K p * ‖h p.1‖ ^ 2) (μ.prod μ) := by
  have hφ := sq_norm_integrable h
  have hm : AEStronglyMeasurable (fun p : V × V => K p * ‖h p.1‖ ^ 2) (μ.prod μ) :=
    hK.meas.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable h).norm.pow 2).comp_fst
  refine (integrable_prod_iff hm).mpr ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact (hK.row x).mul_const (‖h x‖ ^ 2)
  · refine Integrable.mono' (hφ.const_mul S) hm.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun x => ?_)
    have e : ∫ y, ‖K (x, y) * ‖h x‖ ^ 2‖ ∂μ = (∫ y, K (x, y) ∂μ) * ‖h x‖ ^ 2 := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [norm_mul, Real.norm_of_nonneg (hK.nonneg _), norm_pow, norm_norm]
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _), e]
    exact mul_le_mul_of_nonneg_right (hK.row_le x) (by positivity)

theorem weighted_le (hK : SchurKernel μ K S) (h : Lp ℂ 2 μ) :
    ∫ p : V × V, K p * ‖h p.1‖ ^ 2 ∂(μ.prod μ) ≤ S * ‖h‖ ^ 2 := by
  rw [integral_prod _ (weighted_integrable hK h), ← sq_norm_eq, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
    ((sq_norm_integrable h).const_mul S) (Filter.Eventually.of_forall fun x => ?_)
  · exact integral_nonneg fun y => mul_nonneg (hK.nonneg _) (by positivity)
  · dsimp only
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (hK.row_le x) (by positivity)

theorem weighted_integrable' (hK : SchurKernel μ K S) (h : Lp ℂ 2 μ) :
    Integrable (fun p : V × V => K p * ‖h p.2‖ ^ 2) (μ.prod μ) := by
  have := (weighted_integrable hK h).swap
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp, Prod.swap]
  rw [hK.symm]

theorem weighted_le' (hK : SchurKernel μ K S) (h : Lp ℂ 2 μ) :
    ∫ p : V × V, K p * ‖h p.2‖ ^ 2 ∂(μ.prod μ) ≤ S * ‖h‖ ^ 2 := by
  have h1 := integral_prod_swap (μ := μ) (ν := μ) (fun p : V × V => K p * ‖h p.1‖ ^ 2)
  have e : ∫ p : V × V, K p.swap * ‖h p.swap.1‖ ^ 2 ∂(μ.prod μ) =
      ∫ p : V × V, K p * ‖h p.2‖ ^ 2 ∂(μ.prod μ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨a, b⟩ := p
    simp only [Prod.swap]
    rw [hK.symm]
  rw [e] at h1
  rw [h1]
  exact weighted_le hK h

/-- The sesquilinear form of the kernel on `L²`. -/
def formB (K : V × V → ℝ) (f g : Lp ℂ 2 μ) : ℂ :=
  ∫ p : V × V, conj (f p.1) * (K p : ℂ) * g p.2 ∂(μ.prod μ)

theorem form_aesm (hK : SchurKernel μ K S) (f g : Lp ℂ 2 μ) :
    AEStronglyMeasurable (fun p : V × V => conj (f p.1) * (K p : ℂ) * g p.2) (μ.prod μ) := by
  have h1 : AEStronglyMeasurable (fun p : V × V => conj (f p.1)) (μ.prod μ) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).comp_fst
  have h2 : AEStronglyMeasurable (fun p : V × V => (K p : ℂ)) (μ.prod μ) :=
    (Complex.measurable_ofReal.comp hK.meas).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun p : V × V => g p.2) (μ.prod μ) :=
    (Lp.aestronglyMeasurable g).comp_snd
  exact (h1.mul h2).mul h3

theorem form_pointwise (hK : SchurKernel μ K S) (f g : Lp ℂ 2 μ) (t : ℝ) (ht : 0 < t) (p : V × V) :
    ‖conj (f p.1) * (K p : ℂ) * g p.2‖ ≤
      t / 2 * (K p * ‖f p.1‖ ^ 2) + 1 / (2 * t) * (K p * ‖g p.2‖ ^ 2) := by
  have hk := hK.nonneg p
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg hk]
  set a := ‖f p.1‖
  set b := ‖g p.2‖
  have hsq : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  have e : t / 2 * (K p * a ^ 2) + 1 / (2 * t) * (K p * b ^ 2) - a * K p * b =
      K p / (2 * t) * (t * a - b) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ K p / (2 * t) * (t * a - b) ^ 2 := by positivity
  linarith only [e, hnn]

theorem form_integrable (hK : SchurKernel μ K S) (f g : Lp ℂ 2 μ) :
    Integrable (fun p : V × V => conj (f p.1) * (K p : ℂ) * g p.2) (μ.prod μ) := by
  refine Integrable.mono' (((weighted_integrable hK f).const_mul (1 / 2)).add
    ((weighted_integrable' hK g).const_mul (1 / (2 * 1)))) (form_aesm hK f g)
    (Filter.Eventually.of_forall fun p => ?_)
  exact form_pointwise hK f g 1 one_pos p

theorem form_bound_t (hK : SchurKernel μ K S) (f g : Lp ℂ 2 μ) (t : ℝ) (ht : 0 < t) :
    ‖formB K f g‖ ≤ t / 2 * (S * ‖f‖ ^ 2) + 1 / (2 * t) * (S * ‖g‖ ^ 2) := by
  have hi1 := (weighted_integrable hK f).const_mul (t / 2)
  have hi2 := (weighted_integrable' hK g).const_mul (1 / (2 * t))
  have hi12 : Integrable (fun p : V × V => t / 2 * (K p * ‖f p.1‖ ^ 2) +
      1 / (2 * t) * (K p * ‖g p.2‖ ^ 2)) (μ.prod μ) := hi1.add hi2
  refine (norm_integral_le_of_norm_le hi12
    (Filter.Eventually.of_forall fun p => form_pointwise hK f g t ht p)).trans ?_
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left (weighted_le hK f) (show 0 ≤ t / 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (weighted_le' hK g) (show 0 ≤ 1 / (2 * t) by positivity)
  linarith only [h1, h2]

theorem qmp_fst {g g' : V → ℂ} (h : g =ᵐ[μ] g') :
    (fun p : V × V => g p.1) =ᵐ[μ.prod μ] fun p => g' p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp h

theorem qmp_snd {g g' : V → ℂ} (h : g =ᵐ[μ] g') :
    (fun p : V × V => g p.2) =ᵐ[μ.prod μ] fun p => g' p.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp h

/-- The form as a sesquilinear map. -/
def formL (hK : SchurKernel μ K S) : Lp ℂ 2 μ →ₗ⋆[ℂ] Lp ℂ 2 μ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (formB K)
    (fun a b c => by
      unfold formB
      rw [← integral_add (form_integrable hK a c) (form_integrable hK b c)]
      refine integral_congr_ae ?_
      filter_upwards [qmp_fst (Lp.coeFn_add a b)] with p hp
      simp only [hp, Pi.add_apply, map_add]
      ring)
    (fun z a c => by
      unfold formB
      rw [smul_eq_mul]
      change _ = conj z * _
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [qmp_fst (Lp.coeFn_smul z a)] with p hp
      simp only [hp, Pi.smul_apply, smul_eq_mul, map_mul]
      ring)
    (fun a b c => by
      unfold formB
      rw [← integral_add (form_integrable hK a b) (form_integrable hK a c)]
      refine integral_congr_ae ?_
      filter_upwards [qmp_snd (Lp.coeFn_add b c)] with p hp
      simp only [hp, Pi.add_apply]
      ring)
    (fun z a b => by
      unfold formB
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [qmp_snd (Lp.coeFn_smul z b)] with p hp
      simp only [hp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring)

theorem formL_apply (hK : SchurKernel μ K S) (f g : Lp ℂ 2 μ) : formL hK f g = formB K f g := rfl

theorem formL_bound (hK : SchurKernel μ K S) (f g : Lp ℂ 2 μ) :
    ‖formL hK f g‖ ≤ S * ‖f‖ * ‖g‖ := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  have hf' : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hg' : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have h := form_bound_t hK f g (‖g‖ / ‖f‖) (by positivity)
  rw [formL_apply]
  refine h.trans_eq ?_
  field_simp
  ring

end Schur

section FreeMode
open Complex TwistedMehler
open scoped ComplexConjugate

/-- The amplitude of a coherent vector of one mode. -/
def amp (β ρ ξ x : ℝ) : ℝ := Real.exp (-expo β ρ * x ^ 2 + ξ ^ 2 / (8 * expo β ρ))

/-- A coherent vector of one mode: the ground Gaussian times a plane wave, with the normalization that
makes the transfer kernel act by `ξ ↦ ρ ξ`. -/
def coh (β ρ ξ x : ℝ) : ℂ := (amp β ρ ξ x : ℂ) * cexp (I * ξ * x)

theorem coh_continuous (β ρ ξ : ℝ) : Continuous (coh β ρ ξ) := by
  unfold coh amp
  fun_prop

theorem norm_coh (β ρ ξ x : ℝ) : ‖coh β ρ ξ x‖ = amp β ρ ξ x := by
  unfold coh
  have e : I * (ξ : ℂ) * (x : ℂ) = ((ξ * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [norm_mul, e, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
  exact Real.norm_of_nonneg (Real.exp_pos _).le

theorem expo_pos {β ρ : ℝ} (hβ : 0 < β) (h0 : 0 < ρ) (h1 : ρ < 1) : 0 < expo β ρ := by
  unfold expo
  have : 0 < 1 - ρ ^ 2 := by nlinarith only [h0, h1]
  positivity

theorem gauss1 (B : ℝ) (hB : 0 < B) (t : ℝ) :
    ∫ y : ℝ, cexp (I * t * y) * ((Real.exp (-B * y ^ 2) : ℝ) : ℂ) =
      ((Real.sqrt (Real.pi / B) * Real.exp (-t ^ 2 / (4 * B)) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (B : ℂ)) (by simpa using hB) (t : ℂ)
  have e1 (y : ℝ) : cexp (-(B : ℂ) * (y : ℂ) ^ 2) = ((Real.exp (-B * y ^ 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  simp only [e1] at h
  rw [h]
  have e2 : ((Real.pi : ℂ) / (B : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / B) : ℝ) : ℂ) := by
    have e3 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [e3, ← Complex.ofReal_div, ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]
  have e4 : cexp (-(t : ℂ) ^ 2 / (4 * (B : ℂ))) = ((Real.exp (-t ^ 2 / (4 * B)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e2, e4]
  push_cast
  rfl

/-- **The kernel moves a coherent vector.** -/
theorem coh_kernel {β ρ : ℝ} (hβ : 0 < β) (h0 : 0 < ρ) (h1 : ρ < 1) (ξ x : ℝ) :
    ∫ y, ((kernel β (ρ + 1 / ρ - 2) x y : ℝ) : ℂ) * coh β ρ ξ y =
      (lam β ρ : ℂ) * coh β ρ (ρ * ξ) x := by
  set κ := ρ + 1 / ρ - 2 with hκ
  have hrel : ρ + 1 / ρ = κ + 2 := by rw [hκ]; ring
  set E := expo β ρ with hE
  set B := β / (2 * ρ) with hB
  have hBpos : 0 < B := by positivity
  have hEpos : 0 < E := expo_pos hβ h0 h1
  set A := Real.exp (-E * x ^ 2 + ξ ^ 2 / (8 * E)) with hA
  have hpt (y : ℝ) : ((kernel β κ x y : ℝ) : ℂ) * coh β ρ ξ y =
      ((A : ℝ) : ℂ) * cexp (I * ξ * (ρ * x)) *
        (cexp (I * ξ * ((y - ρ * x : ℝ) : ℂ)) * ((Real.exp (-B * (y - ρ * x) ^ 2) : ℝ) : ℂ)) := by
    have hr : kernel β κ x y * amp β ρ ξ y = A * Real.exp (-B * (y - ρ * x) ^ 2) := by
      unfold kernel amp
      rw [hA, ← Real.exp_add, ← Real.exp_add]
      congr 1
      have := exponent_identity β κ ρ hβ h0 hrel x y
      rw [← hE] at *
      rw [← hB] at this
      linarith only [this]
    have hphase : cexp (I * ξ * y) =
        cexp (I * ξ * (ρ * x)) * cexp (I * ξ * ((y - ρ * x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hc : ((kernel β κ x y : ℝ) : ℂ) * ((amp β ρ ξ y : ℝ) : ℂ) =
        ((A : ℝ) : ℂ) * ((Real.exp (-B * (y - ρ * x) ^ 2) : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr
    unfold coh
    rw [hphase]
    linear_combination (cexp (I * ξ * (ρ * x)) * cexp (I * ξ * ((y - ρ * x : ℝ) : ℂ))) * hc
  simp only [hpt]
  rw [integral_const_mul]
  have hshift : ∫ y : ℝ, cexp (I * ξ * ((y - ρ * x : ℝ) : ℂ)) *
      ((Real.exp (-B * (y - ρ * x) ^ 2) : ℝ) : ℂ) =
      ∫ s : ℝ, cexp (I * ξ * (s : ℂ)) * ((Real.exp (-B * s ^ 2) : ℝ) : ℂ) :=
    integral_sub_right_eq_self (μ := volume)
      (fun s : ℝ => cexp (I * ξ * (s : ℂ)) * ((Real.exp (-B * s ^ 2) : ℝ) : ℂ)) (ρ * x)
  rw [hshift, gauss1 B hBpos ξ]
  have hreal : A * Real.exp (-ξ ^ 2 / (4 * B)) = amp β ρ (ρ * ξ) x := by
    unfold amp
    rw [hA, ← Real.exp_add]
    congr 1
    have hne : 1 - ρ ^ 2 ≠ 0 := by
      have : 0 < 1 - ρ ^ 2 := by nlinarith only [h0, h1]
      exact this.ne'
    have e : ξ ^ 2 / (8 * E) + -ξ ^ 2 / (4 * B) = (ρ * ξ) ^ 2 / (8 * E) := by
      rw [hE, hB]
      unfold expo
      field_simp
      ring
    rw [← hE]
    linarith only [e]
  have hphase : cexp (I * ξ * (ρ * x)) = cexp (I * ((ρ * ξ : ℝ) : ℂ) * x) := by
    congr 1
    push_cast
    ring
  unfold coh lam
  rw [hphase, ← hreal]
  push_cast
  ring

/-- **The Gram matrix of coherent vectors.** -/
theorem coh_inner {β ρ : ℝ} (hβ : 0 < β) (h0 : 0 < ρ) (h1 : ρ < 1) (ξ ζ : ℝ) :
    ∫ x : ℝ, coh β ρ ζ x * conj (coh β ρ ξ x) =
      ((Real.sqrt (Real.pi / (2 * expo β ρ)) * Real.exp (ξ * ζ / (4 * expo β ρ)) : ℝ) : ℂ) := by
  set E := expo β ρ with hE
  have hEpos : 0 < E := expo_pos hβ h0 h1
  have hpt (x : ℝ) : coh β ρ ζ x * conj (coh β ρ ξ x) =
      ((Real.exp ((ξ ^ 2 + ζ ^ 2) / (8 * E)) : ℝ) : ℂ) *
        (cexp (I * ((ζ - ξ : ℝ) : ℂ) * x) * ((Real.exp (-(2 * E) * x ^ 2) : ℝ) : ℂ)) := by
    unfold coh
    have hconj : conj (cexp (I * ξ * x)) = cexp (-(I * ξ * x)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hamp : amp β ρ ζ x * amp β ρ ξ x =
        Real.exp ((ξ ^ 2 + ζ ^ 2) / (8 * E)) * Real.exp (-(2 * E) * x ^ 2) := by
      unfold amp
      rw [← hE, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hc : ((amp β ρ ζ x : ℝ) : ℂ) * ((amp β ρ ξ x : ℝ) : ℂ) =
        ((Real.exp ((ξ ^ 2 + ζ ^ 2) / (8 * E)) : ℝ) : ℂ) * ((Real.exp (-(2 * E) * x ^ 2) : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hamp
    have hph : cexp (I * ζ * x) * cexp (-(I * ξ * x)) = cexp (I * ((ζ - ξ : ℝ) : ℂ) * x) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [map_mul, Complex.conj_ofReal, hconj]
    linear_combination (cexp (I * ζ * x) * cexp (-(I * ξ * x))) * hc +
      (((Real.exp ((ξ ^ 2 + ζ ^ 2) / (8 * E)) : ℝ) : ℂ) * ((Real.exp (-(2 * E) * x ^ 2) : ℝ) : ℂ)) * hph
  simp only [hpt]
  rw [integral_const_mul, gauss1 (2 * E) (by positivity) (ζ - ξ), ← Complex.ofReal_mul]
  congr 1
  have e : Real.exp ((ξ ^ 2 + ζ ^ 2) / (8 * E)) * (Real.sqrt (Real.pi / (2 * E)) *
      Real.exp (-(ζ - ξ) ^ 2 / (4 * (2 * E)))) =
      Real.sqrt (Real.pi / (2 * E)) * (Real.exp ((ξ ^ 2 + ζ ^ 2) / (8 * E)) *
        Real.exp (-(ζ - ξ) ^ 2 / (4 * (2 * E)))) := by ring
  rw [e, ← Real.exp_add]
  congr 2
  field_simp
  ring

theorem kernel_le_gauss {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (x y : ℝ) :
    kernel β κ x y ≤ Real.exp (-(β / 2) * (y - x) ^ 2) := by
  unfold kernel
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ β * κ / 4 := by positivity
  nlinarith only [mul_nonneg h1 (sq_nonneg x), mul_nonneg h1 (sq_nonneg y), sq_nonneg (x - y)]

theorem mode_kernel_continuous (β κ : ℝ) : Continuous fun p : ℝ × ℝ => kernel β κ p.1 p.2 := by
  unfold kernel
  fun_prop

theorem kernel_row_integrable {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (x : ℝ) :
    Integrable fun y => kernel β κ x y := by
  refine Integrable.mono' (integrable_shift (β / 2) x (by positivity))
    (((mode_kernel_continuous β κ).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by unfold kernel; exact (Real.exp_pos _).le)]
  exact kernel_le_gauss hβ.le hκ x y

theorem kernel_row_le {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (x : ℝ) :
    ∫ y, kernel β κ x y ≤ Real.sqrt (Real.pi / (β / 2)) := by
  rw [← gaussian_shift (β / 2) x (by positivity)]
  exact integral_mono (kernel_row_integrable hβ hκ x) (integrable_shift _ x (by positivity))
    (fun y => kernel_le_gauss hβ.le hκ x y)

theorem coh_sq_integrable {β ρ : ℝ} (hβ : 0 < β) (h0 : 0 < ρ) (h1 : ρ < 1) (ξ : ℝ) :
    Integrable fun x => ‖coh β ρ ξ x‖ ^ 2 := by
  have hEpos := expo_pos hβ h0 h1
  have h := (integrable_exp_neg_mul_sq (b := 2 * expo β ρ) (by positivity)).const_mul
    (Real.exp (ξ ^ 2 / (4 * expo β ρ)))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [norm_coh]
  unfold amp
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp
  ring

end FreeMode

section FreeManyMode
open Complex TwistedMehler
open scoped ComplexConjugate FourierTransform

variable {d : ℕ}

/-- The configuration space of `d` modes. -/
abbrev EE (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem euclid_integral {𝕜 : Type*} [RCLike 𝕜] (φ : Fin d → ℝ → 𝕜) :
    ∫ x : EE d, ∏ i, φ i (x i) = ∏ i, ∫ t, φ i t := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
  have h := hmp.integral_comp' (fun y : Fin d → ℝ => ∏ i, φ i (y i))
  refine h.trans ?_
  rw [volume_pi]
  exact integral_fintype_prod_eq_prod φ

theorem euclid_integrable {𝕜 : Type*} [RCLike 𝕜] (φ : Fin d → ℝ → 𝕜) (hφ : ∀ i, Integrable (φ i)) :
    Integrable (fun x : EE d => ∏ i, φ i (x i)) := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
  have h : Integrable (fun y : Fin d → ℝ => ∏ i, φ i (y i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hφ
  exact hmp.integrable_comp_of_integrable h

variable (β : ℝ) (ρ : Fin d → ℝ)

/-- A coherent vector of all modes. -/
def cohE (ξ : Fin d → ℝ) (x : EE d) : ℂ := ∏ i, coh β (ρ i) (ξ i) (x i)

/-- The many-mode kernel: a product of free one-mode kernels. -/
def kerE (p : EE d × EE d) : ℝ := ∏ i, kernel β (ρ i + 1 / ρ i - 2) (p.1 i) (p.2 i)

/-- The product of the one-mode eigenvalues. -/
def lamE : ℝ := ∏ i, lam β (ρ i)

/-- The squared norm of the ground vector. -/
def gramC : ℝ := ∏ i, Real.sqrt (Real.pi / (2 * expo β (ρ i)))

/-- The weights of the Gram matrix. -/
def gramG (i : Fin d) : ℝ := 1 / (4 * expo β (ρ i))

theorem cohE_continuous (ξ : Fin d → ℝ) : Continuous (cohE β ρ ξ) := by
  unfold cohE
  refine continuous_finset_prod _ fun i _ => ?_
  have hc : Continuous fun x : EE d => x i := by fun_prop
  exact (coh_continuous β (ρ i) (ξ i)).comp hc

theorem kerE_continuous : Continuous (kerE β ρ) := by
  unfold kerE
  refine continuous_finset_prod _ fun i _ => ?_
  have hc : Continuous fun p : EE d × EE d => (p.1 i, p.2 i) := by fun_prop
  exact (mode_kernel_continuous β _).comp hc

variable {β ρ} (hβ : 0 < β) (h0 : ∀ i, 0 < ρ i) (h1 : ∀ i, ρ i < 1)

include hβ h0 h1

theorem cohE_memLp (ξ : Fin d → ℝ) : MemLp (cohE β ρ ξ) 2 (volume : Measure (EE d)) := by
  refine (memLp_two_iff_integrable_sq_norm (cohE_continuous β ρ ξ).aestronglyMeasurable).mpr ?_
  have h := euclid_integrable (fun i t => ‖coh β (ρ i) (ξ i) t‖ ^ 2)
    (fun i => coh_sq_integrable hβ (h0 i) (h1 i) (ξ i))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  unfold cohE
  rw [norm_prod, Finset.prod_pow]

omit hβ h0 h1 in
theorem kappa_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ r + 1 / r - 2 := by
  have e : r + 1 / r - 2 = (r - 1) ^ 2 / r := by
    field_simp
    ring
  rw [e]
  positivity

/-- The kernel is a Schur kernel. -/
theorem kerE_schur : SchurKernel (volume : Measure (EE d)) (kerE β ρ)
    (∏ _i : Fin d, Real.sqrt (Real.pi / (β / 2))) where
  meas := (kerE_continuous β ρ).measurable
  nonneg := fun p => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  row := fun x => euclid_integrable (fun i t => kernel β (ρ i + 1 / ρ i - 2) (x i) t)
    (fun i => kernel_row_integrable hβ (kappa_nonneg (h0 i)) (x i))
  row_le := fun x => by
    have h := euclid_integral (𝕜 := ℝ) (fun i t => kernel β (ρ i + 1 / ρ i - 2) (x i) t)
    change ∫ y : EE d, ∏ i, kernel β (ρ i + 1 / ρ i - 2) (x i) (y i) ≤ _
    rw [h]
    refine Finset.prod_le_prod (fun i _ => integral_nonneg fun t => (Real.exp_pos _).le)
      (fun i _ => kernel_row_le hβ (kappa_nonneg (h0 i)) (x i))
  symm := fun x y => by
    unfold kerE
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold kernel
    congr 1
    ring

/-- The coherent vector in `L²`. -/
def cv (ξ : Fin d → ℝ) : Lp ℂ 2 (volume : Measure (EE d)) := (cohE_memLp hβ h0 h1 ξ).toLp

theorem cohE_kernel (ζ : Fin d → ℝ) (x : EE d) :
    ∫ y : EE d, ((kerE β ρ (x, y) : ℝ) : ℂ) * cohE β ρ ζ y =
      (lamE β ρ : ℂ) * cohE β ρ (fun i => ρ i * ζ i) x := by
  have e (y : EE d) : ((kerE β ρ (x, y) : ℝ) : ℂ) * cohE β ρ ζ y =
      ∏ i, (((kernel β (ρ i + 1 / ρ i - 2) (x i) (y i) : ℝ) : ℂ) * coh β (ρ i) (ζ i) (y i)) := by
    unfold kerE cohE
    rw [Finset.prod_mul_distrib]
    push_cast
    rfl
  simp only [e]
  rw [euclid_integral (fun i t => ((kernel β (ρ i + 1 / ρ i - 2) (x i) t : ℝ) : ℂ) *
    coh β (ρ i) (ζ i) t)]
  simp only [coh_kernel hβ (h0 _) (h1 _)]
  unfold lamE cohE
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem cohE_inner (ξ ζ : Fin d → ℝ) :
    ∫ x : EE d, cohE β ρ ζ x * conj (cohE β ρ ξ x) =
      ((gramC β ρ * Real.exp (∑ i, gramG β ρ i * (ξ i * ζ i)) : ℝ) : ℂ) := by
  have e (x : EE d) : cohE β ρ ζ x * conj (cohE β ρ ξ x) =
      ∏ i, (coh β (ρ i) (ζ i) (x i) * conj (coh β (ρ i) (ξ i) (x i))) := by
    unfold cohE
    rw [Finset.prod_mul_distrib, map_prod]
  simp only [e]
  rw [euclid_integral (fun i t => coh β (ρ i) (ζ i) t * conj (coh β (ρ i) (ξ i) t))]
  simp only [coh_inner hβ (h0 _) (h1 _)]
  rw [Real.exp_sum, gramC, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold gramG
  have e2 : ξ i * ζ i / (4 * expo β (ρ i)) = 1 / (4 * expo β (ρ i)) * (ξ i * ζ i) := by ring
  rw [e2]

theorem cv_coe (ξ : Fin d → ℝ) : cv hβ h0 h1 ξ =ᵐ[volume] cohE β ρ ξ := MemLp.coeFn_toLp _

theorem cv_inner (ξ ζ : Fin d → ℝ) : inner ℂ (cv hβ h0 h1 ξ) (cv hβ h0 h1 ζ) =
    ((gramC β ρ * Real.exp (∑ i, gramG β ρ i * (ξ i * ζ i)) : ℝ) : ℂ) := by
  rw [L2.inner_def, ← cohE_inner hβ h0 h1 ξ ζ]
  refine integral_congr_ae ?_
  filter_upwards [cv_coe hβ h0 h1 ξ, cv_coe hβ h0 h1 ζ] with x h₁ h₂
  rw [h₁, h₂, RCLike.inner_apply]

theorem cv_form (ξ ζ : Fin d → ℝ) :
    formL (kerE_schur hβ h0 h1) (cv hβ h0 h1 ξ) (cv hβ h0 h1 ζ) =
      ((gramC β ρ * lamE β ρ *
        Real.exp (∑ i, (gramG β ρ i * ρ i) * (ξ i * ζ i)) : ℝ) : ℂ) := by
  rw [formL_apply]
  unfold formB
  have hS := kerE_schur hβ h0 h1
  have hint := form_integrable hS (cv hβ h0 h1 ξ) (cv hβ h0 h1 ζ)
  have hae : (fun p : EE d × EE d => conj (cv hβ h0 h1 ξ p.1) * ((kerE β ρ p : ℝ) : ℂ) * cv hβ h0 h1 ζ p.2)
      =ᵐ[volume.prod volume] fun p => conj (cohE β ρ ξ p.1) * ((kerE β ρ p : ℝ) : ℂ) * cohE β ρ ζ p.2 := by
    filter_upwards [qmp_fst (cv_coe hβ h0 h1 ξ), qmp_snd (cv_coe hβ h0 h1 ζ)] with p h₁ h₂
    rw [h₁, h₂]
  rw [integral_congr_ae hae, integral_prod _ (hint.congr hae)]
  have hin (x : EE d) : (∫ y : EE d, conj (cohE β ρ ξ x) * ((kerE β ρ (x, y) : ℝ) : ℂ) * cohE β ρ ζ y) =
      (lamE β ρ : ℂ) * (cohE β ρ (fun i => ρ i * ζ i) x * conj (cohE β ρ ξ x)) := by
    simp only [mul_assoc]
    rw [integral_const_mul, cohE_kernel hβ h0 h1]
    ring
  simp only [hin]
  rw [integral_const_mul, cohE_inner hβ h0 h1]
  have e : ∑ i, gramG β ρ i * (ξ i * (ρ i * ζ i)) = ∑ i, (gramG β ρ i * ρ i) * (ξ i * ζ i) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  push_cast
  ring

omit hβ h0 h1 in
/-- A coherent vector is the ground Gaussian times a plane wave, up to a positive constant. -/
theorem conj_cohE (ξ : Fin d → ℝ) (x : EE d) :
    conj (cohE β ρ ξ x) =
      ((∏ i, Real.exp (ξ i ^ 2 / (8 * expo β (ρ i))) : ℝ) : ℂ) * cohE β ρ 0 x *
        cexp (((-(∑ i, ξ i * x i) : ℝ) : ℂ) * I) := by
  have h1D (i : Fin d) : conj (coh β (ρ i) (ξ i) (x i)) =
      ((Real.exp (ξ i ^ 2 / (8 * expo β (ρ i))) : ℝ) : ℂ) * coh β (ρ i) 0 (x i) *
        cexp (((-(ξ i * x i) : ℝ) : ℂ) * I) := by
    unfold coh amp
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have e1 : conj (I * (ξ i : ℂ) * (x i : ℂ)) = ((-(ξ i * x i) : ℝ) : ℂ) * I := by
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    rw [e1]
    have e2 : Real.exp (-expo β (ρ i) * x i ^ 2 + ξ i ^ 2 / (8 * expo β (ρ i))) =
        Real.exp (ξ i ^ 2 / (8 * expo β (ρ i))) *
          Real.exp (-expo β (ρ i) * x i ^ 2 + 0 ^ 2 / (8 * expo β (ρ i))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e2]
    push_cast
    simp
  unfold cohE
  rw [map_prod]
  simp only [h1D, Pi.zero_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod]
  congr 2
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]

/-- **Coherent vectors are total.** This is Fourier injectivity. -/
theorem cv_dense : (Submodule.span ℂ (Set.range (cv hβ h0 h1))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  have horth (ξ : Fin d → ℝ) : ∫ x : EE d, f x * conj (cohE β ρ ξ x) = 0 := by
    have h := hf _ (Submodule.subset_span ⟨ξ, rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [cv_coe hβ h0 h1 ξ] with x hx
    rw [hx, RCLike.inner_apply]
  set Γ := cohE β ρ 0 with hΓ
  let g : EE d → ℂ := fun x => Γ x * f x
  have hg : Integrable g := (cohE_memLp hβ h0 h1 0).integrable_mul (Lp.memLp f)
  have hplane (ξ : Fin d → ℝ) : ∫ x : EE d, cexp (((-(∑ i, ξ i * x i) : ℝ) : ℂ) * I) * g x = 0 := by
    have h := horth ξ
    simp only [conj_cohE] at h
    set a : ℝ := ∏ i, Real.exp (ξ i ^ 2 / (8 * expo β (ρ i))) with ha
    have ha0 : (a : ℂ) ≠ 0 := by
      have : 0 < a := Finset.prod_pos fun i _ => Real.exp_pos _
      exact Complex.ofReal_ne_zero.mpr this.ne'
    have e : ∀ x : EE d, f x * ((a : ℂ) * cohE β ρ 0 x * cexp (((-(∑ i, ξ i * x i) : ℝ) : ℂ) * I)) =
        (a : ℂ) * (cexp (((-(∑ i, ξ i * x i) : ℝ) : ℂ) * I) * g x) := fun x => by
      simp only [g, hΓ]
      ring
    simp only [e] at h
    rw [integral_const_mul] at h
    exact (mul_eq_zero.mp h).resolve_left ha0
  have hfour (w : EE d) : 𝓕 g w = 0 := by
    rw [Real.fourier_eq']
    have h := hplane (fun i => 2 * Real.pi * w i)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [smul_eq_mul]
    congr 3
    have e : inner ℝ v w = ∑ i, v i * w i := by
      simp [PiLp.inner_apply, mul_comm]
    rw [e, Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have htest : ∀ φ : EE d → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) φ → HasCompactSupport φ → ∫ x, φ x • g x = 0 := by
    intro φ hφ hs
    let φc : EE d → ℂ := fun x => (φ x : ℂ)
    have hφc : ContDiff ℝ (↑(⊤ : ℕ∞)) φc := Complex.ofRealCLM.contDiff.comp hφ
    have hsc : HasCompactSupport φc := hs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    let Φ₀ : SchwartzMap (EE d) ℂ := hsc.toSchwartzMap hφc
    let Φ : SchwartzMap (EE d) ℂ := 𝓕⁻ Φ₀
    have hΦ : 𝓕 Φ = Φ₀ := FourierTransform.fourier_fourierInv_eq Φ₀
    have hflip : ∫ x, 𝓕 (Φ : EE d → ℂ) x • g x = ∫ w, Φ w • 𝓕 g w := by
      simpa using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (EE d))
        Real.continuous_fourierChar continuous_inner Φ.integrable hg
    have hc : ∀ x, 𝓕 (Φ : EE d → ℂ) x = (φ x : ℂ) := fun x => by
      rw [← SchwartzMap.fourier_coe, hΦ]
      rfl
    simp only [hc, hfour, smul_zero, integral_zero] at hflip
    rw [← hflip]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hgz : ∀ᵐ x, g x = 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hg.locallyIntegrable htest
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hgz] with x hx
  have hΓ0 : Γ x ≠ 0 := by
    rw [hΓ]
    unfold cohE
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    unfold coh
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') (Complex.exp_ne_zero _)
  exact (mul_eq_zero.mp hx).resolve_left hΓ0

/-- **The spectrum of the free many-mode operator.** With `Ψ = cv 0` the ground Gaussian and any `r` above
all the one-mode ratios, the form is at most `r Λ ‖f‖²` plus `(1 - r) Λ` times the squared `Ψ` component of
`f`. The number of modes does not enter. There is no compactness and no Hermite expansion. -/
theorem free_spectral (r : ℝ) (hr : ∀ i, ρ i ≤ r) (hr1 : r ≤ 1) (f : Lp ℂ 2 (volume : Measure (EE d))) :
    (formL (kerE_schur hβ h0 h1) f f).re ≤ r * lamE β ρ * ‖f‖ ^ 2 +
      (1 - r) * lamE β ρ * ‖inner ℂ (cv hβ h0 h1 0) f‖ ^ 2 / gramC β ρ := by
  have hC : 0 < gramC β ρ := Finset.prod_pos fun i _ =>
    Real.sqrt_pos.mpr (div_pos Real.pi_pos (by have := expo_pos hβ (h0 i) (h1 i); positivity))
  have hL : 0 ≤ lamE β ρ := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  refine coherent_bound (cv hβ h0 h1) (cv_dense hβ h0 h1) (gramC β ρ) (lamE β ρ) r hC hL (gramG β ρ) ρ
    (fun i => ?_) (fun i => (h0 i).le) hr hr1 (cv_inner hβ h0 h1) (formL (kerE_schur hβ h0 h1)) _
    (formL_bound _) (cv_form hβ h0 h1) f
  have := expo_pos hβ (h0 i) (h1 i)
  unfold gramG
  positivity

/-- **The free neutral gap.** Orthogonal to the ground Gaussian, the form is at most `r` times the top. -/
theorem free_gap (r : ℝ) (hr : ∀ i, ρ i ≤ r) (hr1 : r ≤ 1) (f : Lp ℂ 2 (volume : Measure (EE d)))
    (hf : inner ℂ (cv hβ h0 h1 0) f = 0) :
    (formL (kerE_schur hβ h0 h1) f f).re ≤ r * lamE β ρ * ‖f‖ ^ 2 := by
  have h := free_spectral hβ h0 h1 r hr hr1 f
  rw [hf] at h
  simpa using h

/-- The top of the form is the product of the one-mode eigenvalues. -/
theorem free_top (f : Lp ℂ 2 (volume : Measure (EE d))) :
    (formL (kerE_schur hβ h0 h1) f f).re ≤ lamE β ρ * ‖f‖ ^ 2 := by
  have hC : 0 < gramC β ρ := Finset.prod_pos fun i _ =>
    Real.sqrt_pos.mpr (div_pos Real.pi_pos (by have := expo_pos hβ (h0 i) (h1 i); positivity))
  have hL : 0 ≤ lamE β ρ := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have h := free_spectral hβ h0 h1 1 (fun i => (h1 i).le) le_rfl f
  simpa using h

/-- The ground Gaussian attains the top. -/
theorem free_ground : formL (kerE_schur hβ h0 h1) (cv hβ h0 h1 0) (cv hβ h0 h1 0) =
    ((lamE β ρ * ‖cv hβ h0 h1 0‖ ^ 2 : ℝ) : ℂ) := by
  have hn : ‖cv hβ h0 h1 0‖ ^ 2 = gramC β ρ := by
    have h1' : ‖cv hβ h0 h1 0‖ ^ 2 = (inner ℂ (cv hβ h0 h1 0) (cv hβ h0 h1 0) : ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h1', cv_inner]
    simp
  rw [cv_form, hn]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.exp_zero, mul_one]
  rw [mul_comm]

end FreeManyMode

section FreeLattice
open TwistedMehler

variable {d : ℕ}

/-- The lowest frequency controls the ratio: `sin(π/2N) ≤ sinh(ω/2)` gives `exp(-ω) ≤ exp(-√2/N)`. -/
theorem ratio_le_of_stiffness (N : ℝ) (hN : 1 ≤ N) (ω : ℝ)
    (h : Real.sin (Real.pi / (2 * N)) ≤ Real.sinh (ω / 2)) :
    Real.exp (-ω) ≤ Real.exp (-(Real.sqrt 2 / N)) := by
  apply Real.exp_le_exp.mpr
  set ω₀ := 2 * Real.arsinh (Real.sin (Real.pi / (2 * N))) with hω₀
  have hNpos : 0 < N := by linarith only [hN]
  have hθ0 : 0 ≤ Real.pi / (2 * N) := by positivity
  have hθ1 : Real.pi / (2 * N) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [Real.pi_pos, hN]
  have hsin0 : 0 ≤ Real.sin (Real.pi / (2 * N)) := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ1
  have hω0 : 0 ≤ ω₀ := by
    rw [hω₀]
    have := Real.arsinh_nonneg_iff.mpr hsin0
    positivity
  have hsinh : Real.sinh (ω₀ / 2) = Real.sin (Real.pi / (2 * N)) := by
    rw [hω₀, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.sinh_arsinh]
  have hwin := (window N hN ω₀ hω0 hsinh).1
  have hmono : ω₀ / 2 ≤ ω / 2 := Real.sinh_le_sinh.mp (hsinh.le.trans h)
  linarith only [hwin, hmono]

/-- **Milestone A₀ for the free model.** With `d` modes of frequencies `ω i`, each at least the lowest
twisted frequency at lattice size `N`, the form orthogonal to the ground Gaussian is at most
`exp(-√2/N)` times the top. Uniform in `d`. So in physical units `L = N a` the gap is at least `√2/L`,
for any number of modes. This is a free theory: nothing here is the Wilson operator. -/
theorem free_gap_lattice {β : ℝ} (hβ : 0 < β) (N : ℝ) (hN : 1 ≤ N) (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i)
    (hstiff : ∀ i, Real.sin (Real.pi / (2 * N)) ≤ Real.sinh (ω i / 2))
    (f : Lp ℂ 2 (volume : Measure (EE d))) :
    let h0 : ∀ i, 0 < Real.exp (-ω i) := fun i => Real.exp_pos _
    let h1 : ∀ i, Real.exp (-ω i) < 1 := fun i => by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith only [hω i])
    inner ℂ (cv hβ h0 h1 0) f = 0 →
      (formL (kerE_schur hβ h0 h1) f f).re ≤
        Real.exp (-(Real.sqrt 2 / N)) * lamE β (fun i => Real.exp (-ω i)) * ‖f‖ ^ 2 := by
  intro h0 h1 hf
  refine free_gap hβ h0 h1 _ (fun i => ratio_le_of_stiffness N hN (ω i) (hstiff i)) ?_ f hf
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ Real.sqrt 2 / N := by positivity
  linarith only [this]

end FreeLattice

section FreePerturb
open Complex
open scoped ComplexConjugate

variable {d : ℕ} {β : ℝ} {ρ : Fin d → ℝ}

/-- **A relative kernel comparison transfers the spectral bound.** Pointwise signs are not needed on the
test function: `|K - c K₀| ≤ δ c K₀` bounds the difference of the two forms by `δ c` times the free form of
`|f|`, and that is at most `δ c Λ ‖f‖²` by `free_top`. -/
theorem perturbed_gap (hβ : 0 < β) (h0 : ∀ i, 0 < ρ i) (h1 : ∀ i, ρ i < 1) (r : ℝ) (hr : ∀ i, ρ i ≤ r)
    (hr1 : r ≤ 1) (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (Kt : EE d × EE d → ℝ) (hKt : Measurable Kt)
    (hcmp : ∀ p, |Kt p - c * kerE β ρ p| ≤ δ * (c * kerE β ρ p))
    (f : Lp ℂ 2 (volume : Measure (EE d))) (hf : inner ℂ (cv hβ h0 h1 0) f = 0) :
    (formB Kt f f).re ≤ c * (r + δ) * lamE β ρ * ‖f‖ ^ 2 := by
  have hS := kerE_schur hβ h0 h1
  have hint := form_integrable hS f f
  -- the modulus of `f` as an element of `L²`
  let af : EE d → ℂ := fun x => ((‖f x‖ : ℝ) : ℂ)
  have hafm : MemLp af 2 (volume : Measure (EE d)) := by
    have h1' : MemLp (fun x => ‖f x‖) 2 (volume : Measure (EE d)) := (Lp.memLp f).norm
    exact h1'.ofReal
  let g : Lp ℂ 2 (volume : Measure (EE d)) := hafm.toLp
  have hgc : g =ᵐ[volume] af := MemLp.coeFn_toLp _
  have hgn : ‖g‖ = ‖f‖ := by
    have h2 := sq_norm_eq g
    have h3 := sq_norm_eq f
    have h4 : ∫ x, ‖g x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hgc] with x hx
      rw [hx]
      simp [af]
    have h5 : ‖g‖ ^ 2 = ‖f‖ ^ 2 := by rw [← h2, ← h3, h4]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h5
  have hG : (formL hS g g).re = ∫ p : EE d × EE d, kerE β ρ p * (‖f p.1‖ * ‖f p.2‖) ∂(volume.prod volume) := by
    rw [formL_apply]
    unfold formB
    have hae : (fun p : EE d × EE d => conj (g p.1) * ((kerE β ρ p : ℝ) : ℂ) * g p.2) =ᵐ[volume.prod volume]
        fun p => ((kerE β ρ p * (‖f p.1‖ * ‖f p.2‖) : ℝ) : ℂ) := by
      filter_upwards [qmp_fst hgc, qmp_snd hgc] with p h₁ h₂
      rw [h₁, h₂]
      simp only [af, Complex.conj_ofReal]
      push_cast
      ring
    rw [integral_congr_ae hae, integral_complex_ofReal]
    rfl
  have htop := free_top hβ h0 h1 g
  rw [hG, hgn] at htop
  have hgap := free_gap hβ h0 h1 r hr hr1 f hf
  -- the difference of the forms
  have habs : Integrable (fun p : EE d × EE d => kerE β ρ p * (‖f p.1‖ * ‖f p.2‖)) (volume.prod volume) := by
    refine (form_integrable hS f f).norm.congr (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hS.nonneg p)]
    ring
  have hreG : (formL (kerE_schur hβ h0 h1) f f).re = ∫ p : EE d × EE d,
      (conj (f p.1) * ((kerE β ρ p : ℝ) : ℂ) * f p.2).re ∂(volume.prod volume) := by
    rw [formL_apply]
    unfold formB
    exact (reCLM.integral_comp_comm hint).symm
  have hKi : Integrable (fun p : EE d × EE d => conj (f p.1) * ((Kt p : ℝ) : ℂ) * f p.2)
      (volume.prod volume) := by
    refine Integrable.mono' (habs.const_mul ((1 + δ) * c)) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1' : AEStronglyMeasurable (fun p : EE d × EE d => conj (f p.1)) (volume.prod volume) :=
        (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).comp_fst
      have h2' : AEStronglyMeasurable (fun p : EE d × EE d => ((Kt p : ℝ) : ℂ)) (volume.prod volume) :=
        (Complex.measurable_ofReal.comp hKt).aestronglyMeasurable
      have h3' : AEStronglyMeasurable (fun p : EE d × EE d => f p.2) (volume.prod volume) :=
        (Lp.aestronglyMeasurable f).comp_snd
      exact (h1'.mul h2').mul h3'
    · rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      have hk := hS.nonneg p
      have hK' : |Kt p| ≤ (1 + δ) * c * kerE β ρ p := by
        have h2 := abs_sub_abs_le_abs_sub (Kt p) (c * kerE β ρ p)
        have h3 := hcmp p
        rw [abs_of_nonneg (mul_nonneg hc hk)] at h2
        nlinarith only [h2, h3]
      have hff : 0 ≤ ‖f p.1‖ * ‖f p.2‖ := by positivity
      calc ‖f p.1‖ * |Kt p| * ‖f p.2‖ = |Kt p| * (‖f p.1‖ * ‖f p.2‖) := by ring
        _ ≤ (1 + δ) * c * kerE β ρ p * (‖f p.1‖ * ‖f p.2‖) := mul_le_mul_of_nonneg_right hK' hff
        _ = _ := by ring
  have hreK : (formB Kt f f).re = ∫ p : EE d × EE d,
      (conj (f p.1) * ((Kt p : ℝ) : ℂ) * f p.2).re ∂(volume.prod volume) := by
    unfold formB
    exact (reCLM.integral_comp_comm hKi).symm
  have hpt (p : EE d × EE d) : (conj (f p.1) * ((Kt p : ℝ) : ℂ) * f p.2).re ≤
      c * (conj (f p.1) * ((kerE β ρ p : ℝ) : ℂ) * f p.2).re +
        δ * c * (kerE β ρ p * (‖f p.1‖ * ‖f p.2‖)) := by
    set z := conj (f p.1) * f p.2 with hz
    have e1 : conj (f p.1) * ((Kt p : ℝ) : ℂ) * f p.2 = ((Kt p : ℝ) : ℂ) * z := by rw [hz]; ring
    have e2 : conj (f p.1) * ((kerE β ρ p : ℝ) : ℂ) * f p.2 = ((kerE β ρ p : ℝ) : ℂ) * z := by
      rw [hz]
      ring
    rw [e1, e2, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hzn : |z.re| ≤ ‖f p.1‖ * ‖f p.2‖ := by
      have := Complex.abs_re_le_norm z
      rwa [hz, norm_mul, RCLike.norm_conj] at this
    have hc' := hcmp p
    have hd : (Kt p - c * kerE β ρ p) * z.re ≤ δ * (c * kerE β ρ p) * (‖f p.1‖ * ‖f p.2‖) := by
      calc _ ≤ |(Kt p - c * kerE β ρ p) * z.re| := le_abs_self _
        _ = |Kt p - c * kerE β ρ p| * |z.re| := abs_mul _ _
        _ ≤ δ * (c * kerE β ρ p) * (‖f p.1‖ * ‖f p.2‖) :=
          mul_le_mul hc' hzn (abs_nonneg _) (by have := hS.nonneg p; positivity)
    nlinarith only [hd]
  have hiG : Integrable (fun p : EE d × EE d => (conj (f p.1) * ((kerE β ρ p : ℝ) : ℂ) * f p.2).re)
      (volume.prod volume) := reCLM.integrable_comp hint
  have hiK : Integrable (fun p : EE d × EE d => (conj (f p.1) * ((Kt p : ℝ) : ℂ) * f p.2).re)
      (volume.prod volume) := reCLM.integrable_comp hKi
  have hsum : Integrable (fun p : EE d × EE d => c * (conj (f p.1) * ((kerE β ρ p : ℝ) : ℂ) * f p.2).re +
      δ * c * (kerE β ρ p * (‖f p.1‖ * ‖f p.2‖))) (volume.prod volume) :=
    (hiG.const_mul c).add (habs.const_mul (δ * c))
  have hmono := integral_mono hiK hsum hpt
  rw [integral_add (hiG.const_mul c) (habs.const_mul (δ * c)), integral_const_mul, integral_const_mul,
    ← hreK, ← hreG] at hmono
  have h1' := mul_le_mul_of_nonneg_left hgap hc
  have h2' := mul_le_mul_of_nonneg_left htop (mul_nonneg hδ hc)
  have e : c * (r + δ) * lamE β ρ * ‖f‖ ^ 2 =
      c * (r * lamE β ρ * ‖f‖ ^ 2) + δ * c * (lamE β ρ * ‖f‖ ^ 2) := by ring
  rw [e]
  linarith only [hmono, h1', h2']

end FreePerturb


/-! ### Haar measure in Lebesgue coordinates -/

section Gnomonic
open SU2HaarSlice SU2HaarSphere SU2QuaternionEquivalence RegulatedGauge
open scoped ENNReal Pointwise

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The quaternion with real part `a` and imaginary part `t`. -/
def quat (a : ℝ) (t : R3) : Quaternion ℝ := coordinateSplit.symm (a, t)

theorem quat_split (a : ℝ) (t : R3) : coordinateSplit (quat a t) = (a, t) :=
  coordinateSplit.apply_symm_apply _

theorem quat_re (a : ℝ) (t : R3) : (quat a t).re = a := by
  rw [← coordinateSplit_re, quat_split]

theorem quat_norm_sq (a : ℝ) (t : R3) : ‖quat a t‖ ^ 2 = a ^ 2 + ‖t‖ ^ 2 := by
  rw [norm_sq_split, quat_split]

theorem split_smul (r : ℝ) (q : Quaternion ℝ) :
    coordinateSplit (r • q) = (r * (coordinateSplit q).1, r • (coordinateSplit q).2) := by
  refine Prod.ext ?_ ?_
  · simp only [coordinateSplit_re, Quaternion.re_smul, smul_eq_mul]
  · simp only [coordinateSplit_im]
    ext i
    fin_cases i <;> simp

theorem quat_smul (r a : ℝ) (t : R3) : r • quat a t = quat (r * a) (r • t) := by
  apply coordinateSplit.injective
  rw [quat_split, split_smul, quat_split]

/-- The point of the unit sphere above `(1, t)`. -/
def gnom (t : R3) : Quaternion ℝ := (Real.sqrt (1 + ‖t‖ ^ 2))⁻¹ • quat 1 t

theorem root_pos (t : R3) : 0 < Real.sqrt (1 + ‖t‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)

theorem gnom_norm (t : R3) : ‖gnom t‖ = 1 := by
  have hs := root_pos t
  have h2 : ‖quat 1 t‖ = Real.sqrt (1 + ‖t‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (quat 1 t)), quat_norm_sq, one_pow]
  rw [gnom, norm_smul, h2, norm_inv, Real.norm_eq_abs, abs_of_pos hs, inv_mul_cancel₀ hs.ne']

/-- **The gnomonic coordinate on `Q`.** It covers the half `0 < Re q` once. -/
def gnomQ (t : R3) : UnitQuaternion := ⟨gnom t, (mem_unitary_iff_norm_one _).mpr (gnom_norm t)⟩

theorem gnomQ_re (t : R3) : ((gnomQ t : UnitQuaternion) : Quaternion ℝ).re = (Real.sqrt (1 + ‖t‖ ^ 2))⁻¹ := by
  change (gnom t).re = _
  rw [gnom, Quaternion.re_smul, quat_re, smul_eq_mul, mul_one]

theorem gnomQ_re_pos (t : R3) : 0 < ((gnomQ t : UnitQuaternion) : Quaternion ℝ).re := by
  rw [gnomQ_re]
  exact inv_pos.mpr (root_pos t)

theorem gnomQ_measurable : Measurable gnomQ := by
  have h : Measurable fun t : R3 => quat 1 t :=
    coordinateSplit.symm.measurable.comp (measurable_const.prodMk measurable_id)
  have h' : Measurable fun t : R3 => (Real.sqrt (1 + ‖t‖ ^ 2))⁻¹ :=
    (((measurable_const.add (measurable_norm.pow_const 2))).sqrt).inv
  have hg : Measurable gnom := h'.smul h
  let g' : R3 → QuaternionSphere := fun t => ⟨gnom t, by simpa using gnom_norm t⟩
  have hg' : Measurable g' := hg.subtype_mk
  exact sphereEquivalence.symm.measurable.comp hg'

/-- A point of the upper half is the gnomonic point of `Im q / Re q`. -/
theorem gnomQ_surj (q : UnitQuaternion) (hq : 0 < (q : Quaternion ℝ).re) :
    gnomQ ((((q : Quaternion ℝ).re)⁻¹) • (coordinateSplit (q : Quaternion ℝ)).2) = q := by
  set a := (q : Quaternion ℝ).re with ha
  set w := (coordinateSplit (q : Quaternion ℝ)).2 with hw
  apply Subtype.ext
  change gnom (a⁻¹ • w) = q
  have hn : ‖(q : Quaternion ℝ)‖ = 1 := by simp
  have hsum : a ^ 2 + ‖w‖ ^ 2 = 1 := by
    have := norm_sq_split (q : Quaternion ℝ)
    rw [hn, coordinateSplit_re, ← ha, ← hw] at this
    linarith only [this]
  have hroot : Real.sqrt (1 + ‖a⁻¹ • w‖ ^ 2) = a⁻¹ := by
    have e : 1 + ‖a⁻¹ • w‖ ^ 2 = (a⁻¹) ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      field_simp
      linarith only [hsum]
    rw [e, Real.sqrt_sq (inv_pos.mpr hq).le]
  apply coordinateSplit.injective
  rw [gnom, hroot, inv_inv, quat_smul, quat_split, mul_one, smul_smul, mul_inv_cancel₀ hq.ne', one_smul]
  refine Prod.ext ?_ ?_
  · rw [coordinateSplit_re]
  · rfl

/-- **The cone over a subset of the upper half, in product coordinates.** -/
theorem cone_coords (s : Set UnitQuaternion) (hsub : ∀ q ∈ s, 0 < (q : Quaternion ℝ).re) (x : Quaternion ℝ) :
    x ∈ Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereEquivalence '' s)) ↔
      0 < (coordinateSplit x).1 ∧ (coordinateSplit x).1 ^ 2 + ‖(coordinateSplit x).2‖ ^ 2 < 1 ∧
        gnomQ (((coordinateSplit x).1)⁻¹ • (coordinateSplit x).2) ∈ s := by
  constructor
  · rintro ⟨r, hr, _, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    change 0 < (coordinateSplit (r • (q : Quaternion ℝ))).1 ∧
      (coordinateSplit (r • (q : Quaternion ℝ))).1 ^ 2 +
        ‖(coordinateSplit (r • (q : Quaternion ℝ))).2‖ ^ 2 < 1 ∧
      gnomQ ((coordinateSplit (r • (q : Quaternion ℝ))).1⁻¹ • (coordinateSplit (r • (q : Quaternion ℝ))).2) ∈ s
    rw [split_smul]
    have hre := hsub q hq
    have hn : ‖(q : Quaternion ℝ)‖ = 1 := by simp
    have hs := norm_sq_split (q : Quaternion ℝ)
    rw [hn] at hs
    rw [coordinateSplit_re] at *
    refine ⟨mul_pos hr.1 hre, ?_, ?_⟩
    · rw [norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs]
      have hr2 : r ^ 2 < 1 := by nlinarith only [hr.1, hr.2]
      nlinarith only [hr2, hs]
    · have : (r * (q : Quaternion ℝ).re)⁻¹ • r • (coordinateSplit (q : Quaternion ℝ)).2 =
          ((q : Quaternion ℝ).re)⁻¹ • (coordinateSplit (q : Quaternion ℝ)).2 := by
        rw [smul_smul]
        congr 1
        field_simp [hr.1.ne']
      rw [this, gnomQ_surj q hre]
      exact hq
  · rintro ⟨ha, hlt, hmem⟩
    set a := (coordinateSplit x).1 with hadef
    set w := (coordinateSplit x).2 with hwdef
    have hxq : x = quat a w := by
      apply coordinateSplit.injective
      rw [quat_split]
    set t := a⁻¹ • w with ht
    have hroot : a * Real.sqrt (1 + ‖t‖ ^ 2) = Real.sqrt (a ^ 2 + ‖w‖ ^ 2) := by
      rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
      congr 1
      rw [ht, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      field_simp
    set r := Real.sqrt (a ^ 2 + ‖w‖ ^ 2) with hr
    have hrpos : 0 < r := by
      rw [← hroot]
      exact mul_pos ha (root_pos t)
    have hr1 : r < 1 := by
      rw [hr, Real.sqrt_lt' one_pos]
      linarith only [hlt]
    refine ⟨r, ⟨hrpos, hr1⟩, _, ⟨_, ⟨gnomQ t, hmem, rfl⟩, rfl⟩, ?_⟩
    change r • gnom t = x
    rw [gnom, smul_smul, ← hroot, mul_assoc, mul_inv_cancel₀ (root_pos t).ne', mul_one, quat_smul, mul_one,
      ht, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hxq]

/-- The integral of `a³` up to the radius of the cone. -/
theorem lintegral_cube (R : ℝ) (hR : 0 < R) :
    ∫⁻ a in Set.Ioo (0 : ℝ) R, ENNReal.ofReal (a ^ 3) = ENNReal.ofReal (R ^ 4 / 4) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le, integral_pow]
    norm_num
  · exact (continuous_pow 3).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun a ha => ?_)
    have := ha.1
    positivity

/-- **The volume of the cone.** Fubini in the product `(a, t)`, with `w = a t`. -/
theorem cone_volume (s : Set UnitQuaternion) (hs : MeasurableSet s)
    (hsub : ∀ q ∈ s, 0 < (q : Quaternion ℝ).re) :
    volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereEquivalence '' s))) =
      ∫⁻ t : R3, (gnomQ ⁻¹' s).indicator (fun t => ENNReal.ofReal ((1 + ‖t‖ ^ 2)⁻¹ ^ 2 / 4)) t := by
  set C := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereEquivalence '' s)) with hC
  have hTm : MeasurableSet (gnomQ ⁻¹' s) := gnomQ_measurable hs
  -- `E`, the cone in the product coordinates
  set E : Set (ℝ × R3) := {p | 0 < p.1 ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 ∧ gnomQ (p.1⁻¹ • p.2) ∈ s} with hE
  have hEm : MeasurableSet E := by
    have h1 : Measurable fun p : ℝ × R3 => p.1 := measurable_fst
    have h2 : Measurable fun p : ℝ × R3 => p.1 ^ 2 + ‖p.2‖ ^ 2 :=
      (measurable_fst.pow_const 2).add (measurable_snd.norm.pow_const 2)
    have h3 : Measurable fun p : ℝ × R3 => p.1⁻¹ • p.2 := measurable_fst.inv.smul measurable_snd
    exact (measurableSet_lt measurable_const h1).inter
      ((measurableSet_lt h2 measurable_const).inter (gnomQ_measurable.comp h3 hs))
  have hCE : volume C = (volume.prod volume) E := by
    have hpre : coordinateSplit ⁻¹' E = C := by
      ext x
      rw [hC, cone_coords s hsub]
      rfl
    rw [← hpre]
    exact coordinateSplit_preserving.measure_preimage hEm.nullMeasurableSet
  rw [hCE, Measure.prod_apply hEm]
  -- the density on `a`
  let d : ℝ → ℝ≥0∞ := fun a => (Set.Ioi (0 : ℝ)).indicator (fun a => ENNReal.ofReal (a ^ 3)) a
  have hdm : Measurable d := ((measurable_id.pow_const 3).ennreal_ofReal).indicator measurableSet_Ioi
  -- `E'`, the same region in the coordinates `(a, t)`
  set E' : Set (ℝ × R3) := {p | 0 < p.1 ∧ p.1 ^ 2 * (1 + ‖p.2‖ ^ 2) < 1 ∧ gnomQ p.2 ∈ s} with hE'
  have hE'm : MeasurableSet E' := by
    have h1 : Measurable fun p : ℝ × R3 => p.1 := measurable_fst
    have h2 : Measurable fun p : ℝ × R3 => p.1 ^ 2 * (1 + ‖p.2‖ ^ 2) :=
      (measurable_fst.pow_const 2).mul (measurable_const.add (measurable_snd.norm.pow_const 2))
    exact (measurableSet_lt measurable_const h1).inter
      ((measurableSet_lt h2 measurable_const).inter (gnomQ_measurable.comp measurable_snd hs))
  have hfiber (a : ℝ) : volume (Prod.mk a ⁻¹' E) = d a * volume (Prod.mk a ⁻¹' E') := by
    by_cases ha : 0 < a
    · have hset : Prod.mk a ⁻¹' E = a • (Prod.mk a ⁻¹' E') := by
        ext w
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
        simp only [Set.mem_preimage, hE, hE', Set.mem_setOf_eq]
        have e : a ^ 2 * (1 + ‖a⁻¹ • w‖ ^ 2) = a ^ 2 + ‖w‖ ^ 2 := by
          rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          field_simp
        rw [e]
      rw [hset, Measure.addHaar_smul]
      have hdim : Module.finrank ℝ R3 = 3 := by simp
      rw [hdim]
      simp only [d, Set.indicator_of_mem (Set.mem_Ioi.mpr ha), abs_of_pos (pow_pos ha 3)]
    · have h1 : Prod.mk a ⁻¹' E = ∅ := by
        ext w
        simp only [Set.mem_preimage, hE, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => ha h.1
      have hd : d a = 0 := Set.indicator_of_notMem ha _
      rw [h1, hd]
      simp
  simp only [hfiber]
  -- Fubini
  have hswap : ∫⁻ a, d a * volume (Prod.mk a ⁻¹' E') =
      ((volume.withDensity d).prod volume) E' := by
    rw [Measure.prod_apply hE'm, lintegral_withDensity_eq_lintegral_mul _ hdm
      (measurable_measure_prodMk_left hE'm)]
    rfl
  rw [hswap, Measure.prod_apply_symm hE'm]
  refine lintegral_congr fun t => ?_
  by_cases ht : gnomQ t ∈ s
  · set R := (Real.sqrt (1 + ‖t‖ ^ 2))⁻¹ with hR
    have hRpos : 0 < R := inv_pos.mpr (root_pos t)
    have hRsq : R ^ 2 = (1 + ‖t‖ ^ 2)⁻¹ := by
      rw [hR, inv_pow, Real.sq_sqrt (by positivity)]
    have hset : (fun a : ℝ => (a, t)) ⁻¹' E' = Set.Ioo 0 R := by
      ext a
      simp only [Set.mem_preimage, hE', Set.mem_setOf_eq, ht, and_true, Set.mem_Ioo]
      refine and_congr_right fun ha => ?_
      have h1p : 0 < 1 + ‖t‖ ^ 2 := by positivity
      rw [← lt_div_iff₀ h1p, one_div, ← hRsq]
      exact sq_lt_sq₀ ha.le hRpos.le
    rw [hset, withDensity_apply _ measurableSet_Ioo, Set.indicator_of_mem (show t ∈ gnomQ ⁻¹' s from ht)]
    have hd : ∫⁻ a in Set.Ioo 0 R, d a = ∫⁻ a in Set.Ioo 0 R, ENNReal.ofReal (a ^ 3) :=
      setLIntegral_congr_fun measurableSet_Ioo fun a ha => Set.indicator_of_mem (Set.mem_Ioi.mpr ha.1) _
    rw [hd, lintegral_cube R hRpos]
    congr 2
    rw [← hRsq]
    ring
  · have hset : (fun a : ℝ => (a, t)) ⁻¹' E' = ∅ := by
      ext a
      simp only [Set.mem_preimage, hE', Set.mem_setOf_eq, ht, and_false, Set.mem_empty_iff_false]
    rw [hset, Set.indicator_of_notMem (show t ∉ gnomQ ⁻¹' s from ht)]
    simp

/-- The density of Haar measure in the gnomonic coordinate. -/
def gnomDensity (t : R3) : ℝ := (2 * Real.pi ^ 2)⁻¹ * ((1 + ‖t‖ ^ 2)⁻¹) ^ 2

theorem gnomDensity_nonneg (t : R3) : 0 ≤ gnomDensity t := by
  unfold gnomDensity
  positivity

theorem gnomDensity_measurable : Measurable gnomDensity := by
  unfold gnomDensity
  exact measurable_const.mul
    ((measurable_const.add (measurable_norm.pow_const 2)).inv.pow_const 2)

/-- The measure on `ℝ³` that is Haar measure on the upper half. -/
def gnomMeasure : Measure R3 := volume.withDensity fun t => ENNReal.ofReal (gnomDensity t)

/-- **Haar measure on `Q` in Lebesgue coordinates.** On the half `0 < Re q`, Haar measure is the image under `gnomQ`
of the explicit density `(2π²)⁻¹ (1 + |t|²)⁻²`. No approximation. -/
theorem haar_gnomonic : (compactHaar UnitQuaternion).restrict {q | 0 < (q : Quaternion ℝ).re} =
    Measure.map gnomQ gnomMeasure := by
  have hHm : MeasurableSet {q : UnitQuaternion | 0 < (q : Quaternion ℝ).re} :=
    measurableSet_lt measurable_const (Quaternion.continuous_re.comp continuous_subtype_val).measurable
  ext s hs
  set H := {q : UnitQuaternion | 0 < (q : Quaternion ℝ).re} with hH
  rw [Measure.restrict_apply hs, Measure.map_apply gnomQ_measurable hs]
  have hs' : MeasurableSet (s ∩ H) := hs.inter hHm
  have hsph : MeasurableSet (sphereEquivalence '' (s ∩ H)) := by
    have := sphereEquivalence.symm.measurable hs'
    rwa [Homeomorph.preimage_symm] at this
  have h1 : compactHaar UnitQuaternion (s ∩ H) = normalizedSphere (sphereEquivalence '' (s ∩ H)) := by
    have h := sphereEquivalence_preserving.measure_preimage hsph.nullMeasurableSet
    rwa [sphereEquivalence.preimage_image] at h
  have hpre : gnomQ ⁻¹' s = gnomQ ⁻¹' (s ∩ H) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_inter_iff, hH, Set.mem_setOf_eq, gnomQ_re_pos, and_true]
  have hTm : MeasurableSet (gnomQ ⁻¹' (s ∩ H)) := gnomQ_measurable hs'
  rw [h1, normalizedSphere_apply _ hsph, cone_volume _ hs' fun q hq => hq.2, quaternion_unitBall_volume, hpre,
    gnomMeasure, withDensity_apply _ hTm, lintegral_indicator hTm, ENNReal.div_eq_inv_mul]
  rw [← lintegral_const_mul' _ _ (by
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (by positivity)).ne')]
  refine setLIntegral_congr_fun hTm fun t _ => ?_
  have hp : (0 : ℝ) < Real.pi ^ 2 / 2 := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (inv_pos.mpr hp).le]
  congr 1
  unfold gnomDensity
  field_simp
  ring

/-- The same statement for integrals. -/
theorem integral_gnomonic (F : UnitQuaternion → ℝ) (hF : Measurable F) :
    ∫ q in {q : UnitQuaternion | 0 < (q : Quaternion ℝ).re}, F q ∂compactHaar UnitQuaternion =
      ∫ t : R3, gnomDensity t * F (gnomQ t) := by
  rw [haar_gnomonic, integral_map gnomQ_measurable.aemeasurable hF.aestronglyMeasurable, gnomMeasure,
    integral_withDensity_eq_integral_toReal_smul gnomDensity_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change (ENNReal.ofReal (gnomDensity t)).toReal • F (gnomQ t) = _
  rw [ENNReal.toReal_ofReal (gnomDensity_nonneg t), smul_eq_mul]

instance gnomMeasure_finite : IsFiniteMeasure gnomMeasure := by
  constructor
  have h := congrArg (fun m => m Set.univ) haar_gnomonic
  simp only at h
  rw [Measure.map_apply gnomQ_measurable MeasurableSet.univ, Set.preimage_univ] at h
  rw [← h]
  exact measure_lt_top _ _

/-- The half of `Q` around a reference element. -/
def nearRef (r : UnitQuaternion) : Set UnitQuaternion := {q | 0 < ((r⁻¹ * q : UnitQuaternion) : Quaternion ℝ).re}

theorem nearRef_measurable (r : UnitQuaternion) : MeasurableSet (nearRef r) :=
  measurableSet_lt measurable_const
    (Quaternion.continuous_re.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))).measurable

/-- **Haar measure around a reference element, in Lebesgue coordinates.** -/
theorem haar_near (r : UnitQuaternion) :
    (compactHaar UnitQuaternion).restrict (nearRef r) = Measure.map (fun t => r * gnomQ t) gnomMeasure := by
  have hmp := (measurePreserving_mul_left (compactHaar UnitQuaternion) r).restrict_preimage (nearRef_measurable r)
  have hpre : (fun q => r * q) ⁻¹' nearRef r = {q : UnitQuaternion | 0 < (q : Quaternion ℝ).re} := by
    ext q
    simp only [nearRef, Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel_left]
  rw [hpre] at hmp
  rw [← hmp.map_eq, haar_gnomonic, Measure.map_map (measurable_const_mul r) gnomQ_measurable]
  rfl

variable {E : Type*} [Fintype E]

/-- **The product of `haar_near`.** On the fields with every link in the half around a reference field, product Haar
measure is the image of the product of the explicit densities. This is the Haar-to-Lebesgue Jacobian on a product of
`S³` factors, exactly. -/
theorem pi_near (r : E → UnitQuaternion) :
    (Measure.pi fun _ : E => compactHaar UnitQuaternion).restrict (Set.pi Set.univ fun e => nearRef (r e)) =
      Measure.map (fun (t : E → R3) e => r e * gnomQ (t e)) (Measure.pi fun _ : E => gnomMeasure) := by
  have hmap := Measure.pi_map_pi (μ := fun _ : E => gnomMeasure) (f := fun e t => r e * gnomQ t) fun e =>
    ((measurable_const_mul (r e)).comp gnomQ_measurable).aemeasurable
  rw [Measure.restrict_pi_pi, hmap]
  congr 1
  funext e
  exact haar_near (r e)

/-- The same statement for a function that vanishes off the near set. -/
theorem integral_pi_near (r : E → UnitQuaternion) (F : (E → UnitQuaternion) → ℝ) (hF : Measurable F)
    (hsupp : ∀ w, (∃ e, w e ∉ nearRef (r e)) → F w = 0) :
    ∫ w, F w ∂(Measure.pi fun _ : E => compactHaar UnitQuaternion) =
      ∫ t, F (fun e => r e * gnomQ (t e)) ∂(Measure.pi fun _ : E => gnomMeasure) := by
  have hm : Measurable fun (t : E → R3) e => r e * gnomQ (t e) :=
    measurable_pi_iff.mpr fun e =>
      (measurable_const_mul (r e)).comp (gnomQ_measurable.comp (measurable_pi_apply e))
  rw [← integral_map hm.aemeasurable hF.aestronglyMeasurable, ← pi_near]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => hsupp w ?_).symm
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hw
  exact hw

end Gnomonic

section Frame
open SU2QuaternionEquivalence RegulatedGauge

variable {E : Type*} [Fintype E]

/-- A global rotation of a field. -/
def conjF (g : UnitQuaternion) (x : E → UnitQuaternion) : E → UnitQuaternion := fun e => g * x e * g⁻¹

theorem conjF_mul (g h : UnitQuaternion) (x : E → UnitQuaternion) : conjF g (conjF h x) = conjF (g * h) x := by
  funext e
  simp only [conjF, mul_inv_rev]
  group

theorem conjF_measurable : Measurable fun p : UnitQuaternion × (E → UnitQuaternion) => conjF p.1 p.2 := by
  refine measurable_pi_iff.mpr fun e => ?_
  change Measurable fun p : UnitQuaternion × (E → UnitQuaternion) => p.1 * p.2 e * p.1⁻¹
  have a : Measurable fun p : UnitQuaternion × (E → UnitQuaternion) => p.1 := measurable_fst
  have b : Measurable fun p : UnitQuaternion × (E → UnitQuaternion) => p.2 e :=
    (measurable_pi_apply e).comp measurable_snd
  exact (a.mul b).mul a.inv

theorem conjF_preserving (g : UnitQuaternion) :
    MeasurePreserving (conjF g : (E → UnitQuaternion) → (E → UnitQuaternion))
      (Measure.pi fun _ => compactHaar UnitQuaternion) (Measure.pi fun _ => compactHaar UnitQuaternion) := by
  have h : MeasurePreserving (fun q : UnitQuaternion => g * q * g⁻¹) (compactHaar UnitQuaternion)
      (compactHaar UnitQuaternion) :=
    (measurePreserving_mul_right (compactHaar UnitQuaternion) g⁻¹).comp
      (measurePreserving_mul_left (compactHaar UnitQuaternion) g)
  exact measurePreserving_pi (fun _ : E => compactHaar UnitQuaternion) (fun _ : E => compactHaar UnitQuaternion)
    (f := fun _ q => g * q * g⁻¹) fun _ => h

/-- The set of fields with every link in the half around a reference field. -/
def nearSet (r : E → UnitQuaternion) : Set (E → UnitQuaternion) := Set.pi Set.univ fun e => nearRef (r e)

theorem nearSet_measurable (r : E → UnitQuaternion) : MeasurableSet (nearSet r) :=
  MeasurableSet.univ_pi fun e => nearRef_measurable (r e)

/-- **The frame weight.** The fraction of global rotations that bring `x` into the near set. It stands in for a
gauge fixing of the global rotation. -/
def frameWeight (r : E → UnitQuaternion) (x : E → UnitQuaternion) : ℝ :=
  ∫ g, (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF g x) ∂compactHaar UnitQuaternion

theorem frameWeight_measurable (r : E → UnitQuaternion) : Measurable (frameWeight r) := by
  have hc : Measurable fun p : (E → UnitQuaternion) × UnitQuaternion => conjF p.2 p.1 := by
    refine measurable_pi_iff.mpr fun e => ?_
    change Measurable fun p : (E → UnitQuaternion) × UnitQuaternion => p.2 * p.1 e * p.2⁻¹
    have a : Measurable fun p : (E → UnitQuaternion) × UnitQuaternion => p.2 := measurable_snd
    have b : Measurable fun p : (E → UnitQuaternion) × UnitQuaternion => p.1 e :=
      (measurable_pi_apply e).comp measurable_fst
    exact (a.mul b).mul a.inv
  have hi : Measurable ((nearSet r).indicator fun _ : E → UnitQuaternion => (1 : ℝ)) :=
    measurable_const.indicator (nearSet_measurable r)
  have h : Measurable fun p : (E → UnitQuaternion) × UnitQuaternion =>
      (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF p.2 p.1) := hi.comp hc
  have h3 := StronglyMeasurable.integral_prod_right' (ν := compactHaar UnitQuaternion)
    (f := fun p : (E → UnitQuaternion) × UnitQuaternion => (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF p.2 p.1))
    h.stronglyMeasurable
  exact h3.measurable

theorem frameWeight_conj (r : E → UnitQuaternion) (h : UnitQuaternion) (x : E → UnitQuaternion) :
    frameWeight r (conjF h x) = frameWeight r x := by
  unfold frameWeight
  have e : ∀ g, (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF g (conjF h x)) =
      (fun g' => (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF g' x)) (g * h) := fun g => by
    rw [conjF_mul]
  simp only [e]
  exact integral_mul_right_eq_self (μ := compactHaar UnitQuaternion)
    (fun g' => (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF g' x)) h

/-- **Removing the global rotation without a slice.** For a rotation-invariant bounded function, the integral is the
integral over the near set of `F / frameWeight`. Exact. This is the Faddeev-Popov identity for the global rotation,
in a form that needs no coordinates on the orbit. The bound on the weight from below on the support of `F` is a
hypothesis: for `F` supported near the flat field it would follow from `near_flat`, which is not connected here. -/
theorem integral_frame (r : E → UnitQuaternion) (F : (E → UnitQuaternion) → ℝ) (hF : Measurable F)
    (hinv : ∀ g x, F (conjF g x) = F x) (B : ℝ) (hB : ∀ x, |F x| ≤ B) (w₀ : ℝ) (hw₀ : 0 < w₀)
    (hw : ∀ x, F x ≠ 0 → w₀ ≤ frameWeight r x) :
    ∫ x, F x ∂(Measure.pi fun _ : E => compactHaar UnitQuaternion) =
      ∫ x in nearSet r, F x / frameWeight r x ∂(Measure.pi fun _ : E => compactHaar UnitQuaternion) := by
  set A := Measure.pi fun _ : E => compactHaar UnitQuaternion with hA
  set H := compactHaar UnitQuaternion with hH
  set N := nearSet r with hN
  have hNm : MeasurableSet N := nearSet_measurable r
  set Φ : (E → UnitQuaternion) → ℝ := fun x => F x / frameWeight r x with hΦ
  have hΦm : Measurable Φ := hF.div (frameWeight_measurable r)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB fun _ => 1)
  have hΦb (x : E → UnitQuaternion) : ‖Φ x‖ ≤ B / w₀ := by
    rw [Real.norm_eq_abs, hΦ]
    dsimp only
    by_cases hx : F x = 0
    · rw [hx, zero_div, abs_zero]
      positivity
    · have h1 := hw x hx
      rw [abs_div, abs_of_pos (hw₀.trans_le h1)]
      exact div_le_div₀ hB0 (hB x) hw₀ h1
  have hΦinv (g : UnitQuaternion) (x : E → UnitQuaternion) : Φ (conjF g x) = Φ x := by
    simp only [hΦ, hinv, frameWeight_conj]
  -- the integrand on the product
  let I : UnitQuaternion × (E → UnitQuaternion) → ℝ := fun p => N.indicator (fun _ => (1 : ℝ)) (conjF p.1 p.2) * Φ p.2
  have hIm : Measurable I :=
    ((measurable_const.indicator hNm).comp conjF_measurable).mul (hΦm.comp measurable_snd)
  have hIb (p : UnitQuaternion × (E → UnitQuaternion)) : ‖I p‖ ≤ B / w₀ := by
    have h0 : ‖N.indicator (fun _ => (1 : ℝ)) (conjF p.1 p.2)‖ ≤ 1 := by
      by_cases h : conjF p.1 p.2 ∈ N
      · rw [Set.indicator_of_mem h]
        simp
      · rw [Set.indicator_of_notMem h]
        simp
    calc ‖I p‖ = ‖N.indicator (fun _ => (1 : ℝ)) (conjF p.1 p.2)‖ * ‖Φ p.2‖ := norm_mul _ _
      _ ≤ 1 * (B / w₀) := mul_le_mul h0 (hΦb p.2) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hIi : Integrable I (H.prod A) :=
    Integrable.of_bound hIm.aestronglyMeasurable (B / w₀) (Filter.Eventually.of_forall hIb)
  have hswap := integral_integral_swap (f := fun g x => I (g, x)) hIi
  -- the left side, for each rotation
  have hleft (g : UnitQuaternion) : ∫ x, I (g, x) ∂A = ∫ x in N, Φ x ∂A := by
    have e : ∀ x, I (g, x) = (fun y => N.indicator Φ y) (conjF g x) := fun x => by
      change N.indicator (fun _ => (1 : ℝ)) (conjF g x) * Φ x = N.indicator Φ (conjF g x)
      by_cases h : conjF g x ∈ N
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul, hΦinv]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    simp only [e]
    have hind : Measurable (N.indicator Φ) := hΦm.indicator hNm
    have h2 := integral_map (μ := A) (conjF_preserving g).measurable.aemeasurable (f := N.indicator Φ)
      hind.aestronglyMeasurable
    rw [(conjF_preserving g).map_eq, integral_indicator hNm] at h2
    exact h2.symm
  have hright (x : E → UnitQuaternion) : ∫ g, I (g, x) ∂H = F x := by
    have e : ∀ g, I (g, x) = N.indicator (fun _ => (1 : ℝ)) (conjF g x) * Φ x := fun _ => rfl
    simp only [e]
    rw [integral_mul_const]
    change frameWeight r x * Φ x = F x
    by_cases hx : F x = 0
    · simp [hΦ, hx]
    · have h1 := hw₀.trans_le (hw x hx)
      simp only [hΦ]
      field_simp
  simp only [hleft, hright] at hswap
  simp only [integral_const, probReal_univ, one_smul] at hswap
  exact hswap.symm

end Frame

/-! ## The Wilson operator -/

open MeasureTheory WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedVacuum TwistedSliceLift
open TwistedFluxSector TwistedPoincare
open WilsonPositiveGroundState (complexify)
open WilsonSingleLinkStaples (character)
open scoped InnerProductSpace

variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n
local notation "T" => TwistedTransfer.transfer n β

/-! ### Invariances of the potential -/

theorem twistedPotential_continuous : Continuous (twistedPotential n) := by
  have hcd := defect_continuous n
  have hcp : Continuous (potential character 2 : Slice n → ℝ) := by
    have hc := WilsonSingleLinkStaples.character_continuous
    unfold potential spatialHolonomy
    fun_prop
  have hP : twistedPotential n = fun u => potential character 2 u + defect n u :=
    funext (twistedPotential_eq n)
  rw [hP]
  exact hcp.add hcd

theorem twistedPotential_flip (i : Fin 3) (c : ZMod n) (u : Slice n) :
    twistedPotential n (TwistedTransfer.flip n i c u) = twistedPotential n u := by
  rw [twistedPotential_eq, twistedPotential_eq, potential_flip, defect_flip]

theorem twistedPotential_gauge (k : SliceGauge n Q) (u : Slice n) :
    twistedPotential n (gaugeSlice k u) = twistedPotential n u := by
  unfold twistedPotential
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  rw [WilsonSlabGauge.spatialHolonomy_gauge, WilsonSingleLinkStaples.character_classFunction]

theorem wt_gauge (k : SliceGauge n Q) (u : Slice n) : wt n β (gaugeSlice k u) = wt n β u := by
  unfold wt
  rw [twistedPotential_gauge]

/-! ### The two valleys and the off-diagonal kernel -/

/-- The valley with `tr W₃ > 0`: small twisted potential and positive holonomy. -/
def valley (σ : ℝ) : Set (Slice n) := {u | twistedPotential n u < σ ∧ 0 < holo n u}

/-- The mirror valley with `tr W₃ < 0`. -/
def mirror (σ : ℝ) : Set (Slice n) := {u | twistedPotential n u < σ ∧ holo n u < 0}

theorem valley_open (σ : ℝ) : IsOpen (valley n σ) :=
  (isOpen_lt (twistedPotential_continuous n) continuous_const).inter
    (isOpen_lt continuous_const (holo_continuous n))

theorem mirror_open (σ : ℝ) : IsOpen (mirror n σ) :=
  (isOpen_lt (twistedPotential_continuous n) continuous_const).inter
    (isOpen_lt (holo_continuous n) continuous_const)

theorem flip_mem_mirror (σ : ℝ) (u : Slice n) :
    TwistedTransfer.flip n 2 0 u ∈ mirror n σ ↔ u ∈ valley n σ := by
  simp only [mirror, valley, Set.mem_setOf_eq, twistedPotential_flip, holo_flip, neg_lt_zero]

theorem valley_disjoint (σ : ℝ) : Disjoint (valley n σ) (mirror n σ) := by
  rw [Set.disjoint_left]
  rintro u ⟨-, h1⟩ ⟨-, h2⟩
  linarith only [h1, h2]

/-- The error from the region outside the two diagonal valley blocks. -/
def offError (σ : ℝ) : ℝ := Real.exp (-(2 * β / n)) + Real.exp (-(β * σ / 2))

theorem offError_pos (σ : ℝ) : 0 < offError n β σ := by
  unfold offError
  positivity

/-- **Tunneling.** The temporal average decays with the squared difference of the holonomy. -/
theorem avg_le_holo (hβ : 0 ≤ β) (u v : Slice n) :
    avg n β u v ≤ Real.exp (-(β * (holo n u - holo n v) ^ 2 / n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hpt (k : SliceGauge n Q) : Real.exp (-β * temporalAction character 2 u v k) ≤
      Real.exp (-(β * (holo n u - holo n v) ^ 2 / n)) := by
    apply Real.exp_le_exp.mpr
    have h1 := holo_lipschitz n u (gaugeSlice k v)
    rw [holo_gauge, ← temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction] at h1
    have h2 : (holo n u - holo n v) ^ 2 / n ≤ temporalAction character 2 u v k := by
      rw [div_le_iff₀ hnpos]
      linarith only [h1]
    have h3 := mul_le_mul_of_nonneg_left h2 hβ
    have e : β * (holo n u - holo n v) ^ 2 / n = β * ((holo n u - holo n v) ^ 2 / n) := by ring
    rw [e]
    linarith only [h3]
  have hm := integral_mono (avg_integrable n β hβ u v) (integrable_const _) hpt
  simpa [avg] using hm

theorem kernel_le_wt (hβ : 0 ≤ β) (u v : Slice n) : twistedKernel n β (u, v) ≤ wt n β u * wt n β v := by
  rw [kernel_factor]
  have h1 := avg_le_one n β hβ u v
  have h2 := avg_nonneg n β hβ u v
  have h3 := wt_pos n β u
  have h4 := wt_pos n β v
  have : wt n β u * avg n β u v * wt n β v ≤ wt n β u * 1 * wt n β v := by gcongr
  linarith only [this]

theorem wt_le_of_ge (hβ : 0 ≤ β) (σ : ℝ) (u : Slice n) (h : σ ≤ twistedPotential n u) :
    wt n β u ≤ Real.exp (-(β * σ / 2)) := by
  unfold wt
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left h hβ]

/-- **The kernel is exponentially small off the two diagonal valley blocks.** For `σ ≤ 1/(16 n⁴)`, either
one of the two fields has potential at least `σ`, or the fields lie in opposite valleys. -/
theorem kernel_off (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (u v : Slice n)
    (h₁ : ¬ (u ∈ valley n σ ∧ v ∈ valley n σ)) (h₂ : ¬ (u ∈ mirror n σ ∧ v ∈ mirror n σ)) :
    twistedKernel n β (u, v) ≤ offError n β σ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have e₁ := Real.exp_pos (-(2 * β / n))
  have e₂ := Real.exp_pos (-(β * σ / 2))
  have hu1 := wt_le_one n β hβ u
  have hv1 := wt_le_one n β hβ v
  have hu0 := wt_pos n β u
  have hv0 := wt_pos n β v
  have hkw := kernel_le_wt n β hβ u v
  unfold offError
  by_cases hU : σ ≤ twistedPotential n u
  · have := wt_le_of_ge n β hβ σ u hU
    nlinarith only [this, hkw, hv1, hu0, e₁]
  by_cases hV : σ ≤ twistedPotential n v
  · have := wt_le_of_ge n β hβ σ v hV
    nlinarith only [this, hkw, hu1, hv0, e₁]
  push_neg at hU hV
  have hsu := holo_sq_of_small n u (hU.trans_le hσ)
  have hsv := holo_sq_of_small n v (hV.trans_le hσ)
  -- The fields lie in opposite valleys, so the holonomy jumps by at least `√2`.
  have hjump : 2 ≤ (holo n u - holo n v) ^ 2 := by
    set a := holo n u
    set b := holo n v
    have hsign : a * b < 0 := by
      have ha : a ≠ 0 := fun h => by rw [h] at hsu; norm_num at hsu
      have hb : b ≠ 0 := fun h => by rw [h] at hsv; norm_num at hsv
      rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
      · exact absurd ⟨⟨hU, ha'⟩, ⟨hV, hb'⟩⟩ h₂
      · exact mul_neg_of_neg_of_pos ha' hb'
      · exact mul_neg_of_pos_of_neg ha' hb'
      · exact absurd ⟨⟨hU, ha'⟩, ⟨hV, hb'⟩⟩ h₁
    have hprod : 1 / 2 ≤ -(a * b) := by
      by_contra hc
      push_neg at hc
      have h0 : 0 < -(a * b) := by linarith only [hsign]
      have h1 : (a * b) ^ 2 < 1 / 4 := by nlinarith only [h0, hc]
      have h2 : 1 / 4 ≤ a ^ 2 * b ^ 2 := by nlinarith only [hsu, hsv]
      have h3 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
      linarith only [h1, h2, h3]
    nlinarith only [hprod, hsu, hsv]
  have havg := avg_le_holo n β hβ u v
  have hexp : avg n β u v ≤ Real.exp (-(2 * β / n)) := by
    refine havg.trans (Real.exp_le_exp.mpr ?_)
    have h1 : 2 * β / n ≤ β * (holo n u - holo n v) ^ 2 / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      nlinarith only [mul_le_mul_of_nonneg_left hjump hβ]
    linarith only [h1]
  rw [kernel_factor]
  have h0 := avg_nonneg n β hβ u v
  have : wt n β u * avg n β u v * wt n β v ≤ 1 * avg n β u v * 1 := by gcongr
  linarith only [this, hexp, e₂]

/-! ### The quadratic form splits along the valleys -/

/-- The integrand of the transfer form on the product space. -/
def pairFn (h : C(Slice n, ℝ)) (p : Slice n × Slice n) : ℝ := h p.1 * twistedKernel n β p * h p.2

theorem pairFn_continuous (h : C(Slice n, ℝ)) : Continuous (pairFn n β h) :=
  ((h.continuous.comp continuous_fst).mul (twistedKernel n β).continuous).mul
    (h.continuous.comp continuous_snd)

theorem pairFn_integrable (h : C(Slice n, ℝ)) : Integrable (pairFn n β h) ((μ').prod (μ')) :=
  (pairFn_continuous n β h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem form_eq_prod (h : C(Slice n, ℝ)) :
    ∫ u, h u * (∫ v, twistedKernel n β (u, v) * h v ∂μ') ∂μ' =
      ∫ p, pairFn n β h p ∂((μ').prod (μ')) := by
  rw [integral_prod _ (pairFn_integrable n β h)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [pairFn]
  ring

/-- The transfer form compressed to one valley. -/
def valleyForm (σ : ℝ) (h : C(Slice n, ℝ)) : ℝ :=
  ∫ u in valley n σ, ∫ v in valley n σ, h u * twistedKernel n β (u, v) * h v ∂μ' ∂μ'

theorem abs_mean_sq_le (h : C(Slice n, ℝ)) : (∫ v, |h v| ∂μ') ^ 2 ≤ ∫ v, h v ^ 2 ∂μ' := by
  set a := ∫ v, |h v| ∂μ' with ha
  have h0 : 0 ≤ ∫ v, (|h v| - a) ^ 2 ∂μ' := integral_nonneg fun v => sq_nonneg _
  have e : ∀ v, (|h v| - a) ^ 2 = 1 * h v ^ 2 - (2 * a) * |h v| + a ^ 2 := fun v => by
    have := sq_abs (h v)
    nlinarith only [this]
  simp only [e] at h0
  rw [integral_three n (fun v => h v ^ 2) (fun v => |h v|) (fun _ => a ^ 2) (h.continuous.pow 2)
    h.continuous.abs continuous_const] at h0
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
  rw [← ha] at h0
  nlinarith only [h0]

/-- **The transfer form of a `W₃`-flip-even function is twice its valley form, up to `offError`.** This
is where neutrality enters: an even function has the same form on both valleys, and the two valleys
barely interact. -/
theorem form_split (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (h : C(Slice n, ℝ))
    (hflip : ∀ u, h (TwistedTransfer.flip n 2 0 u) = h u) :
    ∫ u, h u * (∫ v, twistedKernel n β (u, v) * h v ∂μ') ∂μ' ≤
      2 * valleyForm n β σ h + offError n β σ * ∫ v, h v ^ 2 ∂μ' := by
  set G := pairFn n β h with hG
  have hGi := pairFn_integrable n β h
  have hGc := pairFn_continuous n β h
  set S : Set (Slice n × Slice n) := valley n σ ×ˢ valley n σ with hS
  set S' : Set (Slice n × Slice n) := mirror n σ ×ˢ mirror n σ with hS'
  have hSm : MeasurableSet S := (valley_open n σ).measurableSet.prod (valley_open n σ).measurableSet
  have hSm' : MeasurableSet S' := (mirror_open n σ).measurableSet.prod (mirror_open n σ).measurableSet
  have hdisj : Disjoint S S' := by
    rw [Set.disjoint_left]
    rintro p ⟨h1, -⟩ ⟨h2, -⟩
    exact Set.disjoint_left.mp (valley_disjoint n σ) h1 h2
  rw [form_eq_prod]
  have hU := setIntegral_union (μ := (μ').prod (μ')) hdisj hSm' hGi.integrableOn hGi.integrableOn
  have hsplit := integral_add_compl (hSm.union hSm') hGi
  rw [hU] at hsplit
  -- the two diagonal blocks agree
  have hmirror : ∫ p in S', G p ∂((μ').prod (μ')) = ∫ p in S, G p ∂((μ').prod (μ')) := by
    let Φ : Slice n × Slice n ≃ᵐ Slice n × Slice n := (flipEquiv n 2 0).prodCongr (flipEquiv n 2 0)
    have hmp : MeasurePreserving (flipEquiv n 2 0) (μ') (μ') := flip_measurePreserving n 2 0
    have hΦ : MeasurePreserving Φ ((μ').prod (μ')) ((μ').prod (μ')) := hmp.prod hmp
    have := hΦ.setIntegral_preimage_emb Φ.measurableEmbedding G S'
    rw [← this]
    have hpre : Φ ⁻¹' S' = S := by
      ext p
      change (TwistedTransfer.flip n 2 0 p.1 ∈ mirror n σ ∧ TwistedTransfer.flip n 2 0 p.2 ∈ mirror n σ) ↔ _
      rw [flip_mem_mirror, flip_mem_mirror]
      rfl
    rw [hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change h (TwistedTransfer.flip n 2 0 p.1) *
      twistedKernel n β (TwistedTransfer.flip n 2 0 p.1, TwistedTransfer.flip n 2 0 p.2) *
      h (TwistedTransfer.flip n 2 0 p.2) = h p.1 * twistedKernel n β p * h p.2
    rw [hflip, hflip, twistedKernel_flip]
  -- the remainder
  have hprodabs : Integrable (fun p : Slice n × Slice n => offError n β σ * (|h p.1| * |h p.2|))
      ((μ').prod (μ')) :=
    (continuous_const.mul ((h.continuous.comp continuous_fst).abs.mul
      (h.continuous.comp continuous_snd).abs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hrem : ∫ p in (S ∪ S')ᶜ, G p ∂((μ').prod (μ')) ≤ offError n β σ * ∫ v, h v ^ 2 ∂μ' := by
    have h1 : ∫ p in (S ∪ S')ᶜ, G p ∂((μ').prod (μ')) ≤
        ∫ p in (S ∪ S')ᶜ, offError n β σ * (|h p.1| * |h p.2|) ∂((μ').prod (μ')) := by
      refine setIntegral_mono_on hGi.integrableOn hprodabs.integrableOn (hSm.union hSm').compl ?_
      rintro ⟨u, v⟩ hp
      have hp1 : ¬ (u ∈ valley n σ ∧ v ∈ valley n σ) := fun hc => hp (Or.inl hc)
      have hp2 : ¬ (u ∈ mirror n σ ∧ v ∈ mirror n σ) := fun hc => hp (Or.inr hc)
      have hk := kernel_off n β hβ σ hσ u v hp1 hp2
      have hk0 := (twistedKernel_pos n β (u, v)).le
      change h u * twistedKernel n β (u, v) * h v ≤ offError n β σ * (|h u| * |h v|)
      have hab : h u * twistedKernel n β (u, v) * h v ≤ twistedKernel n β (u, v) * (|h u| * |h v|) := by
        have e : h u * twistedKernel n β (u, v) * h v = twistedKernel n β (u, v) * (h u * h v) := by ring
        rw [e, ← abs_mul]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) hk0
      have hnn : 0 ≤ |h u| * |h v| := by positivity
      exact hab.trans (mul_le_mul_of_nonneg_right hk hnn)
    have h2 : ∫ p in (S ∪ S')ᶜ, offError n β σ * (|h p.1| * |h p.2|) ∂((μ').prod (μ')) ≤
        ∫ p, offError n β σ * (|h p.1| * |h p.2|) ∂((μ').prod (μ')) := by
      refine setIntegral_le_integral hprodabs (Filter.Eventually.of_forall fun p => ?_)
      have := (offError_pos n β σ).le
      change (0 : ℝ) ≤ offError n β σ * (|h p.1| * |h p.2|)
      positivity
    have h3 : ∫ p, offError n β σ * (|h p.1| * |h p.2|) ∂((μ').prod (μ')) =
        offError n β σ * (∫ v, |h v| ∂μ') ^ 2 := by
      rw [integral_const_mul, integral_prod_mul (fun v => |h v|) (fun v => |h v|), sq]
    have h4 := abs_mean_sq_le n h
    have h5 := mul_le_mul_of_nonneg_left h4 (offError_pos n β σ).le
    linarith only [h1, h2, h3, h5]
  have hval : ∫ p in S, G p ∂((μ').prod (μ')) = valleyForm n β σ h := by
    rw [hS, setIntegral_prod _ hGi.integrableOn]
    rfl
  rw [hmirror] at hsplit
  linarith only [hsplit, hrem, hval]

/-- An even function has at most half its square on the valley. -/
theorem valley_sq_le (σ : ℝ) (h : C(Slice n, ℝ)) (hflip : ∀ u, h (TwistedTransfer.flip n 2 0 u) = h u) :
    2 * ∫ u in valley n σ, h u ^ 2 ∂μ' ≤ ∫ u, h u ^ 2 ∂μ' := by
  have hi : Integrable (fun u => h u ^ 2) μ' := ci n (h.continuous.pow 2)
  have hmirror : ∫ u in mirror n σ, h u ^ 2 ∂μ' = ∫ u in valley n σ, h u ^ 2 ∂μ' := by
    have hmp : MeasurePreserving (flipEquiv n 2 0) (μ') (μ') := flip_measurePreserving n 2 0
    have := hmp.setIntegral_preimage_emb (flipEquiv n 2 0).measurableEmbedding
      (fun u => h u ^ 2) (mirror n σ)
    rw [← this]
    have hpre : (flipEquiv n 2 0) ⁻¹' mirror n σ = valley n σ := by
      ext u
      exact flip_mem_mirror n σ u
    rw [hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change h (TwistedTransfer.flip n 2 0 u) ^ 2 = h u ^ 2
    rw [hflip]
  have hU := setIntegral_union (μ := μ') (f := fun u => h u ^ 2) (valley_disjoint n σ)
    (mirror_open n σ).measurableSet hi.integrableOn hi.integrableOn
  have hle : ∫ u in valley n σ ∪ mirror n σ, h u ^ 2 ∂μ' ≤ ∫ u, h u ^ 2 ∂μ' :=
    setIntegral_le_integral hi (Filter.Eventually.of_forall fun u => sq_nonneg _)
  rw [hU, hmirror] at hle
  linarith only [hle]

/-! ### Reduction of the neutral gap to one valley -/

/-- Invariant under every slice gauge transformation and every center flip. These are the only
observables the neutral sector sees. -/
structure Invariant (h : C(Slice n, ℝ)) : Prop where
  gauge : ∀ (k : SliceGauge n Q) u, h (gaugeSlice k u) = h u
  flip : ∀ i c u, h (TwistedTransfer.flip n i c u) = h u

/-- On invariant observables, the transfer form compressed to the valley is at most `ρ` once a single linear
constraint given by `ψ` is imposed. This is about the valley alone, and `ψ` is free. At fixed `n` it holds with `ρ`
below `‖T‖` (`valleyGap_explicit`). **Open:** `ρ` of size `exp(-c/n) ‖T‖`, uniformly in `n`. -/
def ValleyGap (σ ρ : ℝ) (ψ : C(Slice n, ℝ)) : Prop :=
  ∀ h, Invariant n h → ∫ u in valley n σ, h u * ψ u ∂μ' = 0 →
    valleyForm n β σ h ≤ ρ * ∫ u in valley n σ, h u ^ 2 ∂μ'

/-- The positive ground state is invariant. -/
theorem eta_invariant (hβ : 0 ≤ β) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) : Invariant n η := by
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  refine ⟨fun k u => ?_, top_flip n β η hη heig hlam⟩
  have h1 := heig (gaugeSlice k u)
  have h2 := heig u
  simp only [TwistedTreeGauge.twistedKernel_gauge_left] at h1
  rw [h2] at h1
  exact (mul_left_cancel₀ hlam.ne' h1).symm

theorem sq_integral_pos (φ : C(Slice n, ℝ)) (hne : ∃ u, φ u ≠ 0) : 0 < ∫ u, φ u ^ 2 ∂μ' := by
  obtain ⟨u₀, hu₀⟩ := hne
  haveI hmeas : Measure.IsOpenPosMeasure (μ') := by
    change (Measure.pi fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q).IsOpenPosMeasure
    haveI : (RegulatedGauge.compactHaar Q).IsOpenPosMeasure := GibbsFullSupport.compactHaar_openPos Q
    infer_instance
  exact (φ.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun u => sq_nonneg _) (pow_ne_zero 2 hu₀)

/-- **The two-dimensional eigenspace argument.** A real invariant eigenfunction orthogonal to the
ground state has eigenvalue at most `ρ + offError`. A combination of it with `η` meets the constraint of
`ValleyGap`, and on that combination the transfer form is at least the eigenvalue times the norm. -/
theorem eigen_le_of_valley (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ψ : C(Slice n, ℝ)) (H : ValleyGap n β σ ρ ψ) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u)
    (φ : C(Slice n, ℝ)) (hφ : Invariant n φ) (hne : ∃ u, φ u ≠ 0) (horth : ∫ u, η u * φ u ∂μ' = 0)
    (lam' : ℝ) (hlam' : lam' ≤ ‖T‖)
    (hφeig : ∀ u, (∫ v, twistedKernel n β (u, v) * φ v ∂μ') = lam' * φ u) :
    lam' ≤ ρ + offError n β σ := by
  have hηinv := eta_invariant n β hβ η hη heig
  set A := ∫ u, η u ^ 2 ∂μ' with hA
  set B := ∫ u, φ u ^ 2 ∂μ' with hB
  have hApos : 0 < A := sq_integral_pos n η ⟨fun _ => 1, (hη _).ne'⟩
  have hBpos : 0 < B := sq_integral_pos n φ hne
  -- choose the combination meeting the constraint
  have hiη : IntegrableOn (fun u => η u * ψ u) (valley n σ) μ' :=
    (ci n (η.continuous.mul ψ.continuous)).integrableOn
  have hiφ : IntegrableOn (fun u => φ u * ψ u) (valley n σ) μ' :=
    (ci n (φ.continuous.mul ψ.continuous)).integrableOn
  set α := ∫ u in valley n σ, η u * ψ u ∂μ' with hα
  set γ := ∫ u in valley n σ, φ u * ψ u ∂μ' with hγ
  obtain ⟨a, b, hab, hcon⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a * α + b * γ = 0 := by
    by_cases hz : α = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hz]; ring⟩
    · exact ⟨γ, -α, Or.inr (neg_ne_zero.mpr hz), by ring⟩
  let h : C(Slice n, ℝ) := a • η + b • φ
  have hv (u : Slice n) : h u = a * η u + b * φ u := rfl
  have hinv : Invariant n h :=
    { gauge := fun k u => by rw [hv, hv, hηinv.gauge, hφ.gauge]
      flip := fun i c u => by rw [hv, hv, hηinv.flip, hφ.flip] }
  have hc : ∫ u in valley n σ, h u * ψ u ∂μ' = 0 := by
    have e : ∀ u, h u * ψ u = a * (η u * ψ u) + b * (φ u * ψ u) := fun u => by rw [hv]; ring
    simp only [e]
    rw [integral_add (hiη.const_mul a) (hiφ.const_mul b), integral_const_mul, integral_const_mul]
    exact hcon
  have hvg := H h hinv hc
  have hup := form_split n β hβ σ hσ h (hinv.flip 2 0)
  have hsq := valley_sq_le n σ h (hinv.flip 2 0)
  -- the form and the norm of the combination
  set lam := ‖T‖ with hlamd
  have hinner (u : Slice n) : (∫ v, twistedKernel n β (u, v) * h v ∂μ') =
      a * (lam * η u) + b * (lam' * φ u) := by
    have hK : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    have e : ∀ v, twistedKernel n β (u, v) * h v =
        a * (twistedKernel n β (u, v) * η v) + b * (twistedKernel n β (u, v) * φ v) := fun v => by
      rw [hv]
      ring
    simp only [e]
    have i1 : Integrable (fun v => a * (twistedKernel n β (u, v) * η v)) μ' :=
      (ci n (hK.mul η.continuous)).const_mul a
    have i2 : Integrable (fun v => b * (twistedKernel n β (u, v) * φ v)) μ' :=
      (ci n (hK.mul φ.continuous)).const_mul b
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul, heig, hφeig]
  have hηφ : Continuous fun u => η u * φ u := η.continuous.mul φ.continuous
  have hform : ∫ u, h u * (∫ v, twistedKernel n β (u, v) * h v ∂μ') ∂μ' =
      a ^ 2 * lam * A + b ^ 2 * lam' * B := by
    simp only [hinner]
    have e : ∀ u, h u * (a * (lam * η u) + b * (lam' * φ u)) =
        (a ^ 2 * lam) * η u ^ 2 - (-(a * b * (lam + lam'))) * (η u * φ u) +
          (b ^ 2 * lam') * φ u ^ 2 := fun u => by
      rw [hv]
      ring
    simp only [e]
    rw [integral_three n (fun u => η u ^ 2) (fun u => η u * φ u) (fun u => (b ^ 2 * lam') * φ u ^ 2)
      (η.continuous.pow 2) hηφ (continuous_const.mul (φ.continuous.pow 2)), horth, integral_const_mul]
    ring
  have hnorm : ∫ u, h u ^ 2 ∂μ' = a ^ 2 * A + b ^ 2 * B := by
    have e : ∀ u, h u ^ 2 =
        a ^ 2 * η u ^ 2 - (-(2 * a * b)) * (η u * φ u) + (b ^ 2) * φ u ^ 2 := fun u => by
      rw [hv]
      ring
    simp only [e]
    rw [integral_three n (fun u => η u ^ 2) (fun u => η u * φ u) (fun u => (b ^ 2) * φ u ^ 2)
      (η.continuous.pow 2) hηφ (continuous_const.mul (φ.continuous.pow 2)), horth, integral_const_mul]
    ring
  set X := a ^ 2 * A + b ^ 2 * B with hX
  have hXpos : 0 < X := by
    rcases hab with ha | hb
    · have := sq_pos_of_ne_zero ha
      positivity
    · have := sq_pos_of_ne_zero hb
      positivity
  rw [hform, hnorm] at hup
  rw [hnorm] at hsq
  have hlow : lam' * X ≤ a ^ 2 * lam * A + b ^ 2 * lam' * B := by
    have h1 : 0 ≤ a ^ 2 * A := by positivity
    have h2 := mul_le_mul_of_nonneg_right hlam' h1
    rw [hX]
    nlinarith only [h2]
  have hval : valleyForm n β σ h ≤ ρ * (X / 2) :=
    hvg.trans (mul_le_mul_of_nonneg_left (by linarith only [hsq]) hρ)
  have hfin : lam' * X ≤ (ρ + offError n β σ) * X := by
    nlinarith only [hlow, hup, hval]
  exact le_of_mul_le_mul_right hfin hXpos

/-- The neutral eigenvector reduction: to bound `T` on the neutral complement it suffices to bound the
eigenvalue of every real invariant eigenfunction orthogonal to the ground state. Eigenfunctions with
positive eigenvalue are automatically gauge invariant, and flip invariant when the vector is neutral. -/
theorem contraction_of_real_eigen (hβ : 0 ≤ β) (η : C(Slice n, ℝ))
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ φ : C(Slice n, ℝ), Invariant n φ → (∃ u, φ u ≠ 0) → ∫ u, η u * φ u ∂μ' = 0 →
      ∀ lam' : ℝ, 0 < lam' → lam' ≤ ‖T‖ →
        (∀ u, (∫ v, twistedKernel n β (u, v) * φ v ∂μ') = lam' * φ u) → lam' ≤ B) :
    ∀ f, Neutral n f → inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 → ‖T f‖ ≤ B * ‖f‖ := by
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  set Ω := ContinuousMap.toLp 2 (μ') ℂ (complexify η) with hΩ
  have hTΩ : T Ω = ‖T‖ • Ω := by
    rw [hΩ, transfer_embed]
    have hs : sm n β η = ‖T‖ • η := by
      ext u
      rw [sm_apply, heig]
      rfl
    rw [hs, WilsonPositiveGroundState.complexify_smul, map_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y) := (transfer_positive n β hβ).isSymmetric
  set M := neutralComplement n Ω with hM
  have hTM : ∀ f : Hilbert n, f ∈ M → T f ∈ M := by
    rintro f ⟨hf, hf'⟩
    refine ⟨fun i c => ?_, ?_⟩
    · rw [← transfer_flipOp, hf i c]
    · rw [← hsym, hTΩ, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hf', mul_zero]
  have hmain : ∀ f ∈ M, ‖T f‖ ≤ B * ‖f‖ := by
    refine invariant_bound _ (transfer_positive n β hβ) (TwistedTransfer.transfer_compact n β) M
      (neutralComplement_closed n Ω) hTM _ hB ?_
    rintro w ⟨hneut, horth⟩ hwne lam' hlam' hTw
    have hle : lam' ≤ ‖T‖ := by
      have h1 := (T).le_opNorm w
      rw [hTw, norm_smul, Real.norm_eq_abs, abs_of_pos hlam'] at h1
      exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hwne)
    obtain ⟨f, hfw, hfeig⟩ := continuous_eigenfunction n β lam' hlam'.ne' w hTw
    have hμC : ((lam' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam'.ne'
    have hfgauge (h : SliceGauge n Q) (u : Slice n) : f (gaugeSlice h u) = f u := by
      have h1 := hfeig (gaugeSlice h u)
      have h2 := hfeig u
      simp only [TwistedTreeGauge.twistedKernel_gauge_left] at h1
      rw [h2] at h1
      exact (mul_left_cancel₀ hμC h1).symm
    have hflipae (i : Fin 3) (c : ZMod n) : (f ∘ TwistedTransfer.flip n i c) =ᵐ[μ'] f := by
      have h1 : (flipOp n i c w : Slice n → ℂ) =ᵐ[μ'] ((w : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
        Lp.coeFn_compMeasurePreserving _ (flip_measurePreserving n i c)
      have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') f
      rw [hfw] at h2
      have h3 := (flip_measurePreserving n i c).quasiMeasurePreserving.ae_eq_comp h2
      rw [hneut i c] at h1
      exact h3.symm.trans (h1.symm.trans h2)
    have hfflip (i : Fin 3) (c : ZMod n) (u : Slice n) : f (TwistedTransfer.flip n i c u) = f u := by
      have hmp' : MeasurePreserving (flipEquiv n i c) (μ') (μ') := flip_measurePreserving n i c
      have h1 := hfeig (TwistedTransfer.flip n i c u)
      have h2 := hmp'.integral_comp'
        (fun v => (twistedKernel n β (TwistedTransfer.flip n i c u, v) : ℂ) * f v)
      have h3 : (∫ v, (twistedKernel n β (TwistedTransfer.flip n i c u, v) : ℂ) * f v ∂μ') =
          ∫ v, (twistedKernel n β (u, v) : ℂ) * f v ∂μ' := by
        rw [← h2]
        refine integral_congr_ae ((hflipae i c).mono fun v hv => ?_)
        change (twistedKernel n β (TwistedTransfer.flip n i c u, TwistedTransfer.flip n i c v) : ℂ) *
          f (TwistedTransfer.flip n i c v) = _
        rw [twistedKernel_flip]
        have : f (TwistedTransfer.flip n i c v) = f v := hv
        rw [this]
      rw [h3, hfeig u] at h1
      exact (mul_left_cancel₀ hμC h1).symm
    have hmeanC : ∫ u, (η u : ℂ) * f u ∂μ' = 0 := by
      have h := horth
      rw [hΩ, ← hfw, MeasureTheory.ContinuousMap.inner_toLp] at h
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [complexify, mul_comm]
    have hfnz : ∃ u, f u ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hwne
      rw [← hfw]
      have : f = 0 := by
        ext u
        simp [hall u]
      rw [this, map_zero]
    obtain ⟨u₀, hu₀⟩ := hfnz
    have hcf (u : Slice n) : Integrable (fun v => (twistedKernel n β (u, v) : ℂ) * f v) μ' :=
      (Continuous.mul (Complex.continuous_ofReal.comp ((twistedKernel n β).continuous.comp
        (continuous_const.prodMk continuous_id))) f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hcη : Integrable (fun v => (η v : ℂ) * f v) μ' :=
      (Continuous.mul (Complex.continuous_ofReal.comp η.continuous)
        f.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmk (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ∀ (r : ℝ) (z : ℂ), ℓ ((r : ℂ) * z) = r * ℓ z)
        (hne : ℓ (f u₀) ≠ 0) : lam' ≤ B := by
      let φ : C(Slice n, ℝ) := ⟨fun u => ℓ (f u), ℓ.continuous.comp f.continuous⟩
      have hφv (u : Slice n) : φ u = ℓ (f u) := rfl
      have hφeig (u : Slice n) : (∫ v, twistedKernel n β (u, v) * φ v ∂μ') = lam' * φ u := by
        have h1 := congrArg ℓ (hfeig u)
        rw [hℓ, ← ContinuousLinearMap.integral_comp_comm ℓ (hcf u)] at h1
        rw [hφv, ← h1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hφv, hℓ]
      have hφmean : ∫ u, η u * φ u ∂μ' = 0 := by
        have h1 := congrArg ℓ hmeanC
        rw [map_zero, ← ContinuousLinearMap.integral_comp_comm ℓ hcη] at h1
        rw [← h1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hφv, hℓ]
      have hinv : Invariant n φ :=
        { gauge := fun k u => by rw [hφv, hφv, hfgauge]
          flip := fun i c u => by rw [hφv, hφv, hfflip] }
      exact hbound φ hinv ⟨u₀, hne⟩ hφmean lam' hlam' hle hφeig
    by_cases hre : (f u₀).re ≠ 0
    · exact hmk Complex.reCLM (fun r z => by simp) hre
    · have him : (f u₀).im ≠ 0 := by
        intro h
        apply hu₀
        push_neg at hre
        exact Complex.ext hre h
      exact hmk Complex.imCLM (fun r z => by simp) him
  exact fun f hf hf' => hmain f ⟨hf, hf'⟩

/-- **The neutral gap reduces to one valley.** If `ValleyGap` holds at level `ρ`, then `T` contracts the
neutral complement of its vacuum by `ρ + offError`. All far-field and tunneling contributions are accounted for by
`offError`, with no hypothesis on them. The converse is `valleyGap_of_contraction`. -/
theorem neutral_contraction_of_valley (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (ψ : C(Slice n, ℝ)) (H : ValleyGap n β σ ρ ψ) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) :
    ∀ f, Neutral n f → inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 →
      ‖T f‖ ≤ (ρ + offError n β σ) * ‖f‖ :=
  contraction_of_real_eigen n β hβ η heig _ (add_nonneg hρ (offError_pos n β σ).le)
    fun φ hφ hne horth lam' _ hle hφeig =>
      eigen_le_of_valley n β hβ σ hσ ρ hρ ψ H η hη heig φ hφ hne horth lam' hle hφeig

/-! ### Replacing the unknown ground state by an explicit trial function -/

section Trial

variable {n β}

theorem integral_sub_add' (ν : Measure (Slice n)) {a b c : Slice n → ℝ} (ha : Integrable a ν)
    (hb : Integrable b ν) (hc : Integrable c ν) :
    ∫ v, (a v - b v + c v) ∂ν = ∫ v, a v ∂ν - ∫ v, b v ∂ν + ∫ v, c v ∂ν := by
  have hab : Integrable (fun v => a v - b v) ν := ha.sub hb
  rw [integral_add hab hc, integral_sub ha hb]

/-- Smoothing by the kernel against a finite measure. -/
def smoothOn (ν : Measure (Slice n)) [IsFiniteMeasure ν] (a : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  ⟨fun u => ∫ v, twistedKernel n β (u, v) * a v ∂ν, by
    have hf : Continuous (Function.uncurry fun (u v : Slice n) => twistedKernel n β (u, v) * a v) :=
      (twistedKernel n β).continuous.mul (a.continuous.comp continuous_snd)
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := ν) hf isCompact_univ)⟩

/-- The kernel pairing on a finite measure is symmetric in the two test functions. -/
theorem pairing_swap (ν : Measure (Slice n)) [IsFiniteMeasure ν] (a b : C(Slice n, ℝ)) :
    ∫ u, a u * (∫ v, twistedKernel n β (u, v) * b v ∂ν) ∂ν =
      ∫ u, b u * (∫ v, twistedKernel n β (u, v) * a v ∂ν) ∂ν := by
  have hc : Continuous fun p : Slice n × Slice n => a p.1 * (twistedKernel n β p * b p.2) :=
    (a.continuous.comp continuous_fst).mul
      ((twistedKernel n β).continuous.mul (b.continuous.comp continuous_snd))
  have hi : Integrable (fun p : Slice n × Slice n => a p.1 * (twistedKernel n β p * b p.2)) (ν.prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ u, a u * (∫ v, twistedKernel n β (u, v) * b v ∂ν) ∂ν
      = ∫ u, ∫ v, a u * (twistedKernel n β (u, v) * b v) ∂ν ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ v, ∫ u, a u * (twistedKernel n β (u, v) * b v) ∂ν ∂ν :=
        integral_integral_swap (f := fun u v => a u * (twistedKernel n β (u, v) * b v)) hi
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        have : ∀ u, a u * (twistedKernel n β (u, v) * b v) =
            b v * (twistedKernel n β (v, u) * a u) := fun u => by
          rw [twistedKernel_symm]
          ring
        simp only [this]
        exact integral_const_mul _ _

/-- **The ground-state identity with a trial function, on a finite measure.** Unlike
`ground_state_identity`, `ψ` is arbitrary: the identity holds with the local eigenvalue `Tψ/ψ`, not a
constant, and the unknown ground state does not appear. -/
theorem trial_identity (ν : Measure (Slice n)) [IsFiniteMeasure ν] (ψ g : C(Slice n, ℝ)) :
    ∫ u, ∫ v, ψ u * twistedKernel n β (u, v) * ψ v * (g u - g v) ^ 2 ∂ν ∂ν =
      2 * (∫ u, g u ^ 2 * ψ u * (∫ v, twistedKernel n β (u, v) * ψ v ∂ν) ∂ν) -
        2 * ∫ u, ∫ v, (g u * ψ u) * twistedKernel n β (u, v) * (g v * ψ v) ∂ν ∂ν := by
  let f₁ : C(Slice n, ℝ) := g * ψ
  let f₂ : C(Slice n, ℝ) := g * g * ψ
  have hf₁ (u : Slice n) : f₁ u = g u * ψ u := rfl
  have hf₂ (u : Slice n) : f₂ u = g u * g u * ψ u := rfl
  have hcv {F : Slice n → ℝ} (hF : Continuous F) : Integrable F ν :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let sψ : C(Slice n, ℝ) := smoothOn (β := β) ν ψ
  let s₁ : C(Slice n, ℝ) := smoothOn (β := β) ν f₁
  let s₂ : C(Slice n, ℝ) := smoothOn (β := β) ν f₂
  have hsψ (u : Slice n) : sψ u = ∫ v, twistedKernel n β (u, v) * ψ v ∂ν := rfl
  have hs₁ (u : Slice n) : s₁ u = ∫ v, twistedKernel n β (u, v) * f₁ v ∂ν := rfl
  have hs₂ (u : Slice n) : s₂ u = ∫ v, twistedKernel n β (u, v) * f₂ v ∂ν := rfl
  have hin (u : Slice n) :
      (∫ v, ψ u * twistedKernel n β (u, v) * ψ v * (g u - g v) ^ 2 ∂ν) =
        g u ^ 2 * ψ u * sψ u - 2 * (f₁ u * s₁ u) + ψ u * s₂ u := by
    have hK : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    have e : ∀ v, ψ u * twistedKernel n β (u, v) * ψ v * (g u - g v) ^ 2 =
        (g u ^ 2 * ψ u) * (twistedKernel n β (u, v) * ψ v) -
          (2 * f₁ u) * (twistedKernel n β (u, v) * f₁ v) +
            ψ u * (twistedKernel n β (u, v) * f₂ v) := fun v => by
      rw [hf₁, hf₁, hf₂]
      ring
    simp only [e]
    have i1 : Integrable (fun v => (g u ^ 2 * ψ u) * (twistedKernel n β (u, v) * ψ v)) ν :=
      hcv (continuous_const.mul (hK.mul ψ.continuous))
    have i2 : Integrable (fun v => (2 * f₁ u) * (twistedKernel n β (u, v) * f₁ v)) ν :=
      hcv (continuous_const.mul (hK.mul f₁.continuous))
    have i3 : Integrable (fun v => ψ u * (twistedKernel n β (u, v) * f₂ v)) ν :=
      hcv (continuous_const.mul (hK.mul f₂.continuous))
    rw [integral_sub_add' ν i1 i2 i3, integral_const_mul, integral_const_mul,
      integral_const_mul, hsψ, hs₁, hs₂]
    ring
  simp only [hin]
  have i1 : Integrable (fun u => g u ^ 2 * ψ u * sψ u) ν :=
    hcv (((g.continuous.pow 2).mul ψ.continuous).mul sψ.continuous)
  have i2 : Integrable (fun u => 2 * (f₁ u * s₁ u)) ν :=
    hcv (continuous_const.mul (f₁.continuous.mul s₁.continuous))
  have i3 : Integrable (fun u => ψ u * s₂ u) ν := hcv (ψ.continuous.mul s₂.continuous)
  rw [integral_sub_add' ν i1 i2 i3, integral_const_mul]
  have h3 : ∫ u, ψ u * s₂ u ∂ν = ∫ u, g u ^ 2 * ψ u * sψ u ∂ν := by
    simp only [hs₂, hsψ]
    rw [pairing_swap ν ψ f₂]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hf₂]
    ring
  have h2 : ∫ u, f₁ u * s₁ u ∂ν = ∫ u, ∫ v, (g u * ψ u) * twistedKernel n β (u, v) * (g v * ψ v) ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hs₁, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [hf₁, hf₁]
    ring
  have h1 : ∫ u, g u ^ 2 * ψ u * sψ u ∂ν =
      ∫ u, g u ^ 2 * ψ u * (∫ v, twistedKernel n β (u, v) * ψ v ∂ν) ∂ν := by
    simp only [hsψ]
  rw [h3, h2, h1]
  ring

end Trial

/-- The Dirichlet form of the trial chain, compressed to the valley. -/
def valleyDirichlet (σ : ℝ) (ψ g : C(Slice n, ℝ)) : ℝ :=
  ∫ u in valley n σ, ∫ v in valley n σ, ψ u * twistedKernel n β (u, v) * ψ v * (g u - g v) ^ 2 ∂μ' ∂μ'

/-- The local Poincaré inequality. It concerns only the trial function, the valley and the actual kernel. An instance
with an exponential constant and `ψ = η` is `valleyPoincare_explicit`. **Open:** an explicit `ψ` with `C` about `n`. -/
def ValleyPoincare (σ : ℝ) (ψ : C(Slice n, ℝ)) (M C : ℝ) : Prop :=
  ∀ g, Invariant n g → ∫ u in valley n σ, g u * ψ u ^ 2 ∂μ' = 0 →
    2 * M * ∫ u in valley n σ, g u ^ 2 * ψ u ^ 2 ∂μ' ≤ C * valleyDirichlet n β σ ψ g

/-- **Local Collatz bound plus local Poincaré gives `ValleyGap`.** Here `M` is the largest local eigenvalue
of `ψ` for the compressed kernel. Neither hypothesis mentions the ground state. For an explicit `ψ` at relative
accuracy `1/n`, and `C` about `n`, both are open. -/
theorem valleyGap_of_trial (σ : ℝ) (ψ : C(Slice n, ℝ)) (hψ : ∀ u, 0 < ψ u) (hinv : Invariant n ψ)
    (M C : ℝ) (hC : 0 < C)
    (hColl : ∀ u ∈ valley n σ, ∫ v in valley n σ, twistedKernel n β (u, v) * ψ v ∂μ' ≤ M * ψ u)
    (hP : ValleyPoincare n β σ ψ M C) : ValleyGap n β σ (M * (1 - 1 / C)) ψ := by
  intro h hh hmean
  let g : C(Slice n, ℝ) := ⟨fun u => h u / ψ u, h.continuous.div ψ.continuous fun u => (hψ u).ne'⟩
  have hgv (u : Slice n) : g u = h u / ψ u := rfl
  have hhg (u : Slice n) : h u = g u * ψ u := by
    rw [hgv]
    field_simp [(hψ u).ne']
  have hgi : Invariant n g :=
    { gauge := fun k u => by rw [hgv, hgv, hh.gauge, hinv.gauge]
      flip := fun i c u => by rw [hgv, hgv, hh.flip, hinv.flip] }
  have hgmean : ∫ u in valley n σ, g u * ψ u ^ 2 ∂μ' = 0 := by
    rw [← hmean]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hhg u]
    ring
  have hPg := hP g hgi hgmean
  have hid := trial_identity (n := n) (β := β) ((μ').restrict (valley n σ)) ψ g
  change valleyDirichlet n β σ ψ g = _ at hid
  have hform : ∫ u in valley n σ, ∫ v in valley n σ,
      (g u * ψ u) * twistedKernel n β (u, v) * (g v * ψ v) ∂μ' ∂μ' = valleyForm n β σ h := by
    unfold valleyForm
    simp only [hhg]
  rw [hform] at hid
  set Z := ∫ u in valley n σ, h u ^ 2 ∂μ' with hZ
  have hZe : ∫ u in valley n σ, g u ^ 2 * ψ u ^ 2 ∂μ' = Z := by
    rw [hZ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hhg u]
    ring
  rw [hZe] at hPg
  -- the Collatz bound on the first term
  have hY : ∫ u in valley n σ, g u ^ 2 * ψ u * (∫ v in valley n σ, twistedKernel n β (u, v) * ψ v ∂μ') ∂μ' ≤
      M * Z := by
    rw [← hZe, ← integral_const_mul]
    let sψ : C(Slice n, ℝ) := smoothOn (n := n) (β := β) ((μ').restrict (valley n σ)) ψ
    have hsψ (u : Slice n) : sψ u = ∫ v in valley n σ, twistedKernel n β (u, v) * ψ v ∂μ' := rfl
    simp only [← hsψ]
    refine setIntegral_mono_on (ci n (((g.continuous.pow 2).mul ψ.continuous).mul sψ.continuous)).integrableOn
      (ci n (continuous_const.mul ((g.continuous.pow 2).mul (ψ.continuous.pow 2)))).integrableOn
      (valley_open n σ).measurableSet fun u hu => ?_
    have h1 := hColl u hu
    rw [← hsψ] at h1
    have h2 : 0 ≤ g u ^ 2 * ψ u := mul_nonneg (sq_nonneg _) (hψ u).le
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    calc g u ^ 2 * ψ u * sψ u ≤ g u ^ 2 * ψ u * (M * ψ u) := h3
      _ = M * (g u ^ 2 * ψ u ^ 2) := by ring
  rw [hid] at hPg
  set Q := valleyForm n β σ h with hQ
  set Y := ∫ u in valley n σ, g u ^ 2 * ψ u * (∫ v in valley n σ, twistedKernel n β (u, v) * ψ v ∂μ') ∂μ'
    with hYd
  have hfin : Q ≤ M * Z - M * Z / C := by
    have h1 : M * Z / C ≤ Y - Q := by
      rw [div_le_iff₀ hC]
      nlinarith only [hPg]
    linarith only [h1, hY]
  have e : M * (1 - 1 / C) * Z = M * Z - M * Z / C := by
    field_simp
  rw [e]
  exact hfin

/-! ### The norm from below, on one valley -/

theorem form_le_norm (h : C(Slice n, ℝ)) :
    ∫ u, h u * (∫ v, twistedKernel n β (u, v) * h v ∂μ') ∂μ' ≤ ‖T‖ * ∫ u, h u ^ 2 ∂μ' := by
  set F := ContinuousMap.toLp 2 (μ') ℂ (complexify h) with hF
  have hFsq : ‖F‖ ^ 2 = ∫ u, h u ^ 2 ∂μ' := by
    rw [hF, WilsonPositiveGroundState.real_embedding_norm_sq]
  have hinner : inner ℂ F (T F) = ((∫ u, h u * (∫ v, twistedKernel n β (u, v) * h v ∂μ') ∂μ' : ℝ) : ℂ) := by
    rw [hF, transfer_embed, inner_embed]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [sm_apply]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) F (T F)
  rw [hinner, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 := (T).le_opNorm F
  have h3 := norm_nonneg F
  calc _ ≤ _ := le_abs_self _
    _ ≤ ‖F‖ * ‖T F‖ := h1
    _ ≤ ‖F‖ * (‖T‖ * ‖F‖) := mul_le_mul_of_nonneg_left h2 h3
    _ = ‖T‖ * ‖F‖ ^ 2 := by ring
    _ = _ := by rw [hFsq]

/-- A nonnegative trial function on the valley bounds the norm from below. -/
theorem valleyForm_le_norm (σ : ℝ) (h : C(Slice n, ℝ)) (hnn : ∀ u, 0 ≤ h u) :
    valleyForm n β σ h ≤ ‖T‖ * ∫ u, h u ^ 2 ∂μ' := by
  refine le_trans ?_ (form_le_norm n β h)
  rw [form_eq_prod]
  have hGi := pairFn_integrable n β h
  have hS : ∫ p in valley n σ ×ˢ valley n σ, pairFn n β h p ∂((μ').prod (μ')) = valleyForm n β σ h := by
    rw [setIntegral_prod _ hGi.integrableOn]
    rfl
  rw [← hS]
  refine setIntegral_le_integral hGi (Filter.Eventually.of_forall fun p => ?_)
  have := (twistedKernel_pos n β p).le
  change (0 : ℝ) ≤ h p.1 * twistedKernel n β p * h p.2
  have h1 := hnn p.1
  have h2 := hnn p.2
  positivity

/-! ### The temporal average disappears on gauge-invariant functions -/

/-- The kinetic weight of a pair of fields, with no temporal gauge. A product over links. -/
def kinW (u v : Slice n) : ℝ := Real.exp (-β * kineticAction character 2 u v)

theorem kinW_pos (u v : Slice n) : 0 < kinW n β u v := Real.exp_pos _

theorem kinW_le_one (hβ : 0 ≤ β) (u v : Slice n) : kinW n β u v ≤ 1 := by
  have h : kinW n β u v = Real.exp (-β * temporalAction character 2 u v (fun _ => 1)) := by
    unfold kinW
    rw [temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]
    congr 3
    funext e
    simp [gaugeSlice]
  rw [h]
  exact exp_temporal_le n β hβ u v _

theorem kinW_continuous (u : Slice n) : Continuous (kinW n β u) := by
  have hc := WilsonSingleLinkStaples.character_continuous
  unfold kinW kineticAction
  fun_prop

theorem avg_eq (u v : Slice n) :
    avg n β u v = ∫ k, kinW n β u (gaugeSlice k v) ∂(temporalHaar (n := n) (G := Q)) := by
  unfold avg kinW
  simp only [temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]

/-- **No Laplace evaluation of the temporal gauge is needed.** Against a gauge-invariant function, the
temporal average can be dropped exactly, by Haar invariance. -/
theorem avg_integral_invariant (hβ : 0 ≤ β) (u : Slice n) (E : Slice n → ℝ) (hE : Integrable E μ')
    (hinv : ∀ (k : SliceGauge n Q) v, E (gaugeSlice k v) = E v) :
    ∫ v, avg n β u v * E v ∂μ' = ∫ v, kinW n β u v * E v ∂μ' := by
  set ν := temporalHaar (n := n) (G := Q) with hν
  have hkc : Continuous fun p : Slice n × SliceGauge n Q => kinW n β u (gaugeSlice p.2 p.1) := by
    have hc := WilsonSingleLinkStaples.character_continuous
    unfold kinW kineticAction gaugeSlice
    fun_prop
  have hFi : Integrable (fun p : Slice n × SliceGauge n Q => kinW n β u (gaugeSlice p.2 p.1) * E p.1)
      ((μ').prod ν) := by
    refine Integrable.bdd_mul (c := 1) (hE.comp_fst ν) hkc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (kinW_pos n β _ _)]
    exact kinW_le_one n β hβ _ _
  calc ∫ v, avg n β u v * E v ∂μ'
      = ∫ v, ∫ k, kinW n β u (gaugeSlice k v) * E v ∂ν ∂μ' := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        rw [avg_eq, integral_mul_const]
    _ = ∫ k, ∫ v, kinW n β u (gaugeSlice k v) * E v ∂μ' ∂ν :=
        integral_integral_swap (f := fun v k => kinW n β u (gaugeSlice k v) * E v) hFi
    _ = ∫ _k : SliceGauge n Q, ∫ v, kinW n β u v * E v ∂μ' ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        dsimp only
        have h := (WilsonSlabGauge.gauge_preserves_spatial k).integral_comp
          (WilsonSlabGauge.gaugeHomeomorph k).measurableEmbedding (fun v => kinW n β u v * E v)
        rw [← h]
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hinv]
    _ = _ := by simp

/-- **The transfer operator on gauge-invariant functions is `w K₀ w`**, with `w` the spatial weight and
`K₀` the product over links of single-link kernels. -/
theorem integral_kernel_invariant (hβ : 0 ≤ β) (u : Slice n) (G : C(Slice n, ℝ))
    (hG : ∀ (k : SliceGauge n Q) v, G (gaugeSlice k v) = G v) :
    ∫ v, twistedKernel n β (u, v) * G v ∂μ' = wt n β u * ∫ v, kinW n β u v * (wt n β v * G v) ∂μ' := by
  have hi : Integrable (fun v => wt n β v * G v) μ' := ci n ((wt_continuous n β).mul G.continuous)
  rw [← avg_integral_invariant n β hβ u _ hi fun k v => by rw [wt_gauge, hG], ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [kernel_factor]
  ring

/-- **The valley form in kinetic form.** For gauge-invariant `h` the compressed form contains no temporal
integral. So the open statement `ValleyGap` is about the explicit kernel `w K₀ w`. -/
theorem valleyForm_kinetic (hβ : 0 ≤ β) (σ : ℝ) (h : C(Slice n, ℝ))
    (hh : ∀ (k : SliceGauge n Q) v, h (gaugeSlice k v) = h v) :
    valleyForm n β σ h =
      ∫ u in valley n σ, ∫ v in valley n σ, (wt n β u * h u) * kinW n β u v * (wt n β v * h v) ∂μ' ∂μ' := by
  unfold valleyForm
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  set V := valley n σ with hV
  have hVm : MeasurableSet V := (valley_open n σ).measurableSet
  let E : Slice n → ℝ := V.indicator fun v => wt n β v * h v
  have hEi : Integrable E μ' :=
    (ci n ((wt_continuous n β).mul h.continuous)).integrableOn.integrable_indicator hVm
  have hmem (k : SliceGauge n Q) (v : Slice n) : gaugeSlice k v ∈ V ↔ v ∈ V := by
    simp only [hV, valley, Set.mem_setOf_eq, twistedPotential_gauge, holo_gauge]
  have hEinv (k : SliceGauge n Q) (v : Slice n) : E (gaugeSlice k v) = E v := by
    by_cases hv : v ∈ V
    · simp only [E, Set.indicator_of_mem hv, Set.indicator_of_mem ((hmem k v).mpr hv), wt_gauge, hh]
    · simp only [E, Set.indicator_of_notMem hv,
        Set.indicator_of_notMem (fun hc => hv ((hmem k v).mp hc))]
  have hkey := avg_integral_invariant n β hβ u E hEi hEinv
  have hL : ∫ v in V, h u * twistedKernel n β (u, v) * h v ∂μ' =
      (h u * wt n β u) * ∫ v, avg n β u v * E v ∂μ' := by
    rw [← integral_const_mul, ← integral_indicator hVm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ V
    · simp only [E, Set.indicator_of_mem hv, kernel_factor]
      ring
    · simp only [E, Set.indicator_of_notMem hv, mul_zero]
  have hR : ∫ v in V, (wt n β u * h u) * kinW n β u v * (wt n β v * h v) ∂μ' =
      (h u * wt n β u) * ∫ v, kinW n β u v * E v ∂μ' := by
    rw [← integral_const_mul, ← integral_indicator hVm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    by_cases hv : v ∈ V
    · simp only [E, Set.indicator_of_mem hv]
      ring
    · simp only [E, Set.indicator_of_notMem hv, mul_zero]
  rw [hL, hR, hkey]

/-- The kinetic kernel integrates to an exact power of the single-link Gaussian mass. -/
theorem kinW_mass (u : Slice n) :
    ∫ v, kinW n β u v ∂μ' = SU2GaussianMass.mass β ^ TwistedNormLower.links n := by
  have h := integral_fintype_prod_eq_prod (ι := SpatialVertex n × Fin 3) (E := fun _ => Q)
    (fun e q => Real.exp (-β * TwistedStability.d q (u e) ^ 2))
    (μ := fun _ => RegulatedGauge.compactHaar Q)
  have hp (v : Slice n) : kinW n β u v = ∏ e, Real.exp (-β * TwistedStability.d (v e) (u e) ^ 2) := by
    rw [← Real.exp_sum, kinW, kineticAction, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [kinetic_term, TwistedStability.d_comm]
  simp only [hp]
  refine h.trans ?_
  simp only [TwistedLocalization.gaussian_translate, Finset.prod_const, Finset.card_univ,
    TwistedNormLower.links]

/-- **A Schur bound.** With `norm_lower'`, `mass(24 β)^{7n³} ≤ ‖T‖ ≤ mass(β)^{3n³}`. Both couplings and exponents differ,
so `log ‖T‖` is pinned only to within about `6 n³ log β`. This is far from the relative accuracy `1/n` needed for the
levels `r` and `M`, and it does not address that. -/
theorem norm_le_mass (hβ : 0 ≤ β) : ‖T‖ ≤ SU2GaussianMass.mass β ^ TwistedNormLower.links n := by
  have hm := SU2GaussianMass.mass_pos β
  have hpos : (0 : ℝ) < 1 := one_pos
  let one : C(Slice n, ℝ) := 1
  have h1 (u : Slice n) : one u = 1 := rfl
  refine (TwistedCollatz.collatz_wielandt n β hβ one (fun u => by rw [h1]; exact hpos) 0
    (SU2GaussianMass.mass β ^ TwistedNormLower.links n) (fun u => ?_) (fun u => ?_)).2
  · rw [zero_mul]
    exact integral_nonneg fun v => mul_nonneg (twistedKernel_pos n β (u, v)).le (by rw [h1]; exact zero_le_one)
  · rw [h1, mul_one, integral_kernel_invariant n β hβ u one fun _ _ => rfl, ← kinW_mass n β u]
    have hint : Integrable (fun v => kinW n β u v * (wt n β v * one v)) μ' :=
      ci n ((kinW_continuous n β u).mul ((wt_continuous n β).mul one.continuous))
    have hle : ∫ v, kinW n β u v * (wt n β v * one v) ∂μ' ≤ ∫ v, kinW n β u v ∂μ' := by
      refine integral_mono hint (ci n (kinW_continuous n β u)) fun v => ?_
      dsimp only
      rw [h1, mul_one]
      exact mul_le_of_le_one_right (kinW_pos n β u v).le (wt_le_one n β hβ v)
    have hnn : 0 ≤ ∫ v, kinW n β u v * (wt n β v * one v) ∂μ' :=
      integral_nonneg fun v => by
        rw [h1, mul_one]
        exact mul_nonneg (kinW_pos n β u v).le (wt_pos n β v).le
    exact (mul_le_of_le_one_left hnn (wt_le_one n β hβ u)).trans hle

/-! ### An unconditional instance of the Poincaré inequality -/

theorem potential_le_card (u : Slice n) : twistedPotential n u ≤ 12 * (n : ℝ) ^ 3 := by
  have hterm (x : SpatialVertex n) (p : SpatialPlane) :
      2 - spatialSign n x p * (character (spatialHolonomy u x p.1.1 p.1.2)).re ≤ 4 := by
    rw [WilsonSingleLinkStaples.character_re]
    have hre := abs_le.mp (TwistedFlat.re_le_one (spatialHolonomy u x p.1.1 p.1.2))
    unfold spatialSign
    split_ifs <;> linarith only [hre.1, hre.2]
  calc twistedPotential n u ≤ ∑ _x : SpatialVertex n, ∑ _p : SpatialPlane, (4 : ℝ) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun p _ => hterm x p
    _ = 12 * (n : ℝ) ^ 3 := by
        have hp : Fintype.card SpatialPlane = 3 := by decide
        have hx : Fintype.card (SpatialVertex n) = n ^ 3 := TwistedNormLower.sites_eq n
        simp only [Finset.sum_const, Finset.card_univ, hp, hx, nsmul_eq_mul]
        push_cast
        ring

theorem kinetic_le_card (u v : Slice n) : kineticAction character 2 u v ≤ 12 * (n : ℝ) ^ 3 := by
  have hterm (e : SpatialVertex n × Fin 3) : 2 - (character ((u e)⁻¹ * v e)).re ≤ 4 := by
    rw [WilsonSingleLinkStaples.character_re]
    have hre := abs_le.mp (TwistedFlat.re_le_one ((u e)⁻¹ * v e))
    linarith only [hre.1]
  calc kineticAction character 2 u v ≤ ∑ _e : SpatialVertex n × Fin 3, (4 : ℝ) :=
        Finset.sum_le_sum fun e _ => hterm e
    _ = 12 * (n : ℝ) ^ 3 := by
        have hx : Fintype.card (SpatialVertex n × Fin 3) = 3 * n ^ 3 := TwistedNormLower.links_eq n
        simp only [Finset.sum_const, Finset.card_univ, hx, nsmul_eq_mul]
        push_cast
        ring

/-- The worst-case lower bound on the kernel. -/
theorem kernel_ge (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-(24 * β * (n : ℝ) ^ 3)) ≤ twistedKernel n β (u, v) := by
  have hw (x : Slice n) : Real.exp (-(6 * β * (n : ℝ) ^ 3)) ≤ wt n β x := by
    unfold wt
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left (potential_le_card n x) hβ]
  have ha : Real.exp (-(12 * β * (n : ℝ) ^ 3)) ≤ avg n β u v := by
    have h1 := integral_mono (integrable_const (Real.exp (-(12 * β * (n : ℝ) ^ 3))))
      (avg_integrable n β hβ u v) (μ := temporalHaar (n := n) (G := Q)) fun k => by
        apply Real.exp_le_exp.mpr
        rw [temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]
        nlinarith only [mul_le_mul_of_nonneg_left (kinetic_le_card n u (gaugeSlice k v)) hβ]
    simpa [avg] using h1
  have e : Real.exp (-(24 * β * (n : ℝ) ^ 3)) =
      Real.exp (-(6 * β * (n : ℝ) ^ 3)) * Real.exp (-(12 * β * (n : ℝ) ^ 3)) *
        Real.exp (-(6 * β * (n : ℝ) ^ 3)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e, kernel_factor]
  have h0 := Real.exp_pos (-(6 * β * (n : ℝ) ^ 3))
  have h1 := Real.exp_pos (-(12 * β * (n : ℝ) ^ 3))
  exact mul_le_mul (mul_le_mul (hw u) ha h1.le (wt_pos n β u).le) (hw v) h0.le
    (mul_nonneg (wt_pos n β u).le (avg_nonneg n β hβ u v))

theorem kernel_le_one (hβ : 0 ≤ β) (u v : Slice n) : twistedKernel n β (u, v) ≤ 1 := by
  have h1 := kernel_le_wt n β hβ u v
  have h2 := wt_le_one n β hβ u
  have h3 := wt_le_one n β hβ v
  have h4 := (wt_pos n β v).le
  nlinarith only [h1, h2, h3, h4, wt_pos n β u]

theorem norm_bounds (hβ : 0 ≤ β) : Real.exp (-(24 * β * (n : ℝ) ^ 3)) ≤ ‖T‖ ∧ ‖T‖ ≤ 1 := by
  let one : C(Slice n, ℝ) := 1
  have h1 (u : Slice n) : one u = 1 := rfl
  refine TwistedCollatz.collatz_wielandt n β hβ one (fun u => by rw [h1]; exact one_pos) _ 1
    (fun u => ?_) (fun u => ?_)
  · have hc : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    have hm := integral_mono (integrable_const (Real.exp (-(24 * β * (n : ℝ) ^ 3))))
      (ci n hc) (μ := μ') fun v => kernel_ge n β hβ u v
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
    simp only [h1, mul_one]
    exact hm
  · have hc : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    have hm := integral_mono (ci n hc) (integrable_const (1 : ℝ)) (μ := μ')
      fun v => kernel_le_one n β hβ u v
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
    simp only [h1, mul_one]
    exact hm

/-- **The neutral Poincaré inequality holds unconditionally, with constant `exp(72 β n³)`.** This is the
first instance of `NeutralPoincare` here. The constant is exponentially far from the required `n/c`. It
uses nothing about the valleys, and it does not use neutrality. -/
theorem neutralPoincare_explicit (hβ : 0 ≤ β) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) :
    NeutralPoincare n β η (Real.exp (72 * β * (n : ℝ) ^ 3)) := by
  intro g hg
  obtain ⟨hk, hT1⟩ := norm_bounds n β hβ
  set k := Real.exp (-(24 * β * (n : ℝ) ^ 3)) with hkd
  have hkpos : 0 < k := Real.exp_pos _
  have hlam : 0 < ‖T‖ := hkpos.trans_le hk
  have hkη (u : Slice n) : k * η u ^ 2 ≤ η u := by
    have h1 := eta_le n β hβ η hη hnorm heig hlam u
    have h2 : η u ≤ 1 / k := by
      refine h1.trans ?_
      have h3 := wt_le_one n β hβ u
      exact div_le_div₀ zero_le_one h3 hkpos hk
    have h4 : k * η u ≤ 1 := by
      rw [le_div_iff₀ hkpos] at h2
      linarith only [h2]
    have h5 := (hη u).le
    nlinarith only [mul_le_mul_of_nonneg_right h4 h5]
  set X := ∫ u, g u ^ 2 * η u ^ 2 ∂μ' with hX
  have hX0 : 0 ≤ X := integral_nonneg fun u => by positivity
  -- the pointwise comparison
  have hin (u : Slice n) :
      k ^ 3 * (η u ^ 2 * (g u ^ 2 + X)) ≤
        η u * (∫ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ') := by
    have hK : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    have hc2 : Continuous fun v => twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 :=
      (hK.mul η.continuous).mul ((continuous_const.sub g.continuous).pow 2)
    have hcomp : ∫ v, η v ^ 2 * (g u - g v) ^ 2 ∂μ' = g u ^ 2 + X := by
      have e : ∀ v, η v ^ 2 * (g u - g v) ^ 2 =
          (g u ^ 2) * η v ^ 2 - (2 * g u) * (g v * η v ^ 2) + g v ^ 2 * η v ^ 2 := fun v => by ring
      simp only [e]
      rw [integral_three n (fun v => η v ^ 2) (fun v => g v * η v ^ 2) (fun v => g v ^ 2 * η v ^ 2)
        (η.continuous.pow 2) (g.continuous.mul (η.continuous.pow 2))
        ((g.continuous.pow 2).mul (η.continuous.pow 2)), hnorm, hg.mean]
      ring
    have hmono : ∫ v, k ^ 2 * (η v ^ 2 * (g u - g v) ^ 2) ∂μ' ≤
        ∫ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ' := by
      refine integral_mono (ci n (continuous_const.mul ((η.continuous.pow 2).mul
        ((continuous_const.sub g.continuous).pow 2)))) (ci n hc2) fun v => ?_
      dsimp only
      have h1 : k * k * η v ^ 2 ≤ twistedKernel n β (u, v) * η v := by
        have h2 := kernel_ge n β hβ u v
        have h3 := hkη v
        calc k * k * η v ^ 2 = k * (k * η v ^ 2) := by ring
          _ ≤ twistedKernel n β (u, v) * η v :=
            mul_le_mul h2 h3 (by positivity) (twistedKernel_pos n β (u, v)).le
      have h4 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (g u - g v))
      calc _ = k * k * η v ^ 2 * (g u - g v) ^ 2 := by ring
        _ ≤ _ := h4
    rw [integral_const_mul, hcomp] at hmono
    have hnn : 0 ≤ k ^ 2 * (g u ^ 2 + X) := by positivity
    have h5 := mul_le_mul_of_nonneg_right (hkη u) hnn
    have h6 := mul_le_mul_of_nonneg_left hmono (hη u).le
    calc _ = k * η u ^ 2 * (k ^ 2 * (g u ^ 2 + X)) := by ring
      _ ≤ η u * (k ^ 2 * (g u ^ 2 + X)) := h5
      _ ≤ _ := h6
  have hF : Continuous fun u => η u * (∫ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ') := by
    refine η.continuous.mul ?_
    have hf : Continuous (Function.uncurry fun (u v : Slice n) =>
        twistedKernel n β (u, v) * η v * (g u - g v) ^ 2) :=
      ((twistedKernel n β).continuous.mul (η.continuous.comp continuous_snd)).mul
        (((g.continuous.comp continuous_fst).sub (g.continuous.comp continuous_snd)).pow 2)
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := μ') hf isCompact_univ)
  have hmono : ∫ u, k ^ 3 * (η u ^ 2 * (g u ^ 2 + X)) ∂μ' ≤
      ∫ u, η u * (∫ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ') ∂μ' :=
    integral_mono (ci n (continuous_const.mul ((η.continuous.pow 2).mul
      ((g.continuous.pow 2).add continuous_const)))) (ci n hF) hin
  have hleft : ∫ u, k ^ 3 * (η u ^ 2 * (g u ^ 2 + X)) ∂μ' = k ^ 3 * (2 * X) := by
    rw [integral_const_mul]
    congr 1
    have e : ∀ u, η u ^ 2 * (g u ^ 2 + X) = 1 * (g u ^ 2 * η u ^ 2) - 0 * η u + X * η u ^ 2 :=
      fun u => by ring
    simp only [e]
    rw [integral_three n (fun u => g u ^ 2 * η u ^ 2) (fun u => η u) (fun u => X * η u ^ 2)
      ((g.continuous.pow 2).mul (η.continuous.pow 2)) η.continuous
      (continuous_const.mul (η.continuous.pow 2)), integral_const_mul, hnorm]
    ring
  rw [hleft] at hmono
  change k ^ 3 * (2 * X) ≤ dirichlet n β η g at hmono
  have hC : Real.exp (72 * β * (n : ℝ) ^ 3) * k ^ 3 = 1 := by
    rw [hkd, ← Real.exp_nat_mul, ← Real.exp_add]
    have e : 72 * β * (n : ℝ) ^ 3 + ((3 : ℕ) : ℝ) * -(24 * β * (n : ℝ) ^ 3) = 0 := by
      push_cast
      ring
    rw [e, Real.exp_zero]
  have hCpos := Real.exp_pos (72 * β * (n : ℝ) ^ 3)
  have h1 := mul_le_mul_of_nonneg_left hmono hCpos.le
  have h2 : Real.exp (72 * β * (n : ℝ) ^ 3) * (k ^ 3 * (2 * X)) = 2 * X := by
    rw [← mul_assoc, hC, one_mul]
  rw [h2] at h1
  have h3 : 2 * ‖T‖ * X ≤ 2 * X := by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0]
  exact h3.trans h1

/-- **A quantified finite gap.** `TwistedFiniteGap` gives some `ρ < 1` with no control. Here
`ρ = 1 - exp(-72 β n³)` on the neutral complement. -/
theorem gap_explicit (hβ : 0 ≤ β) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) :
    ∀ f, Neutral n f → inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 →
      ‖T f‖ ≤ (1 - Real.exp (-(72 * β * (n : ℝ) ^ 3))) * ‖T‖ * ‖f‖ := by
  have hC : 1 ≤ Real.exp (72 * β * (n : ℝ) ^ 3) := Real.one_le_exp (by positivity)
  have h := gap_of_poincare n β hβ η hη heig _ hC (neutralPoincare_explicit n β hβ η hη hnorm heig)
  rw [one_div, ← Real.exp_neg] at h
  exact h

/-! ### Low eigenfunctions concentrate on the valleys -/

/-- Every real eigenfunction is bounded by the spatial weight. This is `eta_le` without positivity. -/
theorem eigen_abs_le (hβ : 0 ≤ β) (φ : C(Slice n, ℝ)) (hnorm : ∫ u, φ u ^ 2 ∂μ' = 1) (lam' : ℝ)
    (hlam' : 0 < lam') (hφeig : ∀ u, (∫ v, twistedKernel n β (u, v) * φ v ∂μ') = lam' * φ u)
    (u : Slice n) : |φ u| ≤ wt n β u / lam' := by
  have hK : Continuous fun v => twistedKernel n β (u, v) :=
    (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
  have h1 : ∫ v, |φ v| ∂μ' ≤ 1 := by
    have := abs_mean_sq_le n φ
    rw [hnorm] at this
    have h0 : 0 ≤ ∫ v, |φ v| ∂μ' := integral_nonneg fun v => abs_nonneg _
    nlinarith only [this, h0]
  have h2 : |∫ v, twistedKernel n β (u, v) * φ v ∂μ'| ≤ ∫ v, wt n β u * |φ v| ∂μ' := by
    refine (abs_integral_le_integral_abs).trans (integral_mono (ci n (hK.mul φ.continuous).abs)
      (ci n (continuous_const.mul φ.continuous.abs)) fun v => ?_)
    dsimp only
    rw [abs_mul, abs_of_pos (twistedKernel_pos n β (u, v))]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have h3 := kernel_le_wt n β hβ u v
    have h4 := wt_le_one n β hβ v
    have h5 := wt_pos n β u
    nlinarith only [h3, h4, h5]
  rw [hφeig, abs_mul, abs_of_pos hlam', integral_const_mul] at h2
  rw [le_div_iff₀ hlam']
  have h6 := (wt_pos n β u).le
  nlinarith only [h2, mul_le_mul_of_nonneg_left h1 h6]

/-- **An unconditional statement about the actual eigenfunctions.** A flip-even unit eigenfunction with
eigenvalue `λ'` has all but `exp(-βσ)/λ'²` of its mass on the two valleys, equally divided. -/
theorem eigen_valley_mass (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (φ : C(Slice n, ℝ))
    (hflip : ∀ u, φ (TwistedTransfer.flip n 2 0 u) = φ u) (hnorm : ∫ u, φ u ^ 2 ∂μ' = 1) (lam' : ℝ)
    (hlam' : 0 < lam') (hφeig : ∀ u, (∫ v, twistedKernel n β (u, v) * φ v ∂μ') = lam' * φ u) :
    1 - Real.exp (-(β * σ)) / lam' ^ 2 ≤ 2 * ∫ u in valley n σ, φ u ^ 2 ∂μ' := by
  have hi : Integrable (fun u => φ u ^ 2) μ' := ci n (φ.continuous.pow 2)
  set V := valley n σ
  set W := mirror n σ
  have hVm : MeasurableSet V := (valley_open n σ).measurableSet
  have hWm : MeasurableSet W := (mirror_open n σ).measurableSet
  have hmirror : ∫ u in W, φ u ^ 2 ∂μ' = ∫ u in V, φ u ^ 2 ∂μ' := by
    have hmp : MeasurePreserving (flipEquiv n 2 0) (μ') (μ') := flip_measurePreserving n 2 0
    have := hmp.setIntegral_preimage_emb (flipEquiv n 2 0).measurableEmbedding
      (fun u => φ u ^ 2) W
    rw [← this]
    have hpre : (flipEquiv n 2 0) ⁻¹' W = V := by
      ext u
      exact flip_mem_mirror n σ u
    rw [hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change φ (TwistedTransfer.flip n 2 0 u) ^ 2 = φ u ^ 2
    rw [hflip]
  have hU := setIntegral_union (μ := μ') (f := fun u => φ u ^ 2) (valley_disjoint n σ) hWm
    hi.integrableOn hi.integrableOn
  have hsplit := integral_add_compl (hVm.union hWm) hi
  rw [hU, hmirror, hnorm] at hsplit
  have hrem : ∫ u in (V ∪ W)ᶜ, φ u ^ 2 ∂μ' ≤ Real.exp (-(β * σ)) / lam' ^ 2 := by
    have hconst : Integrable (fun _ : Slice n => Real.exp (-(β * σ)) / lam' ^ 2) μ' := integrable_const _
    have h1 : ∫ u in (V ∪ W)ᶜ, φ u ^ 2 ∂μ' ≤
        ∫ _u in (V ∪ W)ᶜ, Real.exp (-(β * σ)) / lam' ^ 2 ∂μ' := by
      refine setIntegral_mono_on hi.integrableOn hconst.integrableOn (hVm.union hWm).compl fun u hu => ?_
      have hge : σ ≤ twistedPotential n u := by
        by_contra hc
        push_neg at hc
        have hs := holo_sq_of_small n u (hc.trans_le hσ)
        rcases lt_trichotomy (holo n u) 0 with h | h | h
        · exact hu (Or.inr ⟨hc, h⟩)
        · rw [h] at hs
          norm_num at hs
        · exact hu (Or.inl ⟨hc, h⟩)
      have h2 := eigen_abs_le n β hβ φ hnorm lam' hlam' hφeig u
      have h3 := wt_le_of_ge n β hβ σ u hge
      have h4 : |φ u| ≤ Real.exp (-(β * σ / 2)) / lam' :=
        h2.trans (div_le_div_of_nonneg_right h3 hlam'.le)
      have h5 : φ u ^ 2 ≤ (Real.exp (-(β * σ / 2)) / lam') ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h4 2
      refine h5.trans_eq ?_
      rw [div_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have h2 : ∫ _u in (V ∪ W)ᶜ, Real.exp (-(β * σ)) / lam' ^ 2 ∂μ' ≤ Real.exp (-(β * σ)) / lam' ^ 2 := by
      rw [setIntegral_const, smul_eq_mul]
      have hreal : (μ').real (V ∪ W)ᶜ ≤ 1 := by
        exact measureReal_le_one
      have hnn : 0 ≤ Real.exp (-(β * σ)) / lam' ^ 2 := by positivity
      exact mul_le_of_le_one_left hnn hreal
    exact h1.trans h2
  linarith only [hsplit, hrem]

/-! ### The explicit coupling threshold -/

/-- Absolute value of the logarithm of the constant in `mass_lower_poly`. -/
def capLog : ℝ := |Real.log (SU2GaussianMass.cap 1)|

/-- The constant in the threshold. -/
def threshold : ℝ := 64 * (254 + 7 * capLog)

theorem capLog_nonneg : 0 ≤ capLog := abs_nonneg _

theorem threshold_pos : 0 < threshold := by
  unfold threshold
  have := capLog_nonneg
  positivity

theorem cap_one_pos : 0 < SU2GaussianMass.cap 1 := by
  have h := SU2GaussianMass.mass_cap_lower 1 (by norm_num)
  have h0 := SU2GaussianMass.cap_nonneg 1 (by norm_num)
  rcases h0.eq_or_lt with he | hp
  · rw [← he, mul_zero] at h
    norm_num at h
  · exact hp

/-- **The off-diagonal error is negligible for `β ≥ A n⁸`.** With `σ = 1/(16 n⁴)`, `offError` is at most
`exp(-n⁴)` times the lower bound on `‖T‖`. The constant `A` is absolute. -/
theorem offError_le_threshold (n : ℕ) [NeZero n] (β : ℝ) (hβ : threshold * (n : ℝ) ^ 8 ≤ β) :
    offError n β (1 / (16 * (n : ℝ) ^ 4)) ≤
      Real.exp (-(n : ℝ) ^ 4) * SU2GaussianMass.mass (24 * β) ^
        (2 * TwistedNormLower.links n + TwistedNormLower.sites n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hnpos : (0 : ℝ) < n := by linarith only [hn1]
  have hL := capLog_nonneg
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
  have hn8 : (1 : ℝ) ≤ (n : ℝ) ^ 8 := one_le_pow₀ hn1
  have hn34 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
  have hβ1 : (1 : ℝ) ≤ β := by
    have h1 : (64 * 254 : ℝ) ≤ threshold := by
      unfold threshold
      nlinarith only [hL]
    nlinarith only [hβ, h1, hn8]
  have hβ0 : 0 < β := by linarith only [hβ1]
  set b := β / (32 * (n : ℝ) ^ 4) with hb
  -- the two exponentials
  have he₁ : Real.exp (-(2 * β / n)) ≤ Real.exp (-b) := by
    apply Real.exp_le_exp.mpr
    have h : b ≤ 2 * β / n := by
      rw [hb, div_le_div_iff₀ (by positivity) hnpos]
      have h1 : (n : ℝ) ≤ (n : ℝ) ^ 4 := le_self_pow₀ hn1 (by norm_num)
      have h2 := mul_le_mul_of_nonneg_left h1 hβ0.le
      have h3 : 0 < β * (n : ℝ) ^ 4 := by positivity
      nlinarith only [h2, h3]
    linarith only [h]
  have he₂ : Real.exp (-(β * (1 / (16 * (n : ℝ) ^ 4)) / 2)) = Real.exp (-b) := by
    congr 2
    rw [hb]
    field_simp
    ring
  have hoff : offError n β (1 / (16 * (n : ℝ) ^ 4)) ≤ 2 * Real.exp (-b) := by
    unfold offError
    rw [he₂]
    linarith only [he₁]
  -- the lower bound on the mass
  set K := SU2GaussianMass.cap 1 with hK
  have hKpos : 0 < K := cap_one_pos
  set Qv := K * (24 * β) ^ 2 with hQv
  have hQpos : 0 < Qv := by positivity
  have hmass : Qv⁻¹ ≤ SU2GaussianMass.mass (24 * β) :=
    mass_lower_poly β (by linarith only [hβ1])
  set m := 2 * TwistedNormLower.links n + TwistedNormLower.sites n with hm
  have hmv : (m : ℝ) = 7 * (n : ℝ) ^ 3 := by
    rw [hm, TwistedNormLower.links_eq, TwistedNormLower.sites_eq]
    push_cast
    ring
  have hPlow : (Qv ^ m)⁻¹ ≤ SU2GaussianMass.mass (24 * β) ^ m := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hQpos.le) hmass m
  -- the logarithm estimate
  set ℓ := Real.log (24 * β) with hℓ
  set c := 21504 * (n : ℝ) ^ 7 with hc
  have hcpos : 0 < c := by positivity
  have hlogc : Real.log c ≤ 11 + 7 * n := by
    rw [hc, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h1 : Real.log 21504 ≤ 11 := by
      have h2 : Real.log 21504 ≤ Real.log ((2 : ℝ) ^ 15) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h2
      have h3 := Real.log_two_lt_d9
      push_cast at h2
      linarith only [h2, h3]
    have h4 : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hnpos).trans (by linarith only)
    push_cast
    linarith only [h1, h4]
  have hℓle : ℓ ≤ 24 * β / c - 1 + Real.log c := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 24 * β / c by positivity)
    rw [Real.log_div (by positivity) hcpos.ne'] at h1
    linarith only [h1]
  have hscale : 14 * (n : ℝ) ^ 3 * (24 * β / c) = β / (64 * (n : ℝ) ^ 4) := by
    rw [hc]
    field_simp
    ring
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hmain : 14 * (n : ℝ) ^ 3 * ℓ ≤ β / (64 * (n : ℝ) ^ 4) + 14 * (n : ℝ) ^ 3 * (11 + 7 * n) := by
    have h1 := mul_le_mul_of_nonneg_left (hℓle.trans (by linarith only [hlogc] :
      24 * β / c - 1 + Real.log c ≤ 24 * β / c + (11 + 7 * n)))
      (show (0 : ℝ) ≤ 14 * (n : ℝ) ^ 3 by positivity)
    rw [mul_add, hscale] at h1
    exact h1
  have hLK : Real.log K ≤ capLog := le_abs_self _
  have hQlog : Real.log Qv = Real.log K + 2 * ℓ := by
    rw [hQv, Real.log_mul hKpos.ne' (by positivity), Real.log_pow]
    push_cast
    rfl
  have hbudget : β / (64 * (n : ℝ) ^ 4) ≥ (254 + 7 * capLog) * (n : ℝ) ^ 4 := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    have h1 : threshold * (n : ℝ) ^ 8 ≤ β := hβ
    unfold threshold at h1
    have e : (254 + 7 * capLog) * (n : ℝ) ^ 4 * (64 * (n : ℝ) ^ 4) =
        64 * (254 + 7 * capLog) * (n : ℝ) ^ 8 := by ring
    rw [e]
    exact h1
  have hbsplit : b = β / (64 * (n : ℝ) ^ 4) + β / (64 * (n : ℝ) ^ 4) := by
    rw [hb]
    field_simp
    ring
  -- assemble in the exponent
  have hexpo : (1 : ℝ) + (n : ℝ) ^ 4 + (m : ℝ) * Real.log Qv - b ≤ 0 := by
    rw [hQlog, hmv, hbsplit]
    have hnL : (n : ℝ) ^ 3 * Real.log K ≤ (n : ℝ) ^ 4 * capLog := by
      calc _ ≤ (n : ℝ) ^ 3 * capLog := mul_le_mul_of_nonneg_left hLK hn3
        _ ≤ _ := mul_le_mul_of_nonneg_right hn34 hL
    have hn3n : (n : ℝ) ^ 3 * n = (n : ℝ) ^ 4 := by ring
    have h14 : 14 * (n : ℝ) ^ 3 * (11 + 7 * n) ≤ 252 * (n : ℝ) ^ 4 := by
      have : 14 * (n : ℝ) ^ 3 * (11 + 7 * n) = 154 * (n : ℝ) ^ 3 + 98 * ((n : ℝ) ^ 3 * n) := by ring
      rw [this, hn3n]
      linarith only [hn34]
    nlinarith only [hmain, hbudget, hnL, hn4, h14]
  have hQm : Qv ^ m = Real.exp ((m : ℝ) * Real.log Qv) := by
    rw [Real.exp_nat_mul, Real.exp_log hQpos]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith only [this]
  have hfin : 2 * Real.exp (-b) ≤ Real.exp (-(n : ℝ) ^ 4) * (Qv ^ m)⁻¹ := by
    rw [hQm, ← Real.exp_neg, ← Real.exp_add]
    calc 2 * Real.exp (-b) ≤ Real.exp 1 * Real.exp (-b) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 + -b) := (Real.exp_add _ _).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          linarith only [hexpo]
  exact hoff.trans (hfin.trans (mul_le_mul_of_nonneg_left hPlow (Real.exp_pos _).le))

/-- The same, against the norm of `T`. -/
theorem offError_le_norm (n : ℕ) [NeZero n] (β : ℝ) (hβ : threshold * (n : ℝ) ^ 8 ≤ β) :
    offError n β (1 / (16 * (n : ℝ) ^ 4)) ≤
      Real.exp (-(n : ℝ) ^ 4) * ‖TwistedTransfer.transfer n β‖ := by
  have hβ0 : 0 ≤ β := by
    have := threshold_pos
    have h8 : (0 : ℝ) ≤ (n : ℝ) ^ 8 := by positivity
    have := mul_nonneg this.le h8
    linarith only [this, hβ]
  exact (offError_le_threshold n β hβ).trans
    (mul_le_mul_of_nonneg_left (TwistedNormLower.norm_lower' n β hβ0) (Real.exp_pos _).le)

/-! ### The theorem -/

/-- **The valley gap bounds the neutral sector.** Conditional on `ValleyGap`. Here `σ` is any level at
most `1/(16 n⁴)`, `ε ‖T‖` bounds `offError`, `r` is a trial value of the valley form, and `τ` is the target
contraction. The conclusion is the first half of `NeutralWindow` with `ρ₁ = τ`. The bound `hoff` is proved at
`σ = 1/(16 n⁴)` by `offError_le_norm` and at smaller levels by `offError_le_of_budget`. -/
theorem neutral_contraction_general (hβ0 : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (ε τ : ℝ)
    (hε : ε ≤ τ) (hoff : offError n β σ ≤ ε * ‖T‖) (ρ r : ℝ) (hρ : 0 ≤ ρ) (ψ : C(Slice n, ℝ))
    (H : ValleyGap n β σ ρ ψ) (t : C(Slice n, ℝ)) (htn : ∀ u, 0 ≤ t u) (htne : ∃ u, t u ≠ 0)
    (htr : r * ∫ u, t u ^ 2 ∂μ' ≤ valleyForm n β σ t) (hgap : ρ ≤ (τ - ε) * r) :
    ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω ∧ Neutral n Ω ∧
      ∀ f, Neutral n f → inner ℂ Ω f = 0 → ‖T f‖ ≤ τ * ‖T‖ * ‖f‖ := by
  obtain ⟨Ω, hΩ1, hΩ2, hΩ3, hunique⟩ := neutral_vacuum n β hβ0
  obtain ⟨η, hη, hnormL, heig⟩ := exists_positive_top n β hβ0
  refine ⟨Ω, hΩ1, hΩ2, hΩ3, fun f hf hf' => ?_⟩
  -- transport orthogonality to the positive representative
  set Ω' := ContinuousMap.toLp 2 (μ') ℂ (complexify η) with hΩ'
  have hTΩ' : T Ω' = ‖T‖ • Ω' := by
    rw [hΩ', transfer_embed]
    have hs : sm n β η = ‖T‖ • η := by
      ext u
      rw [sm_apply, heig]
      rfl
    rw [hs, WilsonPositiveGroundState.complexify_smul, map_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  obtain ⟨z, hz⟩ := hunique Ω' hTΩ'
  have horth : inner ℂ Ω' f = 0 := by
    rw [hz, inner_smul_left, hf', mul_zero]
  have hmain := neutral_contraction_of_valley n β hβ0 σ hσ ρ hρ ψ H η hη heig f hf horth
  have hr : r ≤ ‖T‖ := by
    have hpos := sq_integral_pos n t htne
    have h1 := valleyForm_le_norm n β σ t htn
    exact le_of_mul_le_mul_right (htr.trans h1) hpos
  have hρle : ρ ≤ (τ - ε) * ‖T‖ :=
    hgap.trans (mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hε))
  have hfin : ρ + offError n β σ ≤ τ * ‖T‖ := by
    nlinarith only [hρle, hoff]
  exact hmain.trans (mul_le_mul_of_nonneg_right hfin (norm_nonneg f))

/-- **Milestone A₀, reduced to the valley.** Conditional, on `ValleyGap` at the open size. Suppose `β ≥ A n⁸`. If
the valley form at level `1/(16 n⁴)` has a gap `ρ` against a trial value `r` of the same form, with `ρ` at most
`(exp(-c/n) - exp(-n⁴)) r`, then `T` contracts the neutral complement of the vacuum by `exp(-c/n)`,
which is the first half of `NeutralWindow`. Here `c` is a parameter of one instance: it is not assumed positive, and
nothing is claimed uniformly in `n`. By `valleyGap_of_contraction` the hypothesis with `ψ = η` is essentially
equivalent to the conclusion. -/
theorem neutral_contraction_A0 (hβ : threshold * (n : ℝ) ^ 8 ≤ β) (c : ℝ)
    (hc : Real.exp (-(n : ℝ) ^ 4) ≤ Real.exp (-c / n)) (ρ r : ℝ) (hρ : 0 ≤ ρ)
    (ψ : C(Slice n, ℝ)) (H : ValleyGap n β (1 / (16 * (n : ℝ) ^ 4)) ρ ψ) (t : C(Slice n, ℝ))
    (htn : ∀ u, 0 ≤ t u) (htne : ∃ u, t u ≠ 0)
    (htr : r * ∫ u, t u ^ 2 ∂μ' ≤ valleyForm n β (1 / (16 * (n : ℝ) ^ 4)) t)
    (hgap : ρ ≤ (Real.exp (-c / n) - Real.exp (-(n : ℝ) ^ 4)) * r) :
    ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω ∧ Neutral n Ω ∧
      ∀ f, Neutral n f → inner ℂ Ω f = 0 → ‖T f‖ ≤ Real.exp (-c / n) * ‖T‖ * ‖f‖ := by
  have hβ0 : 0 ≤ β := by
    have := threshold_pos
    have h8 : (0 : ℝ) ≤ (n : ℝ) ^ 8 := by positivity
    have := mul_nonneg this.le h8
    linarith only [this, hβ]
  exact neutral_contraction_general n β hβ0 _ le_rfl _ _ hc (offError_le_norm n β hβ) ρ r hρ ψ H t htn
    htne htr hgap

/-! ### Comparison potentials -/

/-- **Monotonicity in the potential.** Replacing the weight `w` on the valley by a larger invariant weight
`wc` can only raise every level of the compressed form: a gap for `wc K₀ wc` is a gap for `w K₀ w`, with the
same `ρ` and a constraint adjusted by `w/wc`. So in `ValleyGap` the potential may be replaced by any
invariant lower bound on the valley. This bounds the excited level only. To use the output, `ρ` must still lie below
`(τ - ε) r` for a trial value `r` of the true form, and raising the weight by `e^x` raises the comparison levels by up to
`e^{2x}`. So the whole argument still needs `wc` close to `w` at relative accuracy about `1/n`, on both sides. -/
theorem valleyGap_of_lower_weight (hβ : 0 ≤ β) (σ ρ : ℝ) (hρ : 0 ≤ ρ) (wc ψc : C(Slice n, ℝ))
    (hwc : ∀ u, 0 < wc u) (hwcinv : Invariant n wc)
    (hle : ∀ u ∈ valley n σ, wt n β u ≤ wc u)
    (H : ∀ h, Invariant n h → ∫ u in valley n σ, h u * ψc u ∂μ' = 0 →
      ∫ u in valley n σ, ∫ v in valley n σ, (wc u * h u) * kinW n β u v * (wc v * h v) ∂μ' ∂μ' ≤
        ρ * ∫ u in valley n σ, h u ^ 2 ∂μ')
    (ψ : C(Slice n, ℝ)) (hψ : ∀ u, ψ u = wt n β u / wc u * ψc u) : ValleyGap n β σ ρ ψ := by
  intro h hh hmean
  let h' : C(Slice n, ℝ) := ⟨fun u => wt n β u / wc u * h u,
    ((wt_continuous n β).div wc.continuous fun u => (hwc u).ne').mul h.continuous⟩
  have hv (u : Slice n) : h' u = wt n β u / wc u * h u := rfl
  have hwt_flip (i : Fin 3) (c : ZMod n) (u : Slice n) :
      wt n β (TwistedTransfer.flip n i c u) = wt n β u := by
    unfold wt
    rw [twistedPotential_flip]
  have hinv' : Invariant n h' :=
    { gauge := fun k u => by rw [hv, hv, wt_gauge, hwcinv.gauge, hh.gauge]
      flip := fun i c u => by rw [hv, hv, hwt_flip, hwcinv.flip, hh.flip] }
  have hmean' : ∫ u in valley n σ, h' u * ψc u ∂μ' = 0 := by
    rw [← hmean]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hv, hψ]
    ring
  have hb := H h' hinv' hmean'
  have hw (u : Slice n) : wc u * h' u = wt n β u * h u := by
    rw [hv]
    field_simp [(hwc u).ne']
  simp only [hw] at hb
  rw [valleyForm_kinetic n β hβ σ h hh.gauge]
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hρ)
  refine setIntegral_mono_on (ci n (h'.continuous.pow 2)).integrableOn
    (ci n (h.continuous.pow 2)).integrableOn (valley_open n σ).measurableSet fun u hu => ?_
  rw [hv]
  have hr0 : 0 ≤ wt n β u / wc u := (div_pos (wt_pos n β u) (hwc u)).le
  have hr1 : wt n β u / wc u ≤ 1 := (div_le_one (hwc u)).mpr (hle u hu)
  have hsq : (wt n β u / wc u) ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  have h0 := sq_nonneg (h u)
  rw [mul_pow]
  nlinarith only [hsq, h0]

/-- **The kinetic kernel commutes exactly with left translations of the links.** So `K₀` commutes with the
flows `U ↦ exp(tX)·U` used in `TwistedHessianField`, with no error at any field. This is the identity a
ladder or Bochner argument would start from. -/
theorem kinW_left (u v : Slice n) (g : SpatialVertex n × Fin 3 → Q) :
    kinW n β (fun e => g e * u e) (fun e => g e * v e) = kinW n β u v := by
  unfold kinW kineticAction
  congr 2
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 3
  group

/-! ### The valley gap below `‖T‖` at each fixed cutoff -/

/-- The ground state's own local eigenvalue on the valley is at most `‖T‖`. -/
theorem collatz_eta (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (σ : ℝ) (u : Slice n) :
    ∫ v in valley n σ, twistedKernel n β (u, v) * η v ∂μ' ≤ ‖T‖ * η u := by
  rw [← heig u]
  have hK : Continuous fun v => twistedKernel n β (u, v) * η v :=
    ((twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)).mul η.continuous
  exact setIntegral_le_integral (ci n hK) (Filter.Eventually.of_forall fun v =>
    (mul_pos (twistedKernel_pos n β (u, v)) (hη v)).le)

/-- **A valley Poincaré inequality, from the worst-case kernel.** For the ground state itself, with
`m₀` a lower bound on its mass on the valley. Exponentially far from the constant `n` that is needed. -/
theorem valleyPoincare_explicit (hβ : 0 ≤ β) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (σ m₀ : ℝ) (hm₀ : 0 < m₀)
    (hm : m₀ ≤ ∫ u in valley n σ, η u ^ 2 ∂μ') :
    ValleyPoincare n β σ η ‖T‖ (Real.exp (72 * β * (n : ℝ) ^ 3) / m₀) := by
  intro g _ hmean
  obtain ⟨hk, hT1⟩ := norm_bounds n β hβ
  set k := Real.exp (-(24 * β * (n : ℝ) ^ 3)) with hkd
  have hkpos : 0 < k := Real.exp_pos _
  have hlam : 0 < ‖T‖ := hkpos.trans_le hk
  have hkη (u : Slice n) : k * η u ^ 2 ≤ η u := by
    have h1 := eta_le n β hβ η hη hnorm heig hlam u
    have h2 : η u ≤ 1 / k :=
      h1.trans (div_le_div₀ zero_le_one (wt_le_one n β hβ u) hkpos hk)
    have h4 : k * η u ≤ 1 := by
      rw [le_div_iff₀ hkpos] at h2
      linarith only [h2]
    nlinarith only [mul_le_mul_of_nonneg_right h4 (hη u).le]
  set V := valley n σ with hV
  have hVm : MeasurableSet V := (valley_open n σ).measurableSet
  set X := ∫ u in V, g u ^ 2 * η u ^ 2 ∂μ' with hX
  set m := ∫ u in V, η u ^ 2 ∂μ' with hmd
  have hX0 : 0 ≤ X := integral_nonneg fun u => by positivity
  have hcon {F : Slice n → ℝ} (hF : Continuous F) : IntegrableOn F V μ' := (ci n hF).integrableOn
  -- the inner integral, for `u` fixed
  have hinner (u : Slice n) : ∫ v in V, η v ^ 2 * (g u - g v) ^ 2 ∂μ' = g u ^ 2 * m + X := by
    have e : ∀ v, η v ^ 2 * (g u - g v) ^ 2 =
        (g u ^ 2) * η v ^ 2 - (2 * g u) * (g v * η v ^ 2) + g v ^ 2 * η v ^ 2 := fun v => by ring
    simp only [e]
    have i1 : IntegrableOn (fun v => g u ^ 2 * η v ^ 2) V μ' :=
      hcon (continuous_const.mul (η.continuous.pow 2))
    have i2 : IntegrableOn (fun v => 2 * g u * (g v * η v ^ 2)) V μ' :=
      hcon (continuous_const.mul (g.continuous.mul (η.continuous.pow 2)))
    have i3 : IntegrableOn (fun v => g v ^ 2 * η v ^ 2) V μ' :=
      hcon ((g.continuous.pow 2).mul (η.continuous.pow 2))
    rw [integral_sub_add' _ i1 i2 i3, integral_const_mul, integral_const_mul, hmean]
    ring
  -- the pointwise comparison
  have hin (u : Slice n) : k ^ 3 * (η u ^ 2 * (g u ^ 2 * m + X)) ≤
      ∫ v in V, η u * twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ' := by
    have hK : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    have hmono : ∫ v in V, k ^ 3 * (η u ^ 2 * (η v ^ 2 * (g u - g v) ^ 2)) ∂μ' ≤
        ∫ v in V, η u * twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ' := by
      refine setIntegral_mono_on
        (hcon (continuous_const.mul (continuous_const.mul ((η.continuous.pow 2).mul
          ((continuous_const.sub g.continuous).pow 2)))))
        (hcon (((continuous_const.mul hK).mul η.continuous).mul
          ((continuous_const.sub g.continuous).pow 2))) hVm fun v _ => ?_
      have h2 := kernel_ge n β hβ u v
      have h3 := hkη v
      have h4 := hkη u
      have hsq := sq_nonneg (g u - g v)
      have h5 : k * η u ^ 2 * (k * (k * η v ^ 2)) ≤ η u * (twistedKernel n β (u, v) * η v) := by
        refine mul_le_mul h4 ?_ (by positivity) (hη u).le
        exact mul_le_mul h2 h3 (by positivity) (twistedKernel_pos n β (u, v)).le
      have h6 := mul_le_mul_of_nonneg_right h5 hsq
      calc _ = k * η u ^ 2 * (k * (k * η v ^ 2)) * (g u - g v) ^ 2 := by ring
        _ ≤ _ := h6
        _ = _ := by ring
    have hcomp : ∫ v in V, k ^ 3 * (η u ^ 2 * (η v ^ 2 * (g u - g v) ^ 2)) ∂μ' =
        k ^ 3 * (η u ^ 2 * (g u ^ 2 * m + X)) := by
      rw [integral_const_mul, integral_const_mul, hinner]
    rwa [hcomp] at hmono
  have hF : Continuous fun u => ∫ v in V, η u * twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ' := by
    have hf : Continuous (Function.uncurry fun (u v : Slice n) =>
        η u * twistedKernel n β (u, v) * η v * (g u - g v) ^ 2) :=
      (((η.continuous.comp continuous_fst).mul (twistedKernel n β).continuous).mul
        (η.continuous.comp continuous_snd)).mul
        (((g.continuous.comp continuous_fst).sub (g.continuous.comp continuous_snd)).pow 2)
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := (μ').restrict V) hf isCompact_univ)
  have hmono : ∫ u in V, k ^ 3 * (η u ^ 2 * (g u ^ 2 * m + X)) ∂μ' ≤ valleyDirichlet n β σ η g :=
    setIntegral_mono_on (hcon (continuous_const.mul ((η.continuous.pow 2).mul
      (((g.continuous.pow 2).mul continuous_const).add continuous_const)))) (hcon hF) hVm fun u _ => hin u
  have hleft : ∫ u in V, k ^ 3 * (η u ^ 2 * (g u ^ 2 * m + X)) ∂μ' = k ^ 3 * (2 * (m * X)) := by
    rw [integral_const_mul]
    congr 1
    have e : ∀ u, η u ^ 2 * (g u ^ 2 * m + X) = m * (g u ^ 2 * η u ^ 2) + X * η u ^ 2 := fun u => by ring
    simp only [e]
    have i1 : IntegrableOn (fun u => m * (g u ^ 2 * η u ^ 2)) V μ' :=
      hcon (continuous_const.mul ((g.continuous.pow 2).mul (η.continuous.pow 2)))
    have i2 : IntegrableOn (fun u => X * η u ^ 2) V μ' := hcon (continuous_const.mul (η.continuous.pow 2))
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
    ring
  rw [hleft] at hmono
  have hC : Real.exp (72 * β * (n : ℝ) ^ 3) * k ^ 3 = 1 := by
    rw [hkd, ← Real.exp_nat_mul, ← Real.exp_add]
    have e : 72 * β * (n : ℝ) ^ 3 + ((3 : ℕ) : ℝ) * -(24 * β * (n : ℝ) ^ 3) = 0 := by
      push_cast
      ring
    rw [e, Real.exp_zero]
  have hCpos := Real.exp_pos (72 * β * (n : ℝ) ^ 3)
  have hmono2 := mul_le_mul_of_nonneg_left hmono hCpos.le
  have h2 : Real.exp (72 * β * (n : ℝ) ^ 3) * (k ^ 3 * (2 * (m * X))) = 2 * (m * X) := by
    rw [← mul_assoc, hC, one_mul]
  rw [h2] at hmono2
  have hm0X : m₀ * X ≤ m * X := mul_le_mul_of_nonneg_right hm hX0
  have h3 : 2 * ‖T‖ * X ≤ 2 * X := by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0]
  have h4 : m₀ * (2 * ‖T‖ * X) ≤ Real.exp (72 * β * (n : ℝ) ^ 3) * valleyDirichlet n β σ η g := by
    nlinarith only [mul_le_mul_of_nonneg_left h3 hm₀.le, hm0X, hmono2]
  rw [div_mul_eq_mul_div, le_div_iff₀ hm₀]
  linarith only [h4]

/-- **`ValleyGap` below `‖T‖` holds at every cutoff.** With `ψ = η` and any lower bound `m₀` on the valley
mass of `η`, the level is `‖T‖ (1 - m₀ exp(-72 β n³))`. This is the fixed-`n` statement: the only hard
content of `ValleyGap` is the size `exp(-c/n) ‖T‖`, uniformly in `n`. The ground state appears in `ψ`,
so this is not an explicit trial function. -/
theorem valleyGap_explicit (hβ : 0 ≤ β) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (σ m₀ : ℝ) (hm₀ : 0 < m₀)
    (hm : m₀ ≤ ∫ u in valley n σ, η u ^ 2 ∂μ') :
    ValleyGap n β σ (‖T‖ * (1 - m₀ * Real.exp (-(72 * β * (n : ℝ) ^ 3)))) η := by
  have hC : 0 < Real.exp (72 * β * (n : ℝ) ^ 3) / m₀ := div_pos (Real.exp_pos _) hm₀
  have h := valleyGap_of_trial n β σ η hη (eta_invariant n β hβ η hη heig) ‖T‖ _ hC
    (fun u _ => collatz_eta n β η hη heig σ u)
    (valleyPoincare_explicit n β hβ η hη hnorm heig σ m₀ hm₀ hm)
  have e : 1 - 1 / (Real.exp (72 * β * (n : ℝ) ^ 3) / m₀) = 1 - m₀ * Real.exp (-(72 * β * (n : ℝ) ^ 3)) := by
    rw [one_div_div, Real.exp_neg]
    field_simp
  rwa [e] at h


theorem setIntegral_mirror (σ : ℝ) (a : Slice n → ℝ) :
    ∫ u in mirror n σ, a u ∂μ' = ∫ u in valley n σ, a (TwistedTransfer.flip n 2 0 u) ∂μ' := by
  have hmp : MeasurePreserving (flipEquiv n 2 0) (μ') (μ') := flip_measurePreserving n 2 0
  have := hmp.setIntegral_preimage_emb (flipEquiv n 2 0).measurableEmbedding a (mirror n σ)
  rw [← this]
  have hpre : (flipEquiv n 2 0) ⁻¹' mirror n σ = valley n σ := by
    ext u
    exact flip_mem_mirror n σ u
  rw [hpre]
  rfl

theorem mean_abs_sq_le (V : Set (Slice n)) (h : C(Slice n, ℝ)) :
    (∫ v in V, |h v| ∂μ') ^ 2 ≤ ∫ v in V, h v ^ 2 ∂μ' := by
  set a := ∫ v in V, |h v| ∂μ' with ha
  set A := ∫ v in V, h v ^ 2 ∂μ' with hA
  have ha0 : 0 ≤ a := integral_nonneg fun v => abs_nonneg _
  have hc {F : Slice n → ℝ} (hF : Continuous F) : IntegrableOn F V μ' := (ci n hF).integrableOn
  have h0 : 0 ≤ ∫ v in V, (|h v| - a) ^ 2 ∂μ' := integral_nonneg fun v => sq_nonneg _
  have e : ∀ v, (|h v| - a) ^ 2 = h v ^ 2 - (2 * a) * |h v| + a ^ 2 := fun v => by
    have := sq_abs (h v)
    nlinarith only [this]
  simp only [e] at h0
  have i1 : IntegrableOn (fun v => h v ^ 2) V μ' := hc (h.continuous.pow 2)
  have i2 : IntegrableOn (fun v => 2 * a * |h v|) V μ' := hc (continuous_const.mul h.continuous.abs)
  have i3 : IntegrableOn (fun _ : Slice n => a ^ 2) V μ' := hc continuous_const
  rw [integral_sub_add' _ i1 i2 i3, integral_const_mul, setIntegral_const, smul_eq_mul, ← ha, ← hA] at h0
  have hreal : (μ').real V ≤ 1 := measureReal_le_one
  nlinarith only [h0, hreal, sq_nonneg a]

/-- The real function underlying the test vector: `h` on the two valleys, zero elsewhere. -/
def cutoff (σ : ℝ) (h : C(Slice n, ℝ)) : Slice n → ℝ := (valley n σ ∪ mirror n σ).indicator h

theorem cutoff_mem (σ : ℝ) (h : C(Slice n, ℝ)) {u : Slice n} (hu : u ∈ valley n σ ∪ mirror n σ) :
    cutoff n σ h u = h u := Set.indicator_of_mem hu _

theorem cutoff_not (σ : ℝ) (h : C(Slice n, ℝ)) {u : Slice n} (hu : u ∉ valley n σ ∪ mirror n σ) :
    cutoff n σ h u = 0 := Set.indicator_of_notMem hu _

theorem union_eq (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) :
    valley n σ ∪ mirror n σ = {u | twistedPotential n u < σ} := by
  ext u
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    have hs := holo_sq_of_small n u (lt_of_lt_of_le h hσ)
    rcases lt_trichotomy (holo n u) 0 with h' | h' | h'
    · exact Or.inr ⟨h, h'⟩
    · rw [h'] at hs
      norm_num at hs
    · exact Or.inl ⟨h, h'⟩

/-- **The transfer form of a cut-off even function.** The form of `h` restricted to the two valleys is
twice the valley form plus a cross term, and the cross term is bounded by `offError`. -/
theorem cutoff_form (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (h : C(Slice n, ℝ))
    (hflip : ∀ u, h (TwistedTransfer.flip n 2 0 u) = h u) :
    2 * valleyForm n β σ h - 2 * (offError n β σ * ∫ u in valley n σ, h u ^ 2 ∂μ') ≤
      ∫ u, cutoff n σ h u * ∫ v, twistedKernel n β (u, v) * cutoff n σ h v ∂μ' ∂μ' := by
  set V := valley n σ with hV
  set W := mirror n σ with hW
  have hVm : MeasurableSet V := (valley_open n σ).measurableSet
  have hWm : MeasurableSet W := (mirror_open n σ).measurableSet
  have hdis : Disjoint V W := valley_disjoint n σ
  have hUm : MeasurableSet (V ∪ W) := hVm.union hWm
  let sV : C(Slice n, ℝ) := smoothOn (n := n) (β := β) ((μ').restrict V) h
  let sW : C(Slice n, ℝ) := smoothOn (n := n) (β := β) ((μ').restrict W) h
  have hsV (u : Slice n) : sV u = ∫ v in V, twistedKernel n β (u, v) * h v ∂μ' := rfl
  have hsW (u : Slice n) : sW u = ∫ v in W, twistedKernel n β (u, v) * h v ∂μ' := rfl
  have hc {F : Slice n → ℝ} {S : Set (Slice n)} (hF : Continuous F) : IntegrableOn F S μ' :=
    (ci n hF).integrableOn
  -- the row integral
  have hrow (u : Slice n) : ∫ v, twistedKernel n β (u, v) * cutoff n σ h v ∂μ' = sV u + sW u := by
    have hK : Continuous fun v => twistedKernel n β (u, v) * h v :=
      ((twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)).mul h.continuous
    have e : (fun v => twistedKernel n β (u, v) * cutoff n σ h v) =
        (V ∪ W).indicator fun v => twistedKernel n β (u, v) * h v := by
      funext v
      by_cases hv : v ∈ V ∪ W
      · rw [Set.indicator_of_mem hv, cutoff_mem n σ h hv]
      · rw [Set.indicator_of_notMem hv, cutoff_not n σ h hv, mul_zero]
    rw [e, integral_indicator hUm, setIntegral_union hdis hWm (hc hK) (hc hK), hsV, hsW]
  have hout : ∫ u, cutoff n σ h u * ∫ v, twistedKernel n β (u, v) * cutoff n σ h v ∂μ' ∂μ' =
      ∫ u in V ∪ W, h u * (sV u + sW u) ∂μ' := by
    simp only [hrow]
    have e : (fun u => cutoff n σ h u * (sV u + sW u)) =
        (V ∪ W).indicator fun u => h u * (sV u + sW u) := by
      funext u
      by_cases hu : u ∈ V ∪ W
      · rw [Set.indicator_of_mem hu, cutoff_mem n σ h hu]
      · rw [Set.indicator_of_notMem hu, cutoff_not n σ h hu, zero_mul]
    rw [e, integral_indicator hUm]
  have hcon1 : Continuous fun u => h u * (sV u + sW u) :=
    h.continuous.mul (sV.continuous.add sW.continuous)
  rw [hout, setIntegral_union hdis hWm (hc hcon1) (hc hcon1)]
  -- mirror symmetry of the two smoothings
  have hswap (u : Slice n) : sW (TwistedTransfer.flip n 2 0 u) = sV u := by
    rw [hsW, hsV, setIntegral_mirror]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [twistedKernel_flip, hflip]
  have hswap' (u : Slice n) : sV (TwistedTransfer.flip n 2 0 u) = sW u := by
    have := hswap (TwistedTransfer.flip n 2 0 u)
    rwa [TwistedTransfer.flip_flip, eq_comm] at this
  have hW2 : ∫ u in W, h u * (sV u + sW u) ∂μ' = ∫ u in V, h u * (sV u + sW u) ∂μ' := by
    rw [setIntegral_mirror]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hflip, hswap, hswap']
    ring
  rw [hW2]
  have i1 : IntegrableOn (fun u => h u * sV u) V μ' := hc (h.continuous.mul sV.continuous)
  have i2 : IntegrableOn (fun u => h u * sW u) V μ' := hc (h.continuous.mul sW.continuous)
  have hsplit : ∫ u in V, h u * (sV u + sW u) ∂μ' = ∫ u in V, h u * sV u ∂μ' + ∫ u in V, h u * sW u ∂μ' := by
    simp only [mul_add]
    exact integral_add i1 i2
  have hform : ∫ u in V, h u * sV u ∂μ' = valleyForm n β σ h := by
    unfold valleyForm
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hsV, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    ring
  -- the cross term
  set a := ∫ v in V, |h v| ∂μ' with ha
  have ha0 : 0 ≤ a := integral_nonneg fun v => abs_nonneg _
  have haW : ∫ v in W, |h v| ∂μ' = a := by
    rw [setIntegral_mirror]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [hflip]
  have hoff0 := (offError_pos n β σ).le
  have hcross (u : Slice n) (hu : u ∈ V) : -(|h u| * (offError n β σ * a)) ≤ h u * sW u := by
    have hK : Continuous fun v => twistedKernel n β (u, v) * h v :=
      ((twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)).mul h.continuous
    have hb : |sW u| ≤ offError n β σ * a := by
      rw [hsW, ← haW, ← integral_const_mul]
      refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on (hc hK.abs)
        (hc (continuous_const.mul h.continuous.abs)) hWm fun v hv => ?_)
      rw [abs_mul, abs_of_pos (twistedKernel_pos n β (u, v))]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine kernel_off n β hβ σ hσ u v ?_ ?_
      · rintro ⟨-, hv'⟩
        exact Set.disjoint_left.mp hdis hv' hv
      · rintro ⟨hu', -⟩
        exact Set.disjoint_left.mp hdis hu hu'
    have h1 := abs_mul (h u) (sW u)
    have h2 := neg_abs_le (h u * sW u)
    have h3 := mul_le_mul_of_nonneg_left hb (abs_nonneg (h u))
    linarith only [h1, h2, h3]
  have hcrossI : -(a * (offError n β σ * a)) ≤ ∫ u in V, h u * sW u ∂μ' := by
    have hL : IntegrableOn (fun u => -(|h u| * (offError n β σ * a))) V μ' :=
      hc (h.continuous.abs.mul continuous_const).neg
    have hm := setIntegral_mono_on hL i2 hVm hcross
    have e : ∫ u in V, -(|h u| * (offError n β σ * a)) ∂μ' = -(a * (offError n β σ * a)) := by
      rw [integral_neg, integral_mul_const]
    rwa [e] at hm
  have hsq := mean_abs_sq_le n V h
  rw [← ha] at hsq
  have hfin := mul_le_mul_of_nonneg_left hsq hoff0
  rw [hsplit, hform]
  nlinarith only [hcrossI, hfin]

/-- **A contraction gives the valley gap.** With `ψ = η`. This is the converse of
`neutral_contraction_of_valley`. Together they show that `ValleyGap` against the ground state is the neutral gap
with error `offError`, in both directions. So reducing the gap to `ValleyGap` removes the far field and tunneling
and nothing else. -/
theorem valleyGap_of_contraction (hβ : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4))
    (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (B : ℝ)
    (hB : ∀ f, Neutral n f → inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 → ‖T f‖ ≤ B * ‖f‖) :
    ValleyGap n β σ (B + offError n β σ) η := by
  intro h hh hmean
  have hηinv := eta_invariant n β hβ η hη heig
  set V := valley n σ with hV
  set W := mirror n σ with hW
  have hVm : MeasurableSet V := (valley_open n σ).measurableSet
  have hWm : MeasurableSet W := (mirror_open n σ).measurableSet
  have hdis : Disjoint V W := valley_disjoint n σ
  have hUm : MeasurableSet (V ∪ W) := hVm.union hWm
  set r := cutoff n σ h with hr
  have hrm : Measurable r := h.continuous.measurable.indicator hUm
  have hF0 : MemLp (fun u => (r u : ℂ)) 2 (μ') := by
    have h1 : MemLp (fun u => ((h u : ℝ) : ℂ)) 2 (μ') :=
      (Continuous.memLp_of_hasCompactSupport (Complex.continuous_ofReal.comp h.continuous)
        (HasCompactSupport.of_compactSpace _))
    have h2 := h1.indicator hUm
    have e : (V ∪ W).indicator (fun u => ((h u : ℝ) : ℂ)) = fun u => (r u : ℂ) := by
      funext u
      by_cases hu : u ∈ V ∪ W
      · rw [Set.indicator_of_mem hu, hr, cutoff_mem n σ h hu]
      · rw [Set.indicator_of_notMem hu, hr, cutoff_not n σ h hu, Complex.ofReal_zero]
    rwa [e] at h2
  let F : Hilbert n := hF0.toLp
  have hFae : F =ᵐ[μ'] fun u => (r u : ℂ) := MemLp.coeFn_toLp _
  -- neutrality
  have hneut : Neutral n F := by
    intro i c
    apply Lp.ext
    have h1 : (flipOp n i c F : Slice n → ℂ) =ᵐ[μ'] (F ∘ TwistedTransfer.flip n i c) :=
      Lp.coeFn_compMeasurePreserving _ (flip_measurePreserving n i c)
    have h2 := (flip_measurePreserving n i c).quasiMeasurePreserving.ae_eq_comp hFae
    refine h1.trans (h2.trans (Filter.EventuallyEq.trans ?_ hFae.symm))
    refine Filter.Eventually.of_forall fun u => ?_
    simp only [Function.comp, hr]
    have hmem : TwistedTransfer.flip n i c u ∈ V ∪ W ↔ u ∈ V ∪ W := by
      rw [hV, hW, union_eq n σ hσ]
      simp only [Set.mem_setOf_eq, twistedPotential_flip]
    by_cases hu : u ∈ V ∪ W
    · rw [cutoff_mem n σ h hu, cutoff_mem n σ h (hmem.mpr hu), hh.flip]
    · rw [cutoff_not n σ h hu, cutoff_not n σ h (fun hc => hu (hmem.mp hc))]
  have hflip2 (u : Slice n) := hh.flip 2 0 u
  -- orthogonality
  have horth : inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) F = 0 := by
    have hΩ := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') (complexify η)
    rw [L2.inner_def]
    have e : ∫ a, inner ℂ ((ContinuousMap.toLp 2 (μ') ℂ (complexify η)) a) (F a) ∂μ' =
        ((∫ u, η u * r u ∂μ' : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [hΩ, hFae] with a h₁ h₂
      rw [h₁, h₂]
      simp [complexify, mul_comm]
    rw [e]
    have hzero : ∫ u, η u * r u ∂μ' = 0 := by
      have ee : (fun u => η u * r u) = (V ∪ W).indicator fun u => h u * η u := by
        funext u
        by_cases hu : u ∈ V ∪ W
        · rw [Set.indicator_of_mem hu, hr, cutoff_mem n σ h hu, mul_comm]
        · rw [Set.indicator_of_notMem hu, hr, cutoff_not n σ h hu, mul_zero]
      have hc : Continuous fun u => h u * η u := h.continuous.mul η.continuous
      rw [ee, integral_indicator hUm, setIntegral_union hdis hWm (ci n hc).integrableOn
        (ci n hc).integrableOn, hmean]
      rw [hW, setIntegral_mirror]
      have : ∫ u in valley n σ, h (TwistedTransfer.flip n 2 0 u) * η (TwistedTransfer.flip n 2 0 u) ∂μ' =
          ∫ u in valley n σ, h u * η u ∂μ' := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [hflip2, hηinv.flip]
      rw [this]
      rw [← hV, hmean]
      simp
    rw [hzero]
    simp
  have hTF := hB F hneut horth
  -- the squared norm
  set A := ∫ u in V, h u ^ 2 ∂μ' with hA
  have hFsq : ‖F‖ ^ 2 = 2 * A := by
    have hs := sq_norm_eq F
    have hi : ∫ x, ‖F x‖ ^ 2 ∂μ' = ∫ u, r u ^ 2 ∂μ' := by
      refine integral_congr_ae ?_
      filter_upwards [hFae] with a h₁
      rw [h₁]
      simp
    have hc : Continuous fun u => h u ^ 2 := h.continuous.pow 2
    have ee : (fun u => r u ^ 2) = (V ∪ W).indicator fun u => h u ^ 2 := by
      funext u
      by_cases hu : u ∈ V ∪ W
      · rw [Set.indicator_of_mem hu, hr, cutoff_mem n σ h hu]
      · rw [Set.indicator_of_notMem hu, hr, cutoff_not n σ h hu]
        simp
    rw [← hs, hi, ee, integral_indicator hUm, setIntegral_union hdis hWm (ci n hc).integrableOn
      (ci n hc).integrableOn, hW, setIntegral_mirror]
    have : ∫ u in valley n σ, h (TwistedTransfer.flip n 2 0 u) ^ 2 ∂μ' = A := by
      rw [hA, hV]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [hflip2]
    rw [this, ← hA]
    ring
  -- the inner product
  have hTae := CompactKernelOperator.operator_integral (μ') (twistedKernel n β) F
  have hrow (x : Slice n) : ∫ y, ((twistedKernel n β (x, y) : ℝ) : ℂ) * F y ∂μ' =
      ((∫ y, twistedKernel n β (x, y) * r y ∂μ' : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hFae] with a h₁
    rw [h₁]
    push_cast
    rfl
  have hinner : inner ℂ F (T F) = ((∫ u, r u * ∫ v, twistedKernel n β (u, v) * r v ∂μ' ∂μ' : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hFae, hTae] with a h₁ h₂
    have h₂' : (T F : Slice n → ℂ) a = _ := h₂
    rw [h₂', hrow, h₁]
    simp [mul_comm]
  have hcf := cutoff_form n β hβ σ hσ h hflip2
  have h1 := norm_inner_le_norm (𝕜 := ℂ) F (T F)
  rw [hinner, Complex.norm_real, Real.norm_eq_abs] at h1
  have hup : ∫ u, r u * ∫ v, twistedKernel n β (u, v) * r v ∂μ' ∂μ' ≤ B * ‖F‖ ^ 2 := by
    calc _ ≤ _ := le_abs_self _
      _ ≤ ‖F‖ * ‖T F‖ := h1
      _ ≤ ‖F‖ * (B * ‖F‖) := mul_le_mul_of_nonneg_left hTF (norm_nonneg F)
      _ = _ := by ring
  rw [hFsq] at hup
  change 2 * valleyForm n β σ h - 2 * (offError n β σ * A) ≤ _ at hcf
  have hfin : 2 * valleyForm n β σ h ≤ 2 * ((B + offError n β σ) * A) := by
    nlinarith only [hcf, hup]
  linarith only [hfin]


/-- A flip-invariant continuous function embeds as a neutral vector. -/
theorem embed_neutral (a : C(Slice n, ℝ)) (ha : ∀ i c u, a (TwistedTransfer.flip n i c u) = a u) :
    Neutral n (ContinuousMap.toLp 2 (μ') ℂ (complexify a)) := by
  intro i c
  apply Lp.ext
  have h0 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') (complexify a)
  have h1 : (flipOp n i c (ContinuousMap.toLp 2 (μ') ℂ (complexify a)) : Slice n → ℂ) =ᵐ[μ']
      ((ContinuousMap.toLp 2 (μ') ℂ (complexify a) : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ (flip_measurePreserving n i c)
  have h2 := (flip_measurePreserving n i c).quasiMeasurePreserving.ae_eq_comp h0
  refine h1.trans (h2.trans (Filter.EventuallyEq.trans ?_ h0.symm))
  refine Filter.Eventually.of_forall fun u => ?_
  change ((a (TwistedTransfer.flip n i c u) : ℝ) : ℂ) = ((a u : ℝ) : ℂ)
  rw [ha]

/-- A Rayleigh lower bound on a continuous function gives a lower bound on the operator norm of its image. -/
theorem embed_lower (c : C(Slice n, ℝ)) (hne : ∃ u, c u ≠ 0) (m : ℝ)
    (hm : m * ∫ u, c u ^ 2 ∂μ' ≤ ∫ u, c u * (∫ v, twistedKernel n β (u, v) * c v ∂μ') ∂μ') :
    ContinuousMap.toLp 2 (μ') ℂ (complexify c) ≠ 0 ∧
      m * ‖ContinuousMap.toLp 2 (μ') ℂ (complexify c)‖ ≤ ‖T (ContinuousMap.toLp 2 (μ') ℂ (complexify c))‖ := by
  set F := ContinuousMap.toLp 2 (μ') ℂ (complexify c) with hF
  have hFsq : ‖F‖ ^ 2 = ∫ u, c u ^ 2 ∂μ' := by
    rw [hF, WilsonPositiveGroundState.real_embedding_norm_sq]
  have hpos : 0 < ‖F‖ ^ 2 := by
    rw [hFsq]
    exact sq_integral_pos n c hne
  have hFpos : 0 < ‖F‖ := by
    have h0 := norm_nonneg F
    rcases h0.eq_or_lt with h | h
    · rw [← h] at hpos
      norm_num at hpos
    · exact h
  refine ⟨norm_pos_iff.mp hFpos, ?_⟩
  have hinner : inner ℂ F (T F) = ((∫ u, c u * (∫ v, twistedKernel n β (u, v) * c v ∂μ') ∂μ' : ℝ) : ℂ) := by
    rw [hF, transfer_embed, inner_embed]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [sm_apply]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) F (T F)
  rw [hinner, Complex.norm_real, Real.norm_eq_abs] at h1
  have h2 : m * ‖F‖ ^ 2 ≤ ‖F‖ * ‖T F‖ := by
    rw [hFsq]
    exact hm.trans ((le_abs_self _).trans h1)
  have h3 : ‖F‖ * (m * ‖F‖) ≤ ‖F‖ * ‖T F‖ := by
    calc _ = m * ‖F‖ ^ 2 := by ring
      _ ≤ _ := h2
  exact le_of_mul_le_mul_left h3 hFpos

/-- **The second half of the window, from one observable.** An exact consequence of the ground-state identity:
a neutral observable `g` of mean zero under `η²` gives a neutral vector orthogonal to the vacuum whose image has
norm at least `(1 - D/(2 ‖T‖ X)) ‖T‖` times its own, with `X` the variance of `g` and `D` its Dirichlet form. The
open content is a lower bound on `X` for an observable with `D/(2 ‖T‖ X)` of size `1/n`. `holo` does not qualify:
it is flip-odd, and `holo² ≥ 1/2` on the valley gives no variance. -/
theorem second_half_of_observable (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u)
    (g : C(Slice n, ℝ)) (hg : NeutralObservable n η g) (hne : ∃ u, g u ≠ 0)
    (hlam : 0 < ‖T‖) (hflip : ∀ i c u, η (TwistedTransfer.flip n i c u) = η u) :
    ∃ f : Hilbert n, Neutral n f ∧ inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 ∧ f ≠ 0 ∧
      (1 - dirichlet n β η g / (2 * ‖T‖ * ∫ u, g u ^ 2 * η u ^ 2 ∂μ')) * ‖T‖ * ‖f‖ ≤ ‖T f‖ := by
  let c : C(Slice n, ℝ) := g * η
  have hc (u : Slice n) : c u = g u * η u := rfl
  have hne' : ∃ u, c u ≠ 0 := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, mul_ne_zero hu (hη u).ne'⟩
  have hid := ground_state_identity n β η g heig
  set X := ∫ u, g u ^ 2 * η u ^ 2 ∂μ' with hX
  have hXsq : ∫ u, c u ^ 2 ∂μ' = X := by
    rw [hX]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hc]
    ring
  have hXpos : 0 < X := by
    rw [← hXsq]
    exact sq_integral_pos n c hne'
  have hform : ∫ u, c u * (∫ v, twistedKernel n β (u, v) * c v ∂μ') ∂μ' = ‖T‖ * X - dirichlet n β η g / 2 := by
    have : ∫ u, (g u * η u) * (∫ v, twistedKernel n β (u, v) * (g v * η v) ∂μ') ∂μ' =
        ∫ u, c u * (∫ v, twistedKernel n β (u, v) * c v ∂μ') ∂μ' := rfl
    rw [this] at hid
    linarith only [hid]
  have hval : (1 - dirichlet n β η g / (2 * ‖T‖ * X)) * ‖T‖ * ∫ u, c u ^ 2 ∂μ' =
      ‖T‖ * X - dirichlet n β η g / 2 := by
    rw [hXsq]
    field_simp
  obtain ⟨h1, h2⟩ := embed_lower n β c hne' _ (by rw [hval, hform])
  refine ⟨_, embed_neutral n c fun i c' u => ?_, ?_, h1, h2⟩
  · rw [hc, hc, hg.flip, hflip]
  · rw [inner_embed]
    have : ∫ u, η u * c u ∂μ' = 0 := by
      rw [← hg.mean]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [hc]
      ring
    rw [this]
    simp

/-- **The second half of the window, from a plane of trial functions.** The bound `m` on a two-dimensional space of
flip-invariant trial functions gives a neutral vector orthogonal to the vacuum, by the choice of a suitable
combination. The ground state does not appear in the hypotheses. The open content is such a plane with
`m ≥ exp(-C/n) ‖T‖`, which needs the same relative accuracy as the first half. -/
theorem second_half_of_plane (η a b : C(Slice n, ℝ))
    (ha : ∀ i c u, a (TwistedTransfer.flip n i c u) = a u) (hb : ∀ i c u, b (TwistedTransfer.flip n i c u) = b u)
    (hind : ∀ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) → ∃ u, s * a u + t * b u ≠ 0) (m : ℝ)
    (hm : ∀ s t : ℝ, m * ∫ u, (s * a u + t * b u) ^ 2 ∂μ' ≤
      ∫ u, (s * a u + t * b u) * (∫ v, twistedKernel n β (u, v) * (s * a v + t * b v) ∂μ') ∂μ') :
    ∃ f : Hilbert n, Neutral n f ∧ inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 ∧ f ≠ 0 ∧
      m * ‖f‖ ≤ ‖T f‖ := by
  set p := ∫ u, η u * a u ∂μ' with hp
  set q := ∫ u, η u * b u ∂μ' with hq
  obtain ⟨s, t, hst, hzero⟩ : ∃ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) ∧ s * p + t * q = 0 := by
    by_cases h0 : p = 0 ∧ q = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by rw [h0.1, h0.2]; ring⟩
    · refine ⟨q, -p, ?_, by ring⟩
      by_cases hq0 : q = 0
      · refine Or.inr (neg_ne_zero.mpr fun hp0 => h0 ⟨hp0, hq0⟩)
      · exact Or.inl hq0
  let c : C(Slice n, ℝ) := ⟨fun u => s * a u + t * b u,
    (continuous_const.mul a.continuous).add (continuous_const.mul b.continuous)⟩
  have hc (u : Slice n) : c u = s * a u + t * b u := rfl
  obtain ⟨h1, h2⟩ := embed_lower n β c (hind s t hst) m (hm s t)
  refine ⟨_, embed_neutral n c fun i c' u => ?_, ?_, h1, h2⟩
  · rw [hc, hc, ha, hb]
  · rw [inner_embed]
    have e : ∫ u, η u * c u ∂μ' = s * p + t * q := by
      have i1 : Integrable (fun u => s * (η u * a u)) μ' :=
        ci n (continuous_const.mul (η.continuous.mul a.continuous))
      have i2 : Integrable (fun u => t * (η u * b u)) μ' :=
        ci n (continuous_const.mul (η.continuous.mul b.continuous))
      calc ∫ u, η u * c u ∂μ' = ∫ u, (s * (η u * a u) + t * (η u * b u)) ∂μ' := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
            dsimp only
            rw [hc]
            ring
        _ = s * p + t * q := by rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
    rw [e, hzero]
    simp

/-! ### The off-diagonal error on a smaller valley -/

/-- The exponent `offError` must beat on a valley of arbitrary level: `X` plus the logarithm of the lower bound
on `1/‖T‖` from `norm_lower'`. It grows like `n³ log β`, so the level can be about `n³ log β / β`. -/
def levelBudget (n : ℕ) (β X : ℝ) : ℝ :=
  1 + X + 7 * (n : ℝ) ^ 3 * Real.log (SU2GaussianMass.cap 1 * (24 * β) ^ 2)

/-- **The off-diagonal error at a general level.** `offError_le_norm` is the case `σ = 1/(16 n⁴)`. -/
theorem offError_le_of_budget (hβ : 1 / 24 ≤ β) (σ X : ℝ) (h1 : 2 * levelBudget n β X ≤ β * σ)
    (h2 : levelBudget n β X * n ≤ 2 * β) : offError n β σ ≤ Real.exp (-X) * ‖T‖ := by
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  set L := levelBudget n β X with hL
  have he₁ : Real.exp (-(2 * β / n)) ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    have : L ≤ 2 * β / n := by
      rw [le_div_iff₀ hnpos]
      exact h2
    linarith only [this]
  have he₂ : Real.exp (-(β * σ / 2)) ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    linarith only [h1]
  have hoff : offError n β σ ≤ 2 * Real.exp (-L) := by
    unfold offError
    linarith only [he₁, he₂]
  set K := SU2GaussianMass.cap 1 with hK
  have hKpos : 0 < K := cap_one_pos
  set Qv := K * (24 * β) ^ 2 with hQv
  have hβpos : 0 < 24 * β := by linarith only [hβ]
  have hQpos : 0 < Qv := by positivity
  have hmass : Qv⁻¹ ≤ SU2GaussianMass.mass (24 * β) := mass_lower_poly β hβ
  set m := 2 * TwistedNormLower.links n + TwistedNormLower.sites n with hm
  have hmv : (m : ℝ) = 7 * (n : ℝ) ^ 3 := by
    rw [hm, TwistedNormLower.links_eq, TwistedNormLower.sites_eq]
    push_cast
    ring
  have hPlow : (Qv ^ m)⁻¹ ≤ SU2GaussianMass.mass (24 * β) ^ m := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hQpos.le) hmass m
  have hQm : Qv ^ m = Real.exp ((m : ℝ) * Real.log Qv) := by
    rw [Real.exp_nat_mul, Real.exp_log hQpos]
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith only [this]
  have hfin : 2 * Real.exp (-L) ≤ Real.exp (-X) * (Qv ^ m)⁻¹ := by
    rw [hQm, ← Real.exp_neg, ← Real.exp_add]
    calc 2 * Real.exp (-L) ≤ Real.exp 1 * Real.exp (-L) :=
          mul_le_mul_of_nonneg_right h2e (Real.exp_pos _).le
      _ = Real.exp (1 + -L) := (Real.exp_add _ _).symm
      _ = _ := by
          congr 1
          rw [hL, hmv]
          unfold levelBudget
          ring
  exact hoff.trans (hfin.trans (mul_le_mul_of_nonneg_left (hPlow.trans (TwistedNormLower.norm_lower' n β hβ0))
    (Real.exp_pos _).le))


/-! ### The window from trial functions -/

/-- **`ValleyGap` below `‖T‖` at the threshold.** For `β ≥ A n⁸` and level `1/(16 n⁴)`, the valley carries at least a
quarter of the mass of `η²`, so `valleyGap_explicit` applies with `m₀ = 1/4`. -/
theorem valleyGap_at_threshold (hβ : threshold * (n : ℝ) ^ 8 ≤ β) (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) :
    ValleyGap n β (1 / (16 * (n : ℝ) ^ 4)) (‖T‖ * (1 - 1 / 4 * Real.exp (-(72 * β * (n : ℝ) ^ 3)))) η := by
  have hβ0 : 0 ≤ β := by
    have := threshold_pos
    have h8 : (0 : ℝ) ≤ (n : ℝ) ^ 8 := by positivity
    have := mul_nonneg this.le h8
    linarith only [this, hβ]
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ0
  set σ := 1 / (16 * (n : ℝ) ^ 4) with hσ
  refine valleyGap_explicit n β hβ0 η hη hnorm heig σ (1 / 4) (by norm_num) ?_
  have hm := eigen_valley_mass n β hβ0 σ le_rfl η (top_flip n β η hη heig hlam 2 0) hnorm ‖T‖ hlam heig
  have hoff := offError_le_norm n β hβ
  rw [← hσ] at hoff
  have h1 : Real.exp (-(β * σ / 2)) ≤ Real.exp (-(n : ℝ) ^ 4) * ‖T‖ := by
    unfold offError at hoff
    have := Real.exp_pos (-(2 * β / n))
    linarith only [hoff, this]
  have h2 : Real.exp (-(β * σ)) ≤ (Real.exp (-(n : ℝ) ^ 4) * ‖T‖) ^ 2 := by
    have e : Real.exp (-(β * σ)) = Real.exp (-(β * σ / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
  have h3 : Real.exp (-(n : ℝ) ^ 4) ^ 2 ≤ 1 / 2 := by
    have e : Real.exp (-(n : ℝ) ^ 4) ^ 2 = (Real.exp ((n : ℝ) ^ 4) ^ 2)⁻¹ := by
      rw [Real.exp_neg, inv_pow]
    rw [e, one_div]
    apply inv_anti₀ (by norm_num)
    have := Real.add_one_le_exp ((n : ℝ) ^ 4)
    nlinarith only [this, hn4]
  have h4 : Real.exp (-(β * σ)) / ‖T‖ ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [mul_pow] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  linarith only [hm, h4]

/-- **The contraction on a smaller valley.** `neutral_contraction_general` with `offError_le_of_budget`, so no bound
on `offError` is assumed. Conditional on `ValleyGap`, which is now required only at a level about `n³ log β / β`. -/
theorem neutral_contraction_budget (hβ : 1 / 24 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (X τ : ℝ)
    (h1 : 2 * levelBudget n β X ≤ β * σ) (h2 : levelBudget n β X * n ≤ 2 * β) (hε : Real.exp (-X) ≤ τ)
    (ρ r : ℝ) (hρ : 0 ≤ ρ) (ψ : C(Slice n, ℝ)) (H : ValleyGap n β σ ρ ψ) (t : C(Slice n, ℝ))
    (htn : ∀ u, 0 ≤ t u) (htne : ∃ u, t u ≠ 0)
    (htr : r * ∫ u, t u ^ 2 ∂μ' ≤ valleyForm n β σ t) (hgap : ρ ≤ (τ - Real.exp (-X)) * r) :
    ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω ∧ Neutral n Ω ∧
      ∀ f, Neutral n f → inner ℂ Ω f = 0 → ‖T f‖ ≤ τ * ‖T‖ * ‖f‖ :=
  neutral_contraction_general n β (by linarith only [hβ]) σ hσ _ τ hε
    (offError_le_of_budget n β hβ σ X h1 h2) ρ r hρ ψ H t htn htne htr hgap

/-- **Both halves of the window, from trial functions.** Conditional. The hypotheses are all of one kind: integrals
of the actual kernel against functions that do not involve the ground state, namely `H` (through `valleyGap_of_trial`
or otherwise) and the bounds `htr` and `hm`. Nothing in the repository supplies them at the required accuracy,
and every one of them needs the form to relative accuracy about `1/n`. -/
theorem neutralWindow_of_trials (hβ0 : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (ε τ : ℝ) (hε : ε ≤ τ)
    (hoff : offError n β σ ≤ ε * ‖T‖) (ρ r : ℝ) (hρ : 0 ≤ ρ) (ψ : C(Slice n, ℝ)) (H : ValleyGap n β σ ρ ψ)
    (t : C(Slice n, ℝ)) (htn : ∀ u, 0 ≤ t u) (htne : ∃ u, t u ≠ 0)
    (htr : r * ∫ u, t u ^ 2 ∂μ' ≤ valleyForm n β σ t) (hgap : ρ ≤ (τ - ε) * r)
    (a b : C(Slice n, ℝ)) (ha : ∀ i c u, a (TwistedTransfer.flip n i c u) = a u)
    (hb : ∀ i c u, b (TwistedTransfer.flip n i c u) = b u)
    (hind : ∀ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) → ∃ u, s * a u + t * b u ≠ 0) (m : ℝ)
    (hm : ∀ s t : ℝ, m * ∫ u, (s * a u + t * b u) ^ 2 ∂μ' ≤
      ∫ u, (s * a u + t * b u) * (∫ v, twistedKernel n β (u, v) * (s * a v + t * b v) ∂μ') ∂μ')
    (ρ₂ : ℝ) (hρ₂ : ρ₂ * ‖T‖ ≤ m) : NeutralWindow n β τ ρ₂ := by
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ0
  obtain ⟨η, hη, hnormL, heig⟩ := exists_positive_top n β hβ0
  have hflip := top_flip n β η hη heig hlam
  refine ⟨ContinuousMap.toLp 2 (μ') ℂ (complexify η), hnormL, ?_, embed_neutral n η hflip, fun f hf hf' => ?_, ?_⟩
  · rw [transfer_embed]
    have hs : sm n β η = ‖T‖ • η := by
      ext u
      rw [sm_apply, heig]
      rfl
    rw [hs, WilsonPositiveGroundState.complexify_smul, map_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · have hmain := neutral_contraction_of_valley n β hβ0 σ hσ ρ hρ ψ H η hη heig f hf hf'
    have hr : r ≤ ‖T‖ := by
      have hpos := sq_integral_pos n t htne
      have h1 := valleyForm_le_norm n β σ t htn
      exact le_of_mul_le_mul_right (htr.trans h1) hpos
    have hρle : ρ ≤ (τ - ε) * ‖T‖ :=
      hgap.trans (mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hε))
    have hfin : ρ + offError n β σ ≤ τ * ‖T‖ := by
      nlinarith only [hρle, hoff]
    exact hmain.trans (mul_le_mul_of_nonneg_right hfin (norm_nonneg f))
  · obtain ⟨f, h1, h2, h3, h4⟩ := second_half_of_plane n β η a b ha hb hind m hm
    exact ⟨f, h1, h2, h3, (mul_le_mul_of_nonneg_right hρ₂ (norm_nonneg f)).trans h4⟩


/-! ### A Gaussian chart in actual coordinates -/

section Chart
open Complex
open scoped ComplexConjugate

/-- The ground Gaussian is real. -/
theorem cohE_zero_real {d : ℕ} (b : ℝ) (ρ : Fin d → ℝ) (x : EE d) :
    cohE b ρ 0 x = (((cohE b ρ 0 x).re : ℝ) : ℂ) := by
  have h : cohE b ρ 0 x = ((∏ i, TwistedSemiclassical.amp b (ρ i) 0 (x i) : ℝ) : ℂ) := by
    unfold cohE coh
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [h, Complex.ofReal_re]

/-- **Open: a Gaussian chart of the valley, as a change of variables.** Unlike a representation chosen separately for
each observable, everything is forced by the coordinate `χ` and the density `j`: the law of `χ` under Haar measure on
the valley is `j dx`, every invariant observable is a function `h'` of `χ` there, the representing vector is `√j h'`, and
the constraint `ψ` is carried to the ground Gaussian. The kernel `Kt` is the density of the transfer form in these
coordinates, and it is required to be within relative error `δ` of `c` times the free kernel at every pair of points
that carries mass. Off the image of the valley `Kt` is not determined by the form, and may be taken to be `c K₀`.
So this is a pointwise kernel estimate, and it would give all the eigenvalues of the compressed form, not just the
second. On the actual operator `χ` would be a gauge-fixed coordinate, and `j` would contain the Haar-to-Lebesgue Jacobian
and the Faddeev-Popov factor. Nothing here constructs it. -/
structure ValleyChart (n : ℕ) [NeZero n] (β σ : ℝ) (ψ : C(Slice n, ℝ)) {d : ℕ} (b : ℝ) (ρ : Fin d → ℝ)
    (χ : Slice n → EE d) (j : EE d → ℝ) (Kt : EE d × EE d → ℝ) (c δ : ℝ) : Prop where
  χ_meas : Measurable χ
  j_meas : Measurable j
  j_nonneg : ∀ x, 0 ≤ j x
  push : Measure.map χ ((WilsonSlabOperator.measure n).restrict (valley n σ)) =
    (volume : Measure (EE d)).withDensity fun x => ENNReal.ofReal (j x)
  Kt_meas : Measurable Kt
  cmp : ∀ p, |Kt p - c * kerE b ρ p| ≤ δ * (c * kerE b ρ p)
  lift : ∀ h, Invariant n h → ∃ h' : EE d → ℝ, Measurable h' ∧ (∀ u ∈ valley n σ, h u = h' (χ u)) ∧
    valleyForm n β σ h = ∫ p : EE d × EE d,
      (Real.sqrt (j p.1) * h' p.1) * Kt p * (Real.sqrt (j p.2) * h' p.2) ∂(volume.prod volume)
  ground : ∀ u ∈ valley n σ, ψ u = (cohE b ρ 0 (χ u)).re / Real.sqrt (j (χ u))

variable {n β}

/-- **A chart gives the valley gap.** Conditional on `ValleyChart`. Here `free_gap` and `perturbed_gap` act on the
Wilson form, with no further hypothesis. -/
theorem valleyGap_of_valleyChart {σ : ℝ} {ψ : C(Slice n, ℝ)} {d : ℕ} {b : ℝ} {ρ : Fin d → ℝ} (hb : 0 < b)
    (h0 : ∀ i, 0 < ρ i) (h1 : ∀ i, ρ i < 1) (r : ℝ) (hr : ∀ i, ρ i ≤ r) (hr1 : r ≤ 1)
    {χ : Slice n → EE d} {j : EE d → ℝ} {Kt : EE d × EE d → ℝ} {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (H : ValleyChart n β σ ψ b ρ χ j Kt c δ) : ValleyGap n β σ (c * (r + δ) * lamE b ρ) ψ := by
  intro h hh hmean
  obtain ⟨h', hm', hfac, hform⟩ := H.lift h hh
  set V := valley n σ with hV
  have hVm : MeasurableSet V := (valley_open n σ).measurableSet
  have hjm : Measurable fun x => ENNReal.ofReal (j x) := H.j_meas.ennreal_ofReal
  have hjlt : ∀ᵐ x ∂(volume : Measure (EE d)), ENNReal.ofReal (j x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  -- the change of variables
  have hcov (F : EE d → ℝ) (hF : Measurable F) : ∫ u in V, F (χ u) ∂μ' = ∫ x, j x * F x := by
    have h1 := integral_map (μ := (μ').restrict V) H.χ_meas.aemeasurable
      (f := F) hF.aestronglyMeasurable
    rw [H.push, integral_withDensity_eq_integral_toReal_smul hjm hjlt] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change (ENNReal.ofReal (j x)).toReal • F x = j x * F x
    rw [ENNReal.toReal_ofReal (H.j_nonneg x), smul_eq_mul]
  have hcoi (F : EE d → ℝ) (hF : Measurable F) (hi : IntegrableOn (fun u => F (χ u)) V μ') :
      Integrable fun x => j x * F x := by
    have h2 : Integrable F (Measure.map χ ((μ').restrict V)) :=
      (integrable_map_measure hF.aestronglyMeasurable H.χ_meas.aemeasurable).mpr hi
    rw [H.push, integrable_withDensity_iff_integrable_smul' hjm hjlt] at h2
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    change (ENNReal.ofReal (j x)).toReal • F x = j x * F x
    rw [ENNReal.toReal_ofReal (H.j_nonneg x), smul_eq_mul]
  -- the representing vector
  set f0 : EE d → ℝ := fun x => Real.sqrt (j x) * h' x with hf0
  have hf0m : Measurable f0 := H.j_meas.sqrt.mul hm'
  have hsq (x : EE d) : f0 x ^ 2 = j x * h' x ^ 2 := by
    rw [hf0, mul_pow, Real.sq_sqrt (H.j_nonneg x)]
  have hi2 : IntegrableOn (fun u => h' (χ u) ^ 2) V μ' := by
    have hc0 : IntegrableOn (fun u => h u ^ 2) V μ' := (ci n (h.continuous.pow 2)).integrableOn
    refine hc0.congr_fun (fun u hu => ?_) hVm
    dsimp only
    rw [hfac u hu]
  have hf0sq : Integrable fun x => f0 x ^ 2 := by
    have := hcoi (fun x => h' x ^ 2) (hm'.pow_const 2) hi2
    simpa only [hsq] using this
  have hf0L : MemLp f0 2 (volume : Measure (EE d)) :=
    (memLp_two_iff_integrable_sq hf0m.aestronglyMeasurable).mpr hf0sq
  have hfL : MemLp (fun x => ((f0 x : ℝ) : ℂ)) 2 (volume : Measure (EE d)) := hf0L.ofReal
  let f : Lp ℂ 2 (volume : Measure (EE d)) := hfL.toLp
  have hfae : f =ᵐ[volume] fun x => ((f0 x : ℝ) : ℂ) := MemLp.coeFn_toLp _
  -- the norm
  have hA : ‖f‖ ^ 2 = ∫ u in V, h u ^ 2 ∂μ' := by
    rw [← sq_norm_eq f]
    have e1 : ∫ x, ‖f x‖ ^ 2 = ∫ x, f0 x ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hfae] with x hx
      rw [hx]
      simp
    have e2 : ∫ u in V, h u ^ 2 ∂μ' = ∫ u in V, h' (χ u) ^ 2 ∂μ' := by
      refine setIntegral_congr_fun hVm fun u hu => ?_
      dsimp only
      rw [hfac u hu]
    rw [e1, e2, hcov (fun x => h' x ^ 2) (hm'.pow_const 2)]
    simp only [hsq]
  -- orthogonality
  have horth : inner ℂ (cv hb h0 h1 0) f = 0 := by
    set G : EE d → ℝ := fun x => (cohE b ρ 0 x).re with hG
    have hGm : Measurable G :=
      (Complex.continuous_re.comp (cohE_continuous b ρ 0)).measurable
    have hmeanG : ∫ x, G x * f0 x = 0 := by
      rw [← hmean]
      have e1 : ∫ u in V, h u * ψ u ∂μ' = ∫ u in V, (h' (χ u) * (G (χ u) / Real.sqrt (j (χ u)))) ∂μ' := by
        refine setIntegral_congr_fun hVm fun u hu => ?_
        dsimp only
        rw [hfac u hu, H.ground u hu]
      rw [e1, hcov (fun x => h' x * (G x / Real.sqrt (j x)))
        (hm'.mul (hGm.div H.j_meas.sqrt))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      have hd : j x / Real.sqrt (j x) = Real.sqrt (j x) := Real.div_sqrt
      rw [hf0]
      dsimp only
      calc G x * (Real.sqrt (j x) * h' x) = G x * (j x / Real.sqrt (j x) * h' x) := by rw [hd]
        _ = _ := by ring
    rw [L2.inner_def]
    have e : ∫ a, inner ℂ ((cv hb h0 h1 0) a) (f a) = ((∫ x, G x * f0 x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [cv_coe hb h0 h1 0, hfae] with a h₁ h₂
      rw [h₁, h₂, cohE_zero_real b ρ a]
      simp [hG, mul_comm]
    rw [e, hmeanG]
    simp
  -- the form
  have hB : (formB Kt f f).re = valleyForm n β σ h := by
    rw [hform]
    unfold formB
    have hae : (fun p : EE d × EE d => conj (f p.1) * ((Kt p : ℝ) : ℂ) * f p.2) =ᵐ[volume.prod volume]
        fun p => (((Real.sqrt (j p.1) * h' p.1) * Kt p * (Real.sqrt (j p.2) * h' p.2) : ℝ) : ℂ) := by
      filter_upwards [qmp_fst hfae, qmp_snd hfae] with p h₁ h₂
      rw [h₁, h₂]
      simp [hf0]
    rw [integral_congr_ae hae, integral_complex_ofReal, Complex.ofReal_re]
  have hmain := perturbed_gap hb h0 h1 r hr hr1 c δ hc hδ Kt H.Kt_meas H.cmp f horth
  rw [hB, hA] at hmain
  exact hmain

end Chart

/-- **Contraction from a chart.** Conditional on `ValleyChart`, on a trial function reaching the free top within `δ`,
and on `offError ≤ ε ‖T‖`, which `offError_le_of_budget` provides at any level above about `n³ log β / β`. -/
theorem contraction_of_valleyChart (hβ0 : 0 ≤ β) (σ : ℝ) (hσ : σ ≤ 1 / (16 * (n : ℝ) ^ 4)) (ε τ : ℝ) (hε : ε ≤ τ)
    (hoff : offError n β σ ≤ ε * ‖T‖) (ψ : C(Slice n, ℝ)) {d : ℕ} {b : ℝ} {ρ : Fin d → ℝ}
    (hb : 0 < b) (h0 : ∀ i, 0 < ρ i) (h1 : ∀ i, ρ i < 1) (r : ℝ) (hr : ∀ i, ρ i ≤ r) (hr1 : r ≤ 1)
    {χ : Slice n → EE d} {j : EE d → ℝ} {Kt : EE d × EE d → ℝ} (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hr0 : 0 ≤ r + δ) (H : ValleyChart n β σ ψ b ρ χ j Kt c δ)
    (t : C(Slice n, ℝ)) (htn : ∀ u, 0 ≤ t u) (htne : ∃ u, t u ≠ 0)
    (htr : c * (1 - δ) * lamE b ρ * ∫ u, t u ^ 2 ∂μ' ≤ valleyForm n β σ t)
    (hgap : r + δ ≤ (τ - ε) * (1 - δ)) :
    ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω ∧ Neutral n Ω ∧
      ∀ f, Neutral n f → inner ℂ Ω f = 0 → ‖T f‖ ≤ τ * ‖T‖ * ‖f‖ := by
  have hL : 0 ≤ lamE b ρ := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hcL : 0 ≤ c * lamE b ρ := mul_nonneg hc hL
  refine neutral_contraction_general n β hβ0 σ hσ ε τ hε hoff (c * (r + δ) * lamE b ρ)
    (c * (1 - δ) * lamE b ρ) (by positivity) ψ
    (valleyGap_of_valleyChart hb h0 h1 r hr hr1 hc hδ H) t htn htne htr ?_
  have h := mul_le_mul_of_nonneg_left hgap hcL
  calc c * (r + δ) * lamE b ρ = c * lamE b ρ * (r + δ) := by ring
    _ ≤ c * lamE b ρ * ((τ - ε) * (1 - δ)) := h
    _ = _ := by ring

/-! ### Gauge-invariant integrals in Lebesgue coordinates -/

section TreeChart
open SU2HaarSlice
open WilsonTimeSlab WilsonSlabOperator TwistedTreeGauge

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The field in the tree gauge with the given off-tree links. -/
def treeGlue (x : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) : Slice n :=
  fun e => if h : isTree n e then 1 else x ⟨e, h⟩

theorem treeGlue_measurable : Measurable (treeGlue n) := by
  refine measurable_pi_iff.mpr fun e => ?_
  unfold treeGlue
  by_cases h : isTree n e
  · simp only [dif_pos h]
    exact measurable_const
  · simp only [dif_neg h]
    exact measurable_pi_apply _

/-- A global rotation is a gauge transformation on tree-gauge fields. -/
theorem treeGlue_conj (g : Q) (x : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) :
    treeGlue n (conjF g x) = gaugeSlice (fun _ => g) (treeGlue n x) := by
  funext e
  unfold treeGlue gaugeSlice conjF
  by_cases h : isTree n e
  · simp only [dif_pos h]
    group
  · simp only [dif_neg h]

/-- **Gauge-invariant integrals on the off-tree links.** The coordinate tree removes all gauge freedom except the
global rotation, with no Jacobian. Exact. -/
theorem integral_off_tree (F : C(Slice n, ℝ)) (hF : ∀ (h : SliceGauge n Q) u, F (gaugeSlice h u) = F u) :
    ∫ u, F u ∂WilsonSlabOperator.measure n =
      ∫ x, F (treeGlue n x) ∂(Measure.pi fun _ : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} =>
        RegulatedGauge.compactHaar Q) := by
  rw [integral_invariant n F hF]
  set p : SpatialVertex n × Fin 3 → Prop := fun e => ¬ isTree n e with hp
  let μQ : SpatialVertex n × Fin 3 → Measure Q := fun _ => RegulatedGauge.compactHaar Q
  have hsplit := measurePreserving_piEquivPiSubtypeProd μQ p
  let G : ({e // p e} → Q) → ℝ := fun x => F (treeGlue n x)
  have hfix (w : Slice n) : treeFix n w = treeGlue n fun e => w e := by
    funext e
    unfold treeFix treeGlue
    split_ifs <;> rfl
  have h1 : ∫ w, F (treeFix n w) ∂WilsonSlabOperator.measure n =
      ∫ y, G y.1 ∂((Measure.pi fun e : {e // p e} => μQ e).prod (Measure.pi fun e : {e // ¬ p e} => μQ e)) := by
    rw [← hsplit.integral_comp (MeasurableEquiv.measurableEmbedding _) (fun y => G y.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    change F (treeFix n w) = F (treeGlue n fun e => w e)
    rw [hfix]
  rw [h1, integral_fun_fst]
  simp only [probReal_univ, one_smul]
  rfl

/-- **Gauge-invariant integrals in Lebesgue coordinates.** Exact, with no estimate. Tree gauge removes the local gauge
freedom with no Jacobian (`integral_off_tree`), the frame weight removes the global rotation (`integral_frame`), and each
off-tree link is a gnomonic coordinate around `r` with density `gnomDensity` (`integral_pi_near`). Here `r` would be the
flat field in tree gauge. The lower bound `hw` on the frame weight on the support of `F` is a hypothesis. This is an
identity for integrals of one field. It is not a chart in the sense of `ValleyChart`, since the coordinates still carry
the three frame directions, which have no restoring force, and it says nothing about the kernel. -/
theorem integral_tree_chart (F : C(Slice n, ℝ)) (hF : ∀ (h : SliceGauge n Q) u, F (gaugeSlice h u) = F u)
    (r : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) (w₀ : ℝ) (hw₀ : 0 < w₀)
    (hw : ∀ x, F (treeGlue n x) ≠ 0 → w₀ ≤ frameWeight r x) :
    ∫ u, F u ∂WilsonSlabOperator.measure n =
      ∫ t : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → R3,
        F (treeGlue n fun e => r e * gnomQ (t e)) / frameWeight r (fun e => r e * gnomQ (t e))
          ∂(Measure.pi fun _ => gnomMeasure) := by
  have hG : Measurable fun x => F (treeGlue n x) := F.continuous.measurable.comp (treeGlue_measurable n)
  obtain ⟨B, hB⟩ : ∃ B, ∀ u, |F u| ≤ B := ⟨‖F‖, fun u => F.norm_coe_le_norm u⟩
  have hinv (g : Q) (x : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) :
      F (treeGlue n (conjF g x)) = F (treeGlue n x) := by
    rw [treeGlue_conj, hF]
  rw [integral_off_tree n F hF, integral_frame r _ hG hinv B (fun x => hB _) w₀ hw₀ hw]
  have hm : Measurable fun x => F (treeGlue n x) / frameWeight r x := hG.div (frameWeight_measurable r)
  have h2 := integral_pi_near r ((nearSet r).indicator fun x => F (treeGlue n x) / frameWeight r x)
    (hm.indicator (nearSet_measurable r)) (fun w ⟨e, he⟩ => Set.indicator_of_notMem (fun hc => he (Set.mem_pi.mp hc e (Set.mem_univ e))) _)
  rw [← integral_indicator (nearSet_measurable r), h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine Set.indicator_of_mem (Set.mem_pi.mpr fun e _ => ?_) _
  change 0 < (((r e)⁻¹ * (r e * gnomQ (t e)) : Q) : Quaternion ℝ).re
  rw [inv_mul_cancel_left]
  exact gnomQ_re_pos _

end TreeChart

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedSemiclassical

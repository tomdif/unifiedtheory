/- A continuous-time Euclidean two-point kernel at fixed spatial momentum.
The mass law is arbitrary finite positive measure with the stated threshold;
the interacting application constructs that law rather than assuming it.
This module proves the L2 realization and reflection positivity. It does
not assert a four-dimensional local Wightman field or a Gaussian measure. -/
import UnifiedTheory.Audit.KFCausalResolventMassMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalMassEuclideanKernel
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal

variable (ρ : Measure ℝ) [IsFiniteMeasure ρ] (δ : ℝ) (hδ : 0 < δ) (q : ℝ)

/-- `q` is the spatial momentum magnitude. Clamping below threshold only
defines the representative off the support of the mass law. -/
def energy (s : ℝ) : ℝ := Real.sqrt (q^2 + max (δ^2) s)

include hδ in
theorem energy_lower (s : ℝ) : δ ≤ energy δ q s := by
  have hb : δ^2 ≤ q^2 + max (δ^2) s := by
    nlinarith [le_max_left (δ^2) s, sq_nonneg q]
  simpa only [Real.sqrt_sq hδ.le, energy] using Real.sqrt_le_sqrt hb

include hδ in
theorem energy_pos (s : ℝ) : 0 < energy δ q s := hδ.trans_le (energy_lower δ hδ q s)

theorem energy_on_support (hρ : ∀ᵐ s ∂ρ, δ^2 ≤ s) :
    ∀ᵐ s ∂ρ, energy δ q s = Real.sqrt (q^2+s) := by
  filter_upwards [hρ] with s hs
  simp only [energy, max_eq_right hs]

def amplitude (a : ℝ≥0) (s : ℝ) : ℝ :=
  Real.exp (-(a : ℝ)*energy δ q s) / Real.sqrt (2*energy δ q s)

theorem amplitude_nonnegative (a : ℝ≥0) (s : ℝ) : 0 ≤ amplitude δ q a s := by
  unfold amplitude
  positivity

include hδ in
theorem amplitude_bound (a : ℝ≥0) (s : ℝ) :
    amplitude δ q a s ≤ (Real.sqrt (2*δ))⁻¹ := by
  have he : Real.exp (-(a : ℝ)*energy δ q s) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [a.coe_nonneg, energy_pos δ hδ q s]
  have hd : 0 < Real.sqrt (2*energy δ q s) :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) (energy_pos δ hδ q s))
  have hl : Real.sqrt (2*δ) ≤ Real.sqrt (2*energy δ q s) :=
    Real.sqrt_le_sqrt (by linarith [energy_lower δ hδ q s])
  calc
    amplitude δ q a s ≤ 1 / Real.sqrt (2*energy δ q s) :=
      div_le_div_of_nonneg_right he hd.le
    _ ≤ (Real.sqrt (2*δ))⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) hl

def featureFunction (a : ℝ≥0) (s : ℝ) : ℂ := amplitude δ q a s

include hδ in
theorem feature_memLp (a : ℝ≥0) : MemLp (featureFunction δ q a) 2 ρ := by
  refine MemLp.of_bound ?_ ((Real.sqrt (2*δ))⁻¹) ?_
  · apply Measurable.aestronglyMeasurable
    unfold featureFunction amplitude energy
    fun_prop
  · apply Filter.Eventually.of_forall
    intro s
    simpa only [featureFunction, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (amplitude_nonnegative δ q a s)] using amplitude_bound δ hδ q a s

def feature (a : ℝ≥0) : Lp ℂ 2 ρ :=
  (feature_memLp ρ δ hδ q a).toLp (featureFunction δ q a)

def kernel (a b : ℝ≥0) : ℂ := inner ℂ (feature ρ δ hδ q a) (feature ρ δ hδ q b)

include hδ in
theorem amplitude_product (a b : ℝ≥0) (s : ℝ) :
    amplitude δ q a s * amplitude δ q b s =
      Real.exp (-((a : ℝ)+(b : ℝ))*energy δ q s) / (2*energy δ q s) := by
  unfold amplitude
  rw [div_mul_div_comm, ← Real.exp_add, Real.mul_self_sqrt
    (mul_nonneg (by norm_num) (energy_pos δ hδ q s).le)]
  congr 2
  ring

theorem feature_inner_ae (a b : ℝ≥0) :
    (fun s => inner ℂ (feature ρ δ hδ q a s) (feature ρ δ hδ q b s)) =ᵐ[ρ]
      (fun s => ((Real.exp (-((a : ℝ)+(b : ℝ))*energy δ q s) /
        (2*energy δ q s) : ℝ) : ℂ)) := by
  filter_upwards [(feature_memLp ρ δ hδ q a).coeFn_toLp,
    (feature_memLp ρ δ hδ q b).coeFn_toLp] with s ha hb
  change inner ℂ (feature ρ δ hδ q a s) (feature ρ δ hδ q b s) = _
  unfold feature
  rw [ha, hb]
  simp only [featureFunction, RCLike.inner_apply, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  rw [mul_comm, amplitude_product δ hδ q]

include hδ in
theorem kernel_integrable (a b : ℝ≥0) :
    Integrable (fun s => ((Real.exp (-((a : ℝ)+(b : ℝ))*energy δ q s) /
      (2*energy δ q s) : ℝ) : ℂ)) ρ :=
  (L2.integrable_inner (feature ρ δ hδ q a) (feature ρ δ hδ q b)).congr
    (feature_inner_ae ρ δ hδ q a b)

theorem kernel_integral (a b : ℝ≥0) :
    kernel ρ δ hδ q a b =
      ∫ s, ((Real.exp (-((a : ℝ)+(b : ℝ))*energy δ q s) /
        (2*energy δ q s) : ℝ) : ℂ) ∂ρ := by
  rw [kernel, L2.inner_def]
  exact integral_congr_ae (feature_inner_ae ρ δ hδ q a b)

theorem reflection_positive {J : Type*} (S : Finset J) (a : J → ℝ≥0) (c : J → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S,
      (starRingEnd ℂ (c i)) * c j * kernel ρ δ hδ q (a i) (a j)).re := by
  have he : (∑ i ∈ S, ∑ j ∈ S,
      (starRingEnd ℂ (c i)) * c j * kernel ρ δ hδ q (a i) (a j)) =
      inner ℂ (∑ i ∈ S, c i • feature ρ δ hδ q (a i))
        (∑ i ∈ S, c i • feature ρ δ hδ q (a i)) := by
    simp only [sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right, kernel, mul_assoc, mul_left_comm]
  rw [he]
  exact inner_self_nonneg (𝕜 := ℂ)

end
end UnifiedTheory.Audit.KFCausalMassEuclideanKernel

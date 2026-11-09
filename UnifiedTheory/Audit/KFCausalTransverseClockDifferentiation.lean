/- A local L2 domination calculus for complete transverse amplitudes.
Finite sums are taken before squaring, so every interference term remains. -/
import UnifiedTheory.Audit.KFCausalNeutralQuarticBoundary
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalTransverseClockDifferentiation
noncomputable section
open MeasureTheory
open scoped ComplexConjugate Topology
open KFCausalTransverseDilationFlow (Transverse)

structure Regular (f g : ℝ → Transverse → ℂ) : Prop where
  value_continuous : Continuous (fun x : ℝ × Transverse => f x.1 x.2)
  slope_continuous : Continuous (fun x : ℝ × Transverse => g x.1 x.2)
  derivative : ∀ s q, HasDerivAt (fun t => f t q) (g s q) s
  domination : ∀ s₀ : ℝ, ∃ D : Transverse → ℝ, Continuous D ∧ MemLp D 2 volume ∧
    (∀ q, 0 ≤ D q) ∧ ∀ s ∈ Set.Icc (s₀-1) (s₀+1), ∀ q,
      ‖f s q‖ ≤ D q ∧ ‖g s q‖ ≤ D q

theorem continuous_local_bound (f : ℝ → ℂ) (hf : Continuous f) (s : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (s-1) (s+1), ‖f t‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max 0 M, le_max_left _ _, fun t ht => (hM t ht).trans (le_max_right _ _)⟩

theorem regular_mul (f g : ℝ → Transverse → ℂ) (hf : Regular f g)
    (c d : ℝ → ℂ) (hc : Continuous c) (hd : Continuous d)
    (hcd : ∀ s, HasDerivAt c (d s) s) :
    Regular (fun s q => c s*f s q) (fun s q => d s*f s q+c s*g s q) := by
  refine ⟨(hc.comp continuous_fst).mul hf.value_continuous,
    ((hd.comp continuous_fst).mul hf.value_continuous).add
      ((hc.comp continuous_fst).mul hf.slope_continuous),
    fun s q => (hcd s).mul (hf.derivative s q), ?_⟩
  intro s₀
  obtain ⟨D,hD,hD₂,hD₀,hb⟩ := hf.domination s₀
  obtain ⟨M,hM,hm⟩ := continuous_local_bound c hc s₀
  obtain ⟨N,hN,hn⟩ := continuous_local_bound d hd s₀
  refine ⟨fun q => (M+N)*D q, continuous_const.mul hD,
    hD₂.const_mul (M+N), fun q => mul_nonneg (add_nonneg hM hN) (hD₀ q), ?_⟩
  intro s hs q
  have hfb := (hb s hs q).1
  have hgb := (hb s hs q).2
  have hcf : ‖c s*f s q‖ ≤ M*D q := by
    rw [norm_mul]; exact mul_le_mul (hm s hs) hfb (norm_nonneg _) hM
  have hdf : ‖d s*f s q‖ ≤ N*D q := by
    rw [norm_mul]; exact mul_le_mul (hn s hs) hfb (norm_nonneg _) hN
  have hcg : ‖c s*g s q‖ ≤ M*D q := by
    rw [norm_mul]; exact mul_le_mul (hm s hs) hgb (norm_nonneg _) hM
  constructor
  · exact hcf.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN) (hD₀ q))
  · calc
      _ ≤ ‖d s*f s q‖+‖c s*g s q‖ := norm_add_le _ _
      _ ≤ N*D q+M*D q := add_le_add hdf hcg
      _ = _ := by ring

theorem regular_sum (N : ℕ) (f g : Fin N → ℝ → Transverse → ℂ)
    (hf : ∀ i, Regular (f i) (g i)) :
    Regular (fun s q => ∑ i, f i s q) (fun s q => ∑ i, g i s q) := by
  refine ⟨continuous_finset_sum _ (fun i _ => (hf i).value_continuous),
    continuous_finset_sum _ (fun i _ => (hf i).slope_continuous),
    fun s q => ?_, ?_⟩
  · exact HasDerivAt.fun_sum (fun i _ => (hf i).derivative s q)
  intro s₀
  choose D hD hD₂ hD₀ hb using fun i => (hf i).domination s₀
  refine ⟨fun q => ∑ i, D i q, continuous_finset_sum _ (fun i _ => hD i),
    memLp_finset_sum _ (fun i _ => hD₂ i),
    fun q => Finset.sum_nonneg (fun i _ => hD₀ i q), ?_⟩
  intro s hs q
  exact ⟨(norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => (hb i s hs q).1)),
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => (hb i s hs q).2))⟩

theorem regular_memLp (f g : ℝ → Transverse → ℂ) (hf : Regular f g) (s : ℝ) :
    MemLp (f s) 2 volume ∧ MemLp (g s) 2 volume := by
  obtain ⟨D,_,hD,hD₀,hb⟩ := hf.domination s
  have hs : s ∈ Set.Icc (s-1) (s+1) := by constructor <;> linarith
  constructor
  · apply hD.of_le (hf.value_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hD₀ q)] using (hb s hs q).1)
  · apply hD.of_le (hf.slope_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hD₀ q)] using (hb s hs q).2)

def energy (f : ℝ → Transverse → ℂ) (s : ℝ) : ℝ := ∫ q, ‖f s q‖^2
def response (f g : ℝ → Transverse → ℂ) (s : ℝ) : ℝ :=
  ∫ q, 2*(conj (f s q)*g s q).re

theorem energy_derivative (f g : ℝ → Transverse → ℂ) (hf : Regular f g) (s : ℝ) :
    Integrable (fun q => 2*(conj (f s q)*g s q).re) ∧
      HasDerivAt (energy f) (response f g s) s := by
  obtain ⟨D,_,hD,hD₀,hb⟩ := hf.domination s
  have hB : Integrable (fun q => 2*(D q*D q)) := (hD.integrable_mul hD).const_mul 2
  have hfi := (regular_memLp f g hf s).1
  have hi : Integrable (fun q => ‖f s q‖^2) :=
    (memLp_two_iff_integrable_sq_norm hfi.aestronglyMeasurable).mp hfi
  have hv (t : ℝ) : Continuous (fun q => ‖f t q‖^2) :=
    (hf.value_continuous.comp (continuous_const.prodMk continuous_id)).norm.pow 2
  have hg : Continuous (fun q => 2*(conj (f s q)*g s q).re) := by
    have hfc := hf.value_continuous.comp (continuous_const.prodMk continuous_id (f := fun _ : Transverse => s))
    have hgc := hf.slope_continuous.comp (continuous_const.prodMk continuous_id (f := fun _ : Transverse => s))
    exact continuous_const.mul (Complex.continuous_re.comp
      ((Complex.continuous_conj.comp hfc).mul hgc))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t q => ‖f t q‖^2) (F' := fun t q => 2*(conj (f t q)*g t q).re)
    (bound := fun q => 2*(D q*D q))
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t => (hv t).aestronglyMeasurable)) hi hg.aestronglyMeasurable
    _ hB (Filter.Eventually.of_forall (fun q t _ =>
      KFCausalNeutralQuarticBoundary.norm_square_derivative (fun v => f v q) (fun v => g v q) t
        (hf.derivative t q)))
  exact Filter.Eventually.of_forall (fun q t ht => by
    calc
      ‖2*(conj (f t q)*g t q).re‖ = 2*|(conj (f t q)*g t q).re| := by
        rw [Real.norm_eq_abs, abs_mul]; norm_num
      _ ≤ 2*‖conj (f t q)*g t q‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ = 2*(‖f t q‖*‖g t q‖) := by rw [norm_mul, Complex.norm_conj]
      _ ≤ 2*(D q*D q) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hb t ht q).1 (hb t ht q).2 (norm_nonneg _) (hD₀ q)) (by norm_num))

theorem response_continuous (f g : ℝ → Transverse → ℂ) (hf : Regular f g) :
    Continuous (response f g) := by
  have hc : Continuous (fun x : ℝ × Transverse => 2*(conj (f x.1 x.2)*g x.1 x.2).re) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((Complex.continuous_conj.comp hf.value_continuous).mul hf.slope_continuous))
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨D,_,hD,hD₀,hb⟩ := hf.domination s
  apply continuousAt_of_dominated
    (F := fun t q => 2*(conj (f t q)*g t q).re) (bound := fun q => 2*(D q*D q))
    (Filter.Eventually.of_forall (fun t =>
      (hc.comp (continuous_const.prodMk continuous_id (f := fun _ : Transverse => t))).aestronglyMeasurable))
    _ ((hD.integrable_mul hD).const_mul 2)
    (Filter.Eventually.of_forall (fun q =>
      (hc.comp (continuous_id.prodMk continuous_const (g := fun _ : ℝ => q))).continuousAt))
  filter_upwards [Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1)] with t ht
  exact Filter.Eventually.of_forall (fun q => by
    calc
      ‖2*(conj (f t q)*g t q).re‖ = 2*|(conj (f t q)*g t q).re| := by
        rw [Real.norm_eq_abs,abs_mul]; norm_num
      _ ≤ 2*‖conj (f t q)*g t q‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ = 2*(‖f t q‖*‖g t q‖) := by rw [norm_mul,Complex.norm_conj]
      _ ≤ 2*(D q*D q) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hb t ht q).1 (hb t ht q).2 (norm_nonneg _) (hD₀ q)) (by norm_num))

theorem energy_contDiff (f g : ℝ → Transverse → ℂ) (hf : Regular f g) :
    ContDiff ℝ 1 (energy f) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (energy_derivative f g hf s).2.differentiableAt, ?_⟩
  have he : deriv (energy f) = response f g := funext (fun s => (energy_derivative f g hf s).2.deriv)
  rw [he]
  exact response_continuous f g hf

#print axioms continuous_local_bound
#print axioms regular_mul
#print axioms regular_sum
#print axioms regular_memLp
#print axioms energy_derivative
#print axioms response_continuous
#print axioms energy_contDiff
end
end UnifiedTheory.Audit.KFCausalTransverseClockDifferentiation

/- Genuine external products of scalar Schwartz functions, with weighted
derivative estimates and continuous linear dependence on the first factor. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzProductTensor
noncomputable section
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def control (k n : ℕ) : Seminorm ℂ (SchwartzMap E ℂ) :=
  (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ E ℂ)

theorem projection_derivative_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (p : D →L[ℝ] E) (hp : ‖p‖ ≤ 1) (f : SchwartzMap E ℂ) (n : ℕ) (x : D) :
    ‖iteratedFDeriv ℝ n (f ∘ p) x‖ ≤ ‖iteratedFDeriv ℝ n f (p x)‖ := by
  rw [p.iteratedFDeriv_comp_right (f.smooth n) x le_rfl]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (p x)‖ * ∏ _ : Fin n, (1 : ℝ) := by
      gcongr
    _ = _ := by simp

theorem product_weight_bound (k : ℕ) (x : E × F) :
    ‖x‖ ^ k ≤ (1 + ‖x.1‖) ^ k * (1 + ‖x.2‖) ^ k := by
  have h : ‖x‖ ≤ (1 + ‖x.1‖) * (1 + ‖x.2‖) := by
    rw [Prod.norm_def]
    apply max_le <;> nlinarith [norm_nonneg x.1, norm_nonneg x.2]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg x) h k

theorem weighted_derivative_bound (f : SchwartzMap E ℂ) (g : SchwartzMap F ℂ)
    (k n : ℕ) (x : E × F) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : E × F => f y.1 * g y.2) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) *
        (2 ^ k * control k n f) * (2 ^ k * control k n g) := by
  have hf : ContDiff ℝ (n : ℕ) (fun y : E × F => f y.1) :=
    (f.smooth n).comp contDiff_fst
  have hg : ContDiff ℝ (n : ℕ) (fun y : E × F => g y.2) :=
    (g.smooth n).comp contDiff_snd
  have hder := norm_iteratedFDeriv_mul_le hf hg x le_rfl
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : E × F => f y.1) x‖ *
        ‖iteratedFDeriv ℝ (n-i) (fun y : E × F => g y.2) x‖ := by gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ((1 + ‖x.1‖) ^ k * ‖iteratedFDeriv ℝ i f x.1‖) *
        ((1 + ‖x.2‖) ^ k * ‖iteratedFDeriv ℝ (n-i) g x.2‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hfst := projection_derivative_bound (ContinuousLinearMap.fst ℝ E F)
        (ContinuousLinearMap.norm_fst_le _ _ _) f i x
      have hsnd := projection_derivative_bound (ContinuousLinearMap.snd ℝ E F)
        (ContinuousLinearMap.norm_snd_le _ _ _) g (n-i) x
      calc
        _ ≤ ((1 + ‖x.1‖) ^ k * (1 + ‖x.2‖) ^ k) *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x.1‖ *
              ‖iteratedFDeriv ℝ (n-i) g x.2‖) := by
          gcongr
          · exact product_weight_bound k x
          · exact hfst
          · exact hsnd
        _ = _ := by ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 ^ k * control k n f) * (2 ^ k * control k n g) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hfi := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k,n))
        le_rfl hi' f x.1
      have hgi := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k,n))
        le_rfl (Nat.sub_le n i) g x.2
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfi (Nat.cast_nonneg _)) hgi
        (by positivity) (by positivity)
    _ = _ := by simp only [Finset.sum_mul]

def tensorLeftCLM (g : SchwartzMap F ℂ) :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap (E × F) ℂ := by
  refine SchwartzMap.mkCLM (fun f x => f x.1 * g x.2)
    (fun f h x => by simp only [SchwartzMap.add_apply, add_mul])
    (fun c f x => by simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc])
    (fun f => ((f.smooth ⊤).comp contDiff_fst).mul ((g.smooth ⊤).comp contDiff_snd)) ?_
  intro kn
  refine ⟨Finset.Iic kn,
    (∑ i ∈ Finset.range (kn.2 + 1), (kn.2.choose i : ℝ)) * 2 ^ kn.1 *
      (2 ^ kn.1 * control kn.1 kn.2 g), by positivity, ?_⟩
  intro f x
  convert weighted_derivative_bound f g kn.1 kn.2 x using 1 <;>
    dsimp [control] <;> ring

def tensor (f : SchwartzMap E ℂ) (g : SchwartzMap F ℂ) : SchwartzMap (E × F) ℂ :=
  tensorLeftCLM g f

@[simp] theorem tensor_apply (f : SchwartzMap E ℂ) (g : SchwartzMap F ℂ) (x : E × F) :
    tensor f g x = f x.1 * g x.2 := rfl

theorem continuous_tensor_left (g : SchwartzMap F ℂ) :
    Continuous (fun f : SchwartzMap E ℂ => tensor f g) := (tensorLeftCLM g).continuous

end
end UnifiedTheory.Clay.YangMills.SchwartzProductTensor

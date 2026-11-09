/- Actual bounded L2 multiplication for measurable contractions, with
injectivity and symmetry proved from the pointwise multiplier. -/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalContractiveMultiplier
noncomputable section
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem product_memLp (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 μ) : MemLp (fun x => m x*f x) 2 μ := by
  apply (Lp.memLp f).of_le (hm.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

def multiply (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (product_memLp m hm hb f).toLp (fun x => m x*f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(product_memLp m hm hb (f+g)).coeFn_toLp,
      (product_memLp m hm hb f).coeFn_toLp,(product_memLp m hm hb g).coeFn_toLp,
      Lp.coeFn_add f g,Lp.coeFn_add ((product_memLp m hm hb f).toLp _)
        ((product_memLp m hm hb g).toLp _)] with x hfg hf hg hs ht
    rw [hfg,ht]
    simp only [Pi.add_apply,hf,hg,hs,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(product_memLp m hm hb (c • f)).coeFn_toLp,
      (product_memLp m hm hb f).coeFn_toLp,Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((product_memLp m hm hb f).toLp _)] with x hcf hf hs ht
    simp only [RingHom.id_apply]
    rw [hcf,ht]
    simp only [Pi.smul_apply,hf,hs,smul_eq_mul]
    ring

theorem multiply_norm_le (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 μ) : ‖multiply m hm hb f‖ ≤ ‖f‖ := by
  change ‖(product_memLp m hm hb f).toLp (fun x => m x*f x)‖ ≤ ‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  apply eLpNorm_mono_ae
  filter_upwards [] with x
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

def multiplyL (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (multiply m hm hb).mkContinuous 1 (fun f => by simpa only [one_mul] using multiply_norm_le m hm hb f)

theorem multiplyL_coe (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (f : Lp ℂ 2 μ) : multiplyL m hm hb f =ᵐ[μ] fun x => m x*f x :=
  (product_memLp m hm hb f).coeFn_toLp

theorem multiplyL_injective (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (hn : ∀ x, m x ≠ 0) : Function.Injective (multiplyL (μ := μ) m hm hb) := by
  intro f g he
  apply Lp.ext
  filter_upwards [multiplyL_coe m hm hb f,multiplyL_coe m hm hb g] with x hf hg
  have hx := congrArg (fun z : Lp ℂ 2 μ => z x) he
  dsimp only at hx
  rw [hf,hg] at hx
  exact mul_left_cancel₀ (hn x) hx

theorem multiplyL_symmetric (m : X → ℂ) (hm : Measurable m) (hb : ∀ x, ‖m x‖ ≤ 1)
    (hr : ∀ x, starRingEnd ℂ (m x) = m x) (f g : Lp ℂ 2 μ) :
    inner ℂ (multiplyL m hm hb f) g = inner ℂ f (multiplyL m hm hb g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyL_coe m hm hb f,multiplyL_coe m hm hb g] with x hf hg
  rw [hf,hg]
  change inner ℂ (m x • f x) (g x) = inner ℂ (f x) (m x • g x)
  rw [inner_smul_left,inner_smul_right,hr]

#print axioms product_memLp
#print axioms multiply_norm_le
#print axioms multiplyL
#print axioms multiplyL_injective
#print axioms multiplyL_symmetric

end
end UnifiedTheory.Audit.KFCausalContractiveMultiplier

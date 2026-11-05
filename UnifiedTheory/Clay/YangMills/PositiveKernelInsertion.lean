/- Positive kernel products and their genuine compact integral forms.
Subtracting a constant positive mode before multiplying by any other positive
kernel proves an insertion inequality. Reflection geometry is not supplied
by this analytic statement. -/
import UnifiedTheory.Clay.YangMills.CompactKernelMeanFloor
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PositiveKernelInsertion
noncomputable section
open MeasureTheory PositiveKernelForm KernelHilbertCompletion
open scoped TensorProduct

variable {X Y : Type*}

def pullback (K : PositiveKernel Y) (h : X → Y) : PositiveKernel X where
  value xy := K.value (h xy.1, h xy.2)
  positive N x a := K.positive N (fun i => h (x i)) a

def product (K L : PositiveKernel X) : PositiveKernel X :=
  KernelHilbertRealization.vectorKernel
    (fun x => canonical K x ⊗ₜ[ℂ] canonical L x)

theorem product_value (K L : PositiveKernel X) (x y : X) :
    (product K L).value (x, y) = K.value (x, y) * L.value (x, y) := by
  exact (TensorProduct.inner_tmul ℂ _ _ _ _).trans
    (congrArg₂ (· * ·) (canonical_inner K x y) (canonical_inner L x y))

def oneKernel : PositiveKernel X :=
  KernelHilbertRealization.vectorKernel (fun _ : X => (1 : ℂ))

def listProduct : List (PositiveKernel X) → PositiveKernel X
  | [] => oneKernel
  | K :: Ks => product K (listProduct Ks)

theorem listProduct_value (Ks : List (PositiveKernel X)) (x y : X) :
    (listProduct Ks).value (x, y) = (Ks.map (fun K => K.value (x, y))).prod := by
  induction Ks with
  | nil => simp [listProduct, oneKernel, KernelHilbertRealization.vectorKernel]
  | cons K Ks ih => simp only [listProduct, product_value, List.map_cons, List.prod_cons, ih]

def finiteProduct {P : Type*} [Fintype P] (K : P → PositiveKernel X) : PositiveKernel X :=
  listProduct (Finset.univ.toList.map K)

theorem finiteProduct_value {P : Type*} [Fintype P] (K : P → PositiveKernel X) (x y : X) :
    (finiteProduct K).value (x, y) = ∏ p, (K p).value (x, y) := by
  rw [finiteProduct, listProduct_value, List.map_map]
  exact Finset.prod_map_toList _ _

variable [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

def form (K : PositiveKernel X) (f : X → ℂ) : ℂ :=
  ∫ z : X × X, star (f z.1) * K.value (z.1, z.2) * f z.2 ∂μ.prod μ

theorem form_integrable (K : PositiveKernel X) (hK : Continuous K.value)
    (f : X → ℂ) (hf : Continuous f) :
    Integrable (fun z : X × X => star (f z.1) * K.value (z.1, z.2) * f z.2)
      (μ.prod μ) := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact (((continuous_star.comp hf).comp continuous_fst).mul hK).mul
    (hf.comp continuous_snd)

theorem form_eq_inner (K : PositiveKernel X) (hK : Continuous K.value)
    (f : X → ℂ) (hf : Continuous f) :
    form μ K f = inner ℂ (∫ x, f x • canonical K x ∂μ)
      (∫ x, f x • canonical K x ∂μ) := by
  have hi : Integrable (fun x => f x • canonical K x) μ :=
    (hf.smul (WilsonSlabPositivity.continuous_canonical K hK)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [form, integral_prod _ (form_integrable μ K hK f hf),
    ← CompactKernelOperatorPositivity.integral_inner_left μ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_inner hi]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [inner_smul_left, inner_smul_right, canonical_inner]
  simp only [Complex.star_def]
  ring

theorem form_nonneg (K : PositiveKernel X) (hK : Continuous K.value)
    (f : X → ℂ) (hf : Continuous f) :
    0 ≤ (form μ K f).re ∧ (form μ K f).im = 0 := by
  rw [form_eq_inner μ K hK f hf]
  exact ⟨inner_self_nonneg (𝕜 := ℂ), inner_self_im (𝕜 := ℂ) _⟩

theorem insertion_lower (B L R : PositiveKernel X)
    (hB : Continuous B.value) (hL : Continuous L.value) (hR : Continuous R.value)
    (c : ℝ) (hr : ∀ x y, R.value (x, y) = L.value (x, y) - (c : ℂ))
    (f : X → ℂ) (hf : Continuous f) :
    c * (form μ B f).re ≤ (form μ (product B L) f).re := by
  have hBR : Continuous (product B R).value := by
    have he : (product B R).value = fun z => B.value z * R.value z := by
      funext z
      exact product_value B R z.1 z.2
    rw [he]
    exact hB.mul hR
  have hn := (form_nonneg μ (product B R) hBR f hf).1
  have he : form μ (product B R) f = form μ (product B L) f - (c : ℂ) * form μ B f := by
    have hBL : Continuous (product B L).value := by
      have he : (product B L).value = fun z => B.value z * L.value z := by
        funext z
        exact product_value B L z.1 z.2
      rw [he]
      exact hB.mul hL
    rw [form, form, form, ← integral_const_mul, ← integral_sub
      (form_integrable μ (product B L) hBL f hf)
      ((form_integrable μ B hB f hf).const_mul (c : ℂ))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [product_value, product_value, hr]
    ring
  rw [he, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hn
  linarith

end
end UnifiedTheory.Clay.YangMills.PositiveKernelInsertion

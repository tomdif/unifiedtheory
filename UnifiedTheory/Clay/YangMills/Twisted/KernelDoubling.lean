/- Flux-sector doubling for integral kernels on an arbitrary probability space. No operator theory is used.

This replaces the eigenvalue abstraction of `TwistedFluxRecursion` for gauge groups with infinite-dimensional slice
spaces (SU(2): `X = SU(2)^{spatial edges}` with product Haar measure). Only the symmetry of the one-step kernel is used,
not positivity. The time extent must be even (t = 2s), which holds for the in-plane doublings L → 2L with L even.

* `cs_discriminant` / `integral_cs`: Cauchy–Schwarz for bounded measurable functions on a probability space, proved
  from scratch via the discriminant of `∫ (f + λ g)² ≥ 0`.
* `comp_sq_le`: for a symmetric bounded measurable kernel `F` and `G = F ∘ F`, `G(x,y)² ≤ G(x,x) G(y,y)`.
* `trace_double`: `Tr(G ∘ G) ≤ (Tr G)²`, i.e. `Z(4s) ≤ Z(2s)²` with `G = K_s ∘ K_s`.
* `sector_symm`: if `F` commutes with a measurable involution `Ω`, the sector kernel `F⁻(x,y) = (F x y - F x (Ω y))/2`
  is again symmetric, bounded and measurable.
* `comp_minus`: if `Ω` is also measure-preserving, then `F⁻ ∘ F⁻ = (F ∘ F)⁻`, by change of variables.
* `sector_double`: `Z_e(4s) ≤ Z_e(2s)²` in every flux sector, for kernels on any probability space.

For SU(2), take `X = SU(2)^{spatial edges}` with product Haar measure, and let `F` be the gauge-averaged one-step
transfer kernel. It is symmetric because `Re tr A = Re tr A⁻¹` in SU(2) and Haar measure is inversion invariant.
`Ω` flips the spatial links crossing a surface by the centre element −1. The remaining by-hand step is the
identification of the full lattice partition function with `tr(K_s ∘ K_s)` (Fubini over time slices). -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace UnifiedTheory.Clay.YangMills.Twisted.KernelDoubling

/-- Discriminant form of Cauchy–Schwarz. -/
theorem cs_discriminant {A B C : ℝ} (h : ∀ l : ℝ, 0 ≤ A + 2 * l * B + l ^ 2 * C) : B ^ 2 ≤ A * C := by
  have hA : 0 ≤ A := by simpa using h 0
  have hC : 0 ≤ C := by
    by_contra hc; push_neg at hc
    set l := (A + 1) / (-C) + 1
    have hC' : 0 < -C := by linarith
    have hl1 : 1 ≤ l := by simp only [l]; have : 0 ≤ (A + 1) / (-C) := by positivity
                           linarith
    have hlC : l * (-C) ≥ A + 1 := by
      have : (A + 1) / (-C) * (-C) = A + 1 := div_mul_cancel₀ _ (by linarith)
      simp only [l]; nlinarith
    have h1 := h l; have h2 := h (-l)
    nlinarith
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · subst hC0
    by_contra hB; push_neg at hB
    have hB0 : B ≠ 0 := by intro h0; rw [h0] at hB; norm_num at hB
    have h1 := h (-(A + 1) / (2 * B))
    have e : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by field_simp
    simp only [mul_zero, add_zero] at h1
    linarith
  · have := h (-B / C)
    have e : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B ^ 2 / C := by field_simp; ring
    rw [e] at this
    have : B ^ 2 / C ≤ A := by linarith
    rw [div_le_iff₀ hCpos] at this; linarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- A bounded measurable function is integrable on a probability space. -/
theorem integrable_of_bdd {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

/-- Cauchy–Schwarz for bounded measurable functions. -/
theorem integral_cs {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have bnd : ∀ (u v : X → ℝ), (∀ x, |u x| ≤ B) → (∀ x, |v x| ≤ B) → ∀ x, |u x * v x| ≤ |B| * |B| := by
    intro u v hu hv x; rw [abs_mul]
    exact mul_le_mul (le_trans (hu x) (le_abs_self B)) (le_trans (hv x) (le_abs_self B)) (abs_nonneg _) (abs_nonneg B)
  have iff2 : Integrable (fun x => f x ^ 2) μ := by
    simp_rw [sq]; exact integrable_of_bdd (hf.mul hf) (bnd f f hfB hfB)
  have igg : Integrable (fun x => g x ^ 2) μ := by
    simp_rw [sq]; exact integrable_of_bdd (hg.mul hg) (bnd g g hgB hgB)
  have ifg : Integrable (fun x => f x * g x) μ := integrable_of_bdd (hf.mul hg) (bnd f g hfB hgB)
  apply cs_discriminant
  intro l
  have hnn : 0 ≤ ∫ x, (f x + l * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e1 : ∫ x, (f x + l * g x) ^ 2 ∂μ =
      ∫ x, (f x ^ 2 + 2 * l * (f x * g x)) ∂μ + ∫ x, l ^ 2 * g x ^ 2 ∂μ := by
    have i1 : Integrable (fun x => f x ^ 2 + 2 * l * (f x * g x)) μ := iff2.add (ifg.const_mul _)
    have i2 : Integrable (fun x => l ^ 2 * g x ^ 2) μ := igg.const_mul _
    rw [← integral_add i1 i2]
    congr 1; ext x; ring
  have e2 : ∫ x, (f x ^ 2 + 2 * l * (f x * g x)) ∂μ = ∫ x, f x ^ 2 ∂μ + ∫ x, 2 * l * (f x * g x) ∂μ := by
    have i3 : Integrable (fun x => 2 * l * (f x * g x)) μ := ifg.const_mul _
    exact integral_add iff2 i3
  rw [e1, e2, integral_const_mul, integral_const_mul] at hnn
  linarith

/-- Kernel composition `(F ∘ G)(x,y) = ∫ F(x,z) G(z,y) dμ(z)`. -/
noncomputable def comp (μ : Measure X) (F G : X → X → ℝ) (x y : X) : ℝ := ∫ z, F x z * G z y ∂μ

/-- Trace of a kernel, `∫ G(x,x) dμ(x)`. -/
noncomputable def tr (μ : Measure X) (G : X → X → ℝ) : ℝ := ∫ x, G x x ∂μ

/-- A symmetric, bounded, measurable kernel. -/
structure SymKernel (F : X → X → ℝ) (B : ℝ) : Prop where
  meas : Measurable (Function.uncurry F)
  bdd : ∀ x y, |F x y| ≤ B
  symm : ∀ x y, F x y = F y x

theorem bdd_integral {f : X → ℝ} {C : ℝ} (hC : ∀ z, |f z| ≤ C) : |∫ z, f z ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)
  simpa [Real.norm_eq_abs, measure_univ] using this

theorem comp_meas {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) :
    Measurable (Function.uncurry (comp μ F F)) := by
  have hm : Measurable (fun q : (X × X) × X => F q.1.1 q.2 * F q.2 q.1.2) :=
    (hF.meas.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hF.meas.comp (measurable_snd.prodMk measurable_fst.snd))
  have := (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  exact this

theorem comp_bdd {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) (x y : X) : |comp μ F F x y| ≤ |B| * |B| := by
  apply bdd_integral; intro z; rw [abs_mul]
  exact mul_le_mul (le_trans (hF.bdd x z) (le_abs_self B)) (le_trans (hF.bdd z y) (le_abs_self B))
    (abs_nonneg _) (abs_nonneg B)

theorem comp_symm {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) (x y : X) : comp μ F F x y = comp μ F F y x := by
  unfold comp; congr 1; ext z; rw [hF.symm x z, hF.symm z y]; ring

theorem comp_kernel {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) : SymKernel (comp μ F F) (|B| * |B|) :=
  ⟨comp_meas hF, comp_bdd hF, comp_symm hF⟩

/-- Off-diagonal bound `G(x,y)² ≤ G(x,x) G(y,y)` for `G = F ∘ F`, `F` symmetric. -/
theorem comp_sq_le {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) (x y : X) :
    comp μ F F x y ^ 2 ≤ comp μ F F x x * comp μ F F y y := by
  have hx : Measurable (F x) := hF.meas.of_uncurry_left
  have hy : Measurable (F y) := hF.meas.of_uncurry_left
  have e : comp μ F F x y = ∫ z, F x z * F y z ∂μ := by unfold comp; congr 1; ext z; rw [hF.symm z y]
  have ex : comp μ F F x x = ∫ z, F x z ^ 2 ∂μ := by unfold comp; congr 1; ext z; rw [hF.symm z x]; ring
  have ey : comp μ F F y y = ∫ z, F y z ^ 2 ∂μ := by unfold comp; congr 1; ext z; rw [hF.symm z y]; ring
  rw [e, ex, ey]
  exact integral_cs hx hy (fun z => hF.bdd x z) (fun z => hF.bdd y z)

/-- The doubling inequality: `Tr(G ∘ G) ≤ (Tr G)²` for `G = F ∘ F` with `F` symmetric, bounded, measurable. -/
theorem trace_double {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) :
    tr μ (comp μ (comp μ F F) (comp μ F F)) ≤ (tr μ (comp μ F F)) ^ 2 := by
  set G := comp μ F F
  have hG := comp_kernel (μ := μ) hF
  set C := |B| * |B|
  have hGm : Measurable (Function.uncurry G) := hG.meas
  have hdiag : Measurable (fun x => G x x) := hGm.comp (measurable_id.prodMk measurable_id)
  have hrow : ∀ x, Measurable (fun y => G x y) := fun x => hGm.of_uncurry_left
  have hC : 0 ≤ C := by positivity
  -- inner integrals
  have inner : ∀ x, ∫ y, G x y * G y x ∂μ ≤ ∫ y, G x x * G y y ∂μ := by
    intro x
    apply integral_mono
    · exact integrable_of_bdd ((hrow x).mul (hGm.comp (measurable_id.prodMk measurable_const)))
        (fun y => by rw [abs_mul]; exact mul_le_mul (hG.bdd x y) (hG.bdd y x) (abs_nonneg _) hC)
    · exact integrable_of_bdd (measurable_const.mul hdiag)
        (fun y => by rw [abs_mul]; exact mul_le_mul (hG.bdd x x) (hG.bdd y y) (abs_nonneg _) hC)
    · intro y; show G x y * G y x ≤ G x x * G y y
      have hs : G y x = G x y := hG.symm y x
      rw [hs, ← sq]; exact comp_sq_le hF x y
  have outer_m1 : Measurable (fun x => ∫ y, G x y * G y x ∂μ) := by
    have hm : Measurable (fun q : X × X => G q.1 q.2 * G q.2 q.1) :=
      hGm.mul (hGm.comp (measurable_snd.prodMk measurable_fst))
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have outer_bdd1 : ∀ x, |∫ y, G x y * G y x ∂μ| ≤ C * C := fun x =>
    bdd_integral (fun y => by rw [abs_mul]; exact mul_le_mul (hG.bdd x y) (hG.bdd y x) (abs_nonneg _) hC)
  have e2 : ∀ x, ∫ y, G x x * G y y ∂μ = G x x * tr μ G := fun x => integral_const_mul _ _
  have htr : |tr μ G| ≤ C := bdd_integral (μ := μ) (fun y => hG.bdd y y)
  calc tr μ (comp μ G G) = ∫ x, ∫ y, G x y * G y x ∂μ ∂μ := rfl
    _ ≤ ∫ x, ∫ y, G x x * G y y ∂μ ∂μ := by
        apply integral_mono (integrable_of_bdd outer_m1 outer_bdd1)
        · simp_rw [e2]
          exact integrable_of_bdd (hdiag.mul measurable_const)
            (fun x => by rw [abs_mul]; exact mul_le_mul (hG.bdd x x) htr (abs_nonneg _) hC)
        · exact inner
    _ = (tr μ G) ^ 2 := by simp_rw [e2]; rw [integral_mul_const, sq]; rfl

/-- Flux-sector kernel `F⁻(x,y) = (F(x,y) − F(x,Ωy))/2`. -/
noncomputable def minus (F : X → X → ℝ) (Ω : X → X) (x y : X) : ℝ := (F x y - F x (Ω y)) / 2

/-- If `F` commutes with a measurable involution `Ω`, then `F⁻` is again a symmetric bounded measurable kernel. -/
theorem minus_kernel {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) {Ω : X → X} (hΩm : Measurable Ω)
    (hΩ2 : ∀ x, Ω (Ω x) = x) (hinv : ∀ x y, F (Ω x) (Ω y) = F x y) : SymKernel (minus F Ω) B := by
  refine ⟨?_, ?_, ?_⟩
  · unfold minus
    exact ((hF.meas).sub (hF.meas.comp (measurable_fst.prodMk (hΩm.comp measurable_snd)))).div_const 2
  · intro x y; unfold minus
    rw [abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    calc |F x y - F x (Ω y)| ≤ |F x y| + |F x (Ω y)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hF.bdd _ _) (hF.bdd _ _)
      _ = B * 2 := by ring
  · intro x y; unfold minus
    have : F y (Ω x) = F x (Ω y) := by
      rw [← hinv y (Ω x), hΩ2, hF.symm]
    rw [hF.symm x y, this]

/-- With `Ω` measure-preserving as well, the sector projection commutes with composition:
`F⁻ ∘ F⁻ = (F ∘ F)⁻`. So the `e`-sector partition functions are traces of compositions of `F⁻`. -/
theorem comp_minus {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) {Ω : X → X} (hΩm : Measurable Ω)
    (hΩp : MeasurePreserving Ω μ μ) (hΩ2 : ∀ x, Ω (Ω x) = x) (hinv : ∀ x y, F (Ω x) (Ω y) = F x y) (x y : X) :
    comp μ (minus F Ω) (minus F Ω) x y = minus (comp μ F F) Ω x y := by
  let e : X ≃ᵐ X := { toFun := Ω, invFun := Ω, left_inv := hΩ2, right_inv := hΩ2,
                       measurable_toFun := hΩm, measurable_invFun := hΩm }
  have hcv : ∀ g : X → ℝ, ∫ z, g (Ω z) ∂μ = ∫ z, g z ∂μ := fun g =>
    hΩp.integral_comp e.measurableEmbedding g
  have mx : Measurable (F x) := hF.meas.of_uncurry_left
  have mcol : ∀ w, Measurable (fun z => F z w) := fun w => hF.meas.of_uncurry_right
  have B2 : ∀ a b c d : X, |F a b * F c d| ≤ |B| * |B| := fun a b c d => by
    rw [abs_mul]; exact mul_le_mul (le_trans (hF.bdd _ _) (le_abs_self B)) (le_trans (hF.bdd _ _) (le_abs_self B))
      (abs_nonneg _) (abs_nonneg B)
  have j1 : Integrable (fun z => F x z * F z y) μ :=
    integrable_of_bdd (mx.mul (mcol y)) (fun z => B2 _ _ _ _)
  have j2 : Integrable (fun z => F x z * F z (Ω y)) μ :=
    integrable_of_bdd (mx.mul (mcol (Ω y))) (fun z => B2 _ _ _ _)
  have j3 : Integrable (fun z => F x (Ω z) * F z y) μ :=
    integrable_of_bdd ((mx.comp hΩm).mul (mcol y)) (fun z => B2 _ _ _ _)
  have j4 : Integrable (fun z => F x (Ω z) * F z (Ω y)) μ :=
    integrable_of_bdd ((mx.comp hΩm).mul (mcol (Ω y))) (fun z => B2 _ _ _ _)
  have j12 : Integrable (fun z => F x z * F z y - F x z * F z (Ω y)) μ := j1.sub j2
  have j34 : Integrable (fun z => F x (Ω z) * F z y - F x (Ω z) * F z (Ω y)) μ := j3.sub j4
  have eI3 : ∫ z, F x (Ω z) * F z y ∂μ = ∫ z, F x z * F z (Ω y) ∂μ := by
    have := hcv (fun z => F x z * F (Ω z) y)
    simp only [hΩ2] at this; rw [this]; congr 1; ext z
    rw [← hinv (Ω z) y, hΩ2]
  have eI4 : ∫ z, F x (Ω z) * F z (Ω y) ∂μ = ∫ z, F x z * F z y ∂μ := by
    have := hcv (fun z => F x z * F (Ω z) (Ω y))
    simp only [hΩ2] at this; rw [this]; congr 1; ext z; rw [hinv]
  unfold comp minus
  have expand : ∀ z, (F x z - F x (Ω z)) / 2 * ((F z y - F z (Ω y)) / 2) =
      ((F x z * F z y - F x z * F z (Ω y)) - (F x (Ω z) * F z y - F x (Ω z) * F z (Ω y))) / 4 := fun z => by ring
  simp_rw [expand]
  rw [integral_div, integral_sub j12 j34, integral_sub j1 j2, integral_sub j3 j4, eI3, eI4]; ring

/-- **Sector doubling.** With `G = F ∘ F`, `F` symmetric bounded measurable and commuting with a measure-preserving
measurable involution `Ω`, the `e`-sector traces satisfy `Tr((G⁻) ∘ (G⁻)) ≤ (Tr G⁻)²`, i.e. `Z_e(4s) ≤ Z_e(2s)²`
for `F = K_s`. -/
theorem sector_double {F : X → X → ℝ} {B : ℝ} (hF : SymKernel F B) {Ω : X → X} (hΩm : Measurable Ω)
    (hΩp : MeasurePreserving Ω μ μ) (hΩ2 : ∀ x, Ω (Ω x) = x) (hinv : ∀ x y, F (Ω x) (Ω y) = F x y) :
    tr μ (comp μ (minus (comp μ F F) Ω) (minus (comp μ F F) Ω)) ≤ (tr μ (minus (comp μ F F) Ω)) ^ 2 := by
  have hm := minus_kernel hF hΩm hΩ2 hinv
  have e : minus (comp μ F F) Ω = comp μ (minus F Ω) (minus F Ω) := by
    ext x y; exact (comp_minus hF hΩm hΩp hΩ2 hinv x y).symm
  rw [e]; exact trace_double hm

end UnifiedTheory.Clay.YangMills.Twisted.KernelDoubling
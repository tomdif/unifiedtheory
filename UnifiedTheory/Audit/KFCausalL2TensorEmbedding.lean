/- The algebraic Hilbert tensor product embeds isometrically in product L2.
This construction uses the actual product of almost-everywhere classes; no
factorization or completeness of the algebraic tensor product is assumed. -/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalL2TensorEmbedding
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped TensorProduct

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y)

theorem product_memLp (f : X → ℂ) (g : Y → ℂ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : X × Y => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm := hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using hf2.mul_prod hg2

def productState (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (product_memLp μ ν f g (Lp.memLp f) (Lp.memLp g)).toLp
    (fun z : X × Y => f z.1 * g z.2)

theorem productState_coe (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productState μ ν f g =ᵐ[μ.prod ν] fun z => f z.1 * g z.2 :=
  (product_memLp μ ν f g (Lp.memLp f) (Lp.memLp g)).coeFn_toLp

theorem productState_add_left (f f' : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productState μ ν (f + f') g = productState μ ν f g + productState μ ν f' g := by
  apply Lp.ext
  filter_upwards [productState_coe μ ν (f+f') g, productState_coe μ ν f g,
    productState_coe μ ν f' g, Lp.coeFn_add (productState μ ν f g) (productState μ ν f' g),
    (quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f'))] with z h h1 h2 h3 h4
  simp only [h, h3, Pi.add_apply, h1, h2, h4, add_mul]

theorem productState_smul_left (c : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productState μ ν (c • f) g = c • productState μ ν f g := by
  apply Lp.ext
  filter_upwards [productState_coe μ ν (c • f) g, productState_coe μ ν f g,
    Lp.coeFn_smul c (productState μ ν f g),
    (quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c f))] with z h h1 h2 h3
  simp only [h, h2, Pi.smul_apply, h1, h3, smul_eq_mul, mul_assoc]

theorem productState_add_right (f : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    productState μ ν f (g + g') = productState μ ν f g + productState μ ν f g' := by
  apply Lp.ext
  filter_upwards [productState_coe μ ν f (g+g'), productState_coe μ ν f g,
    productState_coe μ ν f g', Lp.coeFn_add (productState μ ν f g) (productState μ ν f g'),
    (quasiMeasurePreserving_snd.ae (Lp.coeFn_add g g'))] with z h h1 h2 h3 h4
  simp only [h, h3, Pi.add_apply, h1, h2, h4, mul_add]

theorem productState_smul_right (c : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productState μ ν f (c • g) = c • productState μ ν f g := by
  apply Lp.ext
  filter_upwards [productState_coe μ ν f (c • g), productState_coe μ ν f g,
    Lp.coeFn_smul c (productState μ ν f g),
    (quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c g))] with z h h1 h2 h3
  simp only [h, h2, Pi.smul_apply, h1, h3, smul_eq_mul]
  ring

theorem productState_inner [SFinite μ] [SFinite ν] (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    inner ℂ (productState μ ν f g) (productState μ ν f' g') =
      inner ℂ f f' * inner ℂ g g' := by
  simp only [L2.inner_def]
  calc
    _ = ∫ z : X × Y, inner ℂ (f z.1) (f' z.1) * inner ℂ (g z.2) (g' z.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [productState_coe μ ν f g, productState_coe μ ν f' g'] with z hz hz'
      simp only [hz, hz', RCLike.inner_apply', map_mul]
      ring
    _ = _ := by
      simpa using integral_prod_mul (μ := μ) (ν := ν)
        (fun x => inner ℂ (f x) (f' x)) (fun y => inner ℂ (g y) (g' y))

def productBilinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) where
  toFun f :=
    { toFun := productState μ ν f
      map_add' := productState_add_right μ ν f
      map_smul' := fun c g => productState_smul_right μ ν c f g }
  map_add' f f' := by apply LinearMap.ext; intro g; exact productState_add_left μ ν f f' g
  map_smul' c f := by apply LinearMap.ext; intro g; exact productState_smul_left μ ν c f g

def tensorMap : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  TensorProduct.lift (productBilinear μ ν)

theorem tensorMap_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    tensorMap μ ν (f ⊗ₜ[ℂ] g) = productState μ ν f g := rfl

theorem tensorMap_inner [SFinite μ] [SFinite ν] (u v : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    inner ℂ (tensorMap μ ν u) (tensorMap μ ν v) = inner ℂ u v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul f' g' => exact productState_inner μ ν f f' g g'
    | add v v' hv hv' => simp only [map_add, inner_add_right, hv, hv']
  | add u u' hu hu' => simp only [map_add, inner_add_left, hu, hu']

def tensorEmbedding [SFinite μ] [SFinite ν] : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (tensorMap μ ν).isometryOfInner (tensorMap_inner μ ν)

theorem tensorEmbedding_tmul [SFinite μ] [SFinite ν] (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    tensorEmbedding μ ν (f ⊗ₜ[ℂ] g) = productState μ ν f g := rfl

#print axioms product_memLp
#print axioms productState_coe
#print axioms productState_add_left
#print axioms productState_smul_left
#print axioms productState_add_right
#print axioms productState_smul_right
#print axioms productState_inner
#print axioms tensorMap_tmul
#print axioms tensorMap_inner
#print axioms tensorEmbedding
#print axioms tensorEmbedding_tmul

end
end UnifiedTheory.Audit.KFCausalL2TensorEmbedding

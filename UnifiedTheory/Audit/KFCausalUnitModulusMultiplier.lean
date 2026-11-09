/- Multiplication by a measurable unit-modulus function on L2.
All representative identities are proved almost everywhere. -/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitModulusMultiplier
noncomputable section
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem product_memLp (m : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1)
    (f : Lp ℂ 2 μ) : MemLp (fun x => m x*f x) 2 μ :=
  (Lp.memLp f).congr_norm (hm.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by rw [norm_mul,hn,one_mul])

def multiply (m : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (product_memLp m hm hn f).toLp (fun x => m x*f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(product_memLp m hm hn (f+g)).coeFn_toLp,
      (product_memLp m hm hn f).coeFn_toLp,(product_memLp m hm hn g).coeFn_toLp,
      Lp.coeFn_add f g,Lp.coeFn_add ((product_memLp m hm hn f).toLp _)
        ((product_memLp m hm hn g).toLp _)] with x hfg hf hg hs ht
    rw [hfg,ht]
    simp only [Pi.add_apply,hf,hg,hs,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(product_memLp m hm hn (c • f)).coeFn_toLp,
      (product_memLp m hm hn f).coeFn_toLp,Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((product_memLp m hm hn f).toLp _)] with x hcf hf hs ht
    simp only [RingHom.id_apply]
    rw [hcf,ht]
    simp only [Pi.smul_apply,hf,hs,smul_eq_mul]
    ring

theorem multiply_coe (m : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1) (f : Lp ℂ 2 μ) :
    multiply m hm hn f =ᵐ[μ] fun x => m x*f x := (product_memLp m hm hn f).coeFn_toLp

theorem multiply_norm (m : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1) (f : Lp ℂ 2 μ) :
    ‖multiply m hm hn f‖ = ‖f‖ := by
  change ‖(product_memLp m hm hn f).toLp (fun x => m x*f x)‖ = ‖f‖
  rw [Lp.norm_toLp,Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by rw [norm_mul,hn,one_mul])

theorem multiply_inverse (m n : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1)
    (hM : Measurable n) (hN : ∀ x, ‖n x‖=1) (hi : ∀ x, n x*m x=1) (f : Lp ℂ 2 μ) :
    multiply n hM hN (multiply m hm hn f) = f := by
  apply Lp.ext
  filter_upwards [multiply_coe n hM hN (multiply m hm hn f),multiply_coe m hm hn f] with x hx hy
  rw [hx,hy,← mul_assoc,hi,one_mul]

def unitary (m : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { toLinearMap := multiply m hm hn
      invFun := multiply (fun x => starRingEnd ℂ (m x)) (Complex.continuous_conj.measurable.comp hm) (fun x => by simpa using hn x)
      left_inv := multiply_inverse m (fun x => starRingEnd ℂ (m x)) hm hn (Complex.continuous_conj.measurable.comp hm)
        (fun x => by simpa using hn x) (fun x => by rw [Complex.conj_mul',hn];norm_num)
      right_inv := multiply_inverse (fun x => starRingEnd ℂ (m x)) m (Complex.continuous_conj.measurable.comp hm)
        (fun x => by simpa using hn x) hm hn (fun x => by rw [Complex.mul_conj',hn];norm_num) }
  norm_map' := multiply_norm m hm hn

theorem unitary_coe (m : X → ℂ) (hm : Measurable m) (hn : ∀ x, ‖m x‖=1) (f : Lp ℂ 2 μ) :
    unitary m hm hn f =ᵐ[μ] fun x => m x*f x := multiply_coe m hm hn f

#print axioms product_memLp
#print axioms multiply
#print axioms multiply_norm
#print axioms multiply_inverse
#print axioms unitary
#print axioms unitary_coe

end
end UnifiedTheory.Audit.KFCausalUnitModulusMultiplier

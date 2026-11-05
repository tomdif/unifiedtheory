/- Every supplied kernel-preserving label equivalence lifts to a genuine
unitary of the constructed Hilbert space. This does not supply spacetime
symmetries, continuity in a group parameter, or a positive energy spectrum. -/
import UnifiedTheory.Clay.YangMills.KernelHilbertCompletion
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.KernelSymmetryUnitary
noncomputable section
open PositiveKernelForm KernelHilbertCompletion

variable {ι : Type*} (K : PositiveKernel ι)

def PreservesKernel (e : Equiv.Perm ι) : Prop :=
  ∀ i j, K.value (e i, e j) = K.value (i, j)

def formalRelabel (e : Equiv.Perm ι) : Formal K ≃ₗ[ℂ] Formal K := Finsupp.domLCongr e

theorem rawForm_relabel (e : Equiv.Perm ι) (he : PreservesKernel K e) (x y : Formal K) :
    rawForm K (formalRelabel K e x) (formalRelabel K e y) = rawForm K x y := by
  change rawForm K (Finsupp.equivMapDomain e x) (Finsupp.equivMapDomain e y) = _
  simp only [rawForm, Finsupp.sum_equivMapDomain]
  apply Finsupp.sum_congr
  intro i hi
  apply Finsupp.sum_congr
  intro j hj
  rw [he i j]

theorem embed_relabel_norm (e : Equiv.Perm ι) (he : PreservesKernel K e) (x : Formal K) :
    ‖embed K (formalRelabel K e x)‖ = ‖embed K x‖ := by
  have hs : ‖embed K (formalRelabel K e x)‖ ^ 2 = ‖embed K x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_embed, inner_embed, rawForm_relabel K e he]
  nlinarith [norm_nonneg (embed K x), norm_nonneg (embed K (formalRelabel K e x))]

/-- The action is extended from the dense finitely supported vectors; it is not
postulated as an additional component of a reconstruction structure. -/
def kernelUnitary (e : Equiv.Perm ι) (he : PreservesKernel K e) : Hilbert K ≃ₗᵢ[ℂ] Hilbert K :=
  (formalRelabel K e).extendOfIsometry (embed K).toLinearMap (embed K).toLinearMap
    (denseRange_embed K) (denseRange_embed K) (embed_relabel_norm K e he)

theorem kernelUnitary_embed (e : Equiv.Perm ι) (he : PreservesKernel K e) (x : Formal K) :
    kernelUnitary K e he (embed K x) = embed K (formalRelabel K e x) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

@[simp] theorem kernelUnitary_canonical (e : Equiv.Perm ι) (he : PreservesKernel K e) (i : ι) :
    kernelUnitary K e he (canonical K i) = canonical K (e i) := by
  unfold canonical
  rw [kernelUnitary_embed]
  exact congrArg (embed K) (Finsupp.domLCongr_single e i (1 : ℂ))

theorem kernelUnitary_vacuum (e : Equiv.Perm ι) (he : PreservesKernel K e) (unitIndex : ι)
    (hunit : e unitIndex = unitIndex) :
    kernelUnitary K e he (vacuum K unitIndex) = vacuum K unitIndex := by
  simp only [vacuum, kernelUnitary_canonical, hunit]

def kernelSymmetries : Subgroup (Equiv.Perm ι) where
  carrier := {e | PreservesKernel K e}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro e f he hf i j
    exact (he (f i) (f j)).trans (hf i j)
  inv_mem' := by
    intro e he i j
    simpa using (he (e.symm i) (e.symm j)).symm

theorem formalRelabel_one (x : Formal K) : formalRelabel K 1 x = x := by
  apply Finsupp.ext
  intro i
  rfl

theorem formalRelabel_mul (e f : Equiv.Perm ι) (x : Formal K) :
    formalRelabel K (e * f) x = formalRelabel K e (formalRelabel K f x) := by
  apply Finsupp.ext
  intro i
  rfl

theorem kernelUnitary_one : kernelUnitary K 1 (kernelSymmetries K).one_mem = 1 := by
  apply DFunLike.coe_injective
  exact (denseRange_embed K).equalizer (kernelUnitary K 1 _).continuous continuous_id (by
    funext x
    simp only [Function.comp_apply]
    rw [kernelUnitary_embed, formalRelabel_one]
    rfl)

theorem kernelUnitary_mul (e f : kernelSymmetries K) :
    kernelUnitary K (e * f).val (e * f).property =
      kernelUnitary K e.val e.property * kernelUnitary K f.val f.property := by
  apply DFunLike.coe_injective
  exact (denseRange_embed K).equalizer (kernelUnitary K (e * f).val _).continuous
    ((kernelUnitary K e.val _).continuous.comp (kernelUnitary K f.val _).continuous) (by
      funext x
      simp only [Function.comp_apply]
      change kernelUnitary K (e * f).val _ (embed K x) =
        kernelUnitary K e.val _ (kernelUnitary K f.val _ (embed K x))
      rw [kernelUnitary_embed, kernelUnitary_embed, kernelUnitary_embed]
      exact congrArg (embed K) (formalRelabel_mul K e.val f.val x))

/-- The entire group of kernel symmetries has a constructed unitary
representation. A physical symmetry identification needs further input. -/
def kernelRepresentation : kernelSymmetries K →* (Hilbert K ≃ₗᵢ[ℂ] Hilbert K) where
  toFun e := kernelUnitary K e.val e.property
  map_one' := kernelUnitary_one K
  map_mul' := kernelUnitary_mul K

end
end UnifiedTheory.Clay.YangMills.KernelSymmetryUnitary

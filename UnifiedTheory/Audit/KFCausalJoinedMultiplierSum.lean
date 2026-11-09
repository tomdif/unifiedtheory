/- Pointwise multiplier sums on actual joined L2 tensor states. -/
import UnifiedTheory.Audit.KFCausalJoinedFourierProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalJoinedMultiplierSum
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalHermiteProductBasis (joinCoordinates)
open KFCausalL2TensorEmbedding (productState)
open KFCausalJoinedFourierProduct

def joinProduct (n m : ℕ) (f : BlockHilbert n) (g : BlockHilbert m) : BlockHilbert (n+m) :=
  joinCoordinates n m (productState volume volume f g)

theorem sum_coe (n m : ℕ) (f f' : BlockHilbert n) (g g' : BlockHilbert m)
    (a : Block n → ℂ) (b : Block m → ℂ)
    (hf : f' =ᵐ[volume] fun x => a x*f x) (hg : g' =ᵐ[volume] fun y => b y*g y) :
    joinProduct n m f' g + joinProduct n m f g' =ᵐ[volume]
      fun z => (a (separate n m z).1+b (separate n m z).2)*(joinProduct n m f g) z := by
  filter_upwards [Lp.coeFn_add (joinProduct n m f' g) (joinProduct n m f g'),
    join_product_coe n m f' g, join_product_coe n m f g', join_product_coe n m f g,
    (Measure.quasiMeasurePreserving_fst.comp (separate_preserves n m).quasiMeasurePreserving).ae hf,
    (Measure.quasiMeasurePreserving_snd.comp (separate_preserves n m).quasiMeasurePreserving).ae hg]
      with z hs h1 h2 h3 hf' hg'
  simp only [Function.comp_apply] at hf' hg'
  change (joinProduct n m f' g + joinProduct n m f g') z = _
  rw [hs]
  change (joinCoordinates n m (productState volume volume f' g)) z+
    (joinCoordinates n m (productState volume volume f g')) z = _
  change (joinCoordinates n m (productState volume volume f g)) z = _ at h3
  rw [h1, h2, hf', hg']
  change _ = _*(joinCoordinates n m (productState volume volume f g)) z
  rw [h3]
  ring

theorem fourier (n m : ℕ) (f : BlockHilbert n) (g : BlockHilbert m) :
    (Lp.fourierTransformₗᵢ (Block (n+m)) ℂ) (joinProduct n m f g) =
      joinProduct n m ((Lp.fourierTransformₗᵢ (Block n) ℂ) f)
        ((Lp.fourierTransformₗᵢ (Block m) ℂ) g) := join_fourier_product n m f g

#print axioms sum_coe
#print axioms fourier
end
end UnifiedTheory.Audit.KFCausalJoinedMultiplierSum

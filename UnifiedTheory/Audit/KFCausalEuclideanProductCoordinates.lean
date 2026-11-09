/- Splitting a Euclidean coordinate set into two blocks preserves volume,
splits the Fourier phase, and gives the actual product-L2 pullback. -/
import UnifiedTheory.Audit.KFCausalL2TensorEmbedding
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open scoped TensorProduct

variable (n m : ℕ)
abbrev Block (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Joint (n m : ℕ) := EuclideanSpace ℝ (Fin n ⊕ Fin m)
abbrev BlockHilbert (n : ℕ) := Lp ℂ 2 (volume : Measure (Block n))
abbrev ProductHilbert (n m : ℕ) := Lp ℂ 2 (volume : Measure (Block n × Block m))
abbrev JointHilbert (n m : ℕ) := Lp ℂ 2 (volume : Measure (Joint n m))

def split : Joint n m ≃ᵐ (Block n × Block m) :=
  (MeasurableEquiv.toLp 2 ((Fin n ⊕ Fin m) → ℝ)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).trans
      ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).prodCongr
        (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

theorem split_preserves_volume : MeasurePreserving (split n m) :=
  (((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).symm.prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ))).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n ⊕ Fin m))

theorem split_fst (x : Joint n m) (i : Fin n) : (split n m x).1 i = x (.inl i) := rfl
theorem split_snd (x : Joint n m) (i : Fin m) : (split n m x).2 i = x (.inr i) := rfl

theorem inner_split (x k : Joint n m) :
    inner ℝ x k = inner ℝ (split n m x).1 (split n m k).1 +
      inner ℝ (split n m x).2 (split n m k).2 := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, split_fst, split_snd]

def coordinates : ProductHilbert n m ≃ₗᵢ[ℂ] JointHilbert n m :=
  unitaryPullback (split n m) (split_preserves_volume n m)

theorem coordinates_coe (f : ProductHilbert n m) :
    coordinates n m f =ᵐ[volume] f ∘ split n m :=
  unitaryPullback_coe _ _ _

theorem productState_functions_coe (f : Block n → ℂ) (g : Block m → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    productState volume volume (hf.toLp f) (hg.toLp g) =ᵐ[volume]
      fun z : Block n × Block m => f z.1 * g z.2 := by
  filter_upwards [productState_coe volume volume (hf.toLp f) (hg.toLp g),
    quasiMeasurePreserving_fst.ae hf.coeFn_toLp,
    quasiMeasurePreserving_snd.ae hg.coeFn_toLp] with z hz h1 h2
  exact hz.trans (congrArg₂ (· * ·) h1 h2)

theorem coordinates_product_coe (f : Block n → ℂ) (g : Block m → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    coordinates n m (productState volume volume (hf.toLp f) (hg.toLp g)) =ᵐ[volume]
      fun x => f (split n m x).1 * g (split n m x).2 := by
  filter_upwards [coordinates_coe n m (productState volume volume (hf.toLp f) (hg.toLp g)),
    (split_preserves_volume n m).quasiMeasurePreserving.ae
      (productState_functions_coe n m f g hf hg)] with x hx hprod
  exact hx.trans hprod

#print axioms split_preserves_volume
#print axioms split_fst
#print axioms split_snd
#print axioms inner_split
#print axioms coordinates
#print axioms coordinates_coe
#print axioms productState_functions_coe
#print axioms coordinates_product_coe

end
end UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates

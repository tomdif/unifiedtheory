/- Tensor products of the derived scalar Hermite basis give actual complete
two- and four-dimensional Euclidean Hilbert bases. -/
import UnifiedTheory.Audit.KFCausalHermiteHilbertBasis
import UnifiedTheory.Audit.KFCausalProductHilbertExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalHermiteProductBasis
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalMeasureUnitaryPullback (unitaryPullback)
open KFCausalProductHilbertExpansion (productBasis productBasis_apply)

def mapBasis {ι H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ H) (U : H ≃ₗᵢ[ℂ] K) : HilbertBasis ι ℂ K :=
  ⟨U.symm.trans b.repr⟩

theorem mapBasis_apply {ι H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ H) (U : H ≃ₗᵢ[ℂ] K) (i : ι) : mapBasis b U i = U (b i) := by
  classical
  change U (b.repr.symm (lp.single 2 i 1)) = U (b i)
  rw [b.repr_symm_single]

def lineEquiv : Block 1 ≃ₗ[ℝ] ℝ where
  toFun x := x 0
  invFun x := WithLp.toLp 2 (fun _ => x)
  left_inv x := by ext i; fin_cases i; rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def lineIsometry : Block 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := lineEquiv
  norm_map' := (lineEquiv.toLinearMap.isometryOfInner (fun x y => by
    simp [lineEquiv,PiLp.inner_apply])).norm_map

def lineCoordinates : KFCausalGaussianPolynomialTotality.ScalarHilbert ≃ₗᵢ[ℂ] BlockHilbert 1 :=
  unitaryPullback lineIsometry.toMeasurableEquiv lineIsometry.measurePreserving

def mergeIsometry (n m : ℕ) : Joint n m ≃ₗᵢ[ℝ] Block (n+m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv

def joinCoordinates (n m : ℕ) : ProductHilbert n m ≃ₗᵢ[ℂ] BlockHilbert (n+m) :=
  (coordinates n m).trans
    (unitaryPullback (mergeIsometry n m).toMeasurableEquiv (mergeIsometry n m).measurePreserving).symm

def lineBasis (a : ℝ) (ha : 0 < a) : HilbertBasis ℕ ℂ (BlockHilbert 1) :=
  mapBasis (KFCausalHermiteHilbertBasis.basis a ha) lineCoordinates

def planeBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HilbertBasis (ℕ × ℕ) ℂ (BlockHilbert 2) :=
  mapBasis (productBasis 1 1 (lineBasis a ha) (lineBasis b hb)) (joinCoordinates 1 1)

abbrev Index := (ℕ × ℕ) × (ℕ × ℕ)

/-- The same two widths are used in each charged plane. -/
def chargedBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HilbertBasis Index ℂ (BlockHilbert 4) :=
  mapBasis (productBasis 2 2 (planeBasis a b ha hb) (planeBasis a b ha hb)) (joinCoordinates 2 2)

theorem planeBasis_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i j : ℕ) :
    planeBasis a b ha hb (i,j) = joinCoordinates 1 1
      (KFCausalL2TensorEmbedding.productState volume volume (lineBasis a ha i) (lineBasis b hb j)) := by
  rw [planeBasis,mapBasis_apply,productBasis_apply]

theorem chargedBasis_apply (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (i j : ℕ × ℕ) :
    chargedBasis a b ha hb (i,j) = joinCoordinates 2 2
      (KFCausalL2TensorEmbedding.productState volume volume
        (planeBasis a b ha hb i) (planeBasis a b ha hb j)) := by
  rw [chargedBasis,mapBasis_apply,productBasis_apply]

theorem charged_expansion (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : BlockHilbert 4) :
    HasSum (fun i => inner ℂ (chargedBasis a b ha hb i) f • chargedBasis a b ha hb i) f := by
  simpa only [HilbertBasis.repr_apply_apply] using (chargedBasis a b ha hb).hasSum_repr f

#print axioms mapBasis_apply
#print axioms lineIsometry
#print axioms chargedBasis
#print axioms planeBasis_apply
#print axioms chargedBasis_apply
#print axioms charged_expansion
end
end UnifiedTheory.Audit.KFCausalHermiteProductBasis

/- Complete product bases and partial Hilbert expansions on actual product L2.
Surjectivity follows from the proved Euclidean product density. -/
import UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalProductHilbertExpansion
noncomputable section
open MeasureTheory
open scoped ENNReal
open KFCausalEuclideanProductCoordinates
open KFCausalL2TensorEmbedding
open KFCausalWeightedTensorRepresentative (leftProduct rightProduct closed_submodule_total)
open KFCausalProductPhaseTranslation (product_norm)

theorem basis_closed_total {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (S : Submodule ℂ H) (hS : IsClosed (S : Set H))
    (hb : ∀ i, b i ∈ S) : S = ⊤ := by
  apply top_unique
  rw [← b.dense_span]
  exact Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hb i)) hS

variable {ι κ : Type*} (n m : ℕ)

def column (b : HilbertBasis ι ℂ (BlockHilbert n)) (i : ι) :
    BlockHilbert m →ₗᵢ[ℂ] ProductHilbert n m where
  toLinearMap := (productBilinear volume volume) (b i)
  norm_map' g := by
    change ‖productState volume volume (b i) g‖ = ‖g‖
    rw [product_norm,b.orthonormal.1 i,one_mul]

theorem column_apply (b : HilbertBasis ι ℂ (BlockHilbert n)) (i : ι) (g : BlockHilbert m) :
    column n m b i g = productState volume volume (b i) g := rfl

theorem column_orthogonal (b : HilbertBasis ι ℂ (BlockHilbert n)) :
    OrthogonalFamily ℂ (fun _ : ι => BlockHilbert m) (column n m b) := by
  intro i j hij g h
  change inner ℂ (productState volume volume (b i) g) (productState volume volume (b j) h) = 0
  rw [productState_inner,b.orthonormal.2 hij,zero_mul]

theorem column_total (b : HilbertBasis ι ℂ (BlockHilbert n)) :
    (⨆ i, (column n m b i).toLinearMap.range).topologicalClosure = ⊤ := by
  let S := (⨆ i, (column n m b i).toLinearMap.range).topologicalClosure
  have hS : IsClosed (S : Set (ProductHilbert n m)) := Submodule.isClosed_topologicalClosure _
  apply closed_submodule_total n m id id denseRange_id denseRange_id S hS
  intro g h
  let U := S.comap (leftProduct n m h).toLinearMap
  have hU : U = ⊤ := basis_closed_total b U
    (hS.preimage (leftProduct n m h).continuous) (fun i => by
      apply Submodule.le_topologicalClosure
      exact Submodule.mem_iSup_of_mem i ⟨h,rfl⟩)
  have hg : g ∈ U := by rw [hU]; trivial
  exact hg

def hilbertSum (b : HilbertBasis ι ℂ (BlockHilbert n)) :
    IsHilbertSum ℂ (fun _ : ι => BlockHilbert m) (column n m b) :=
  IsHilbertSum.mk (column_orthogonal n m b) (by rw [column_total])

/-- A partial expansion; all spectator coordinates remain in actual L2. -/
def partialTransform (b : HilbertBasis ι ℂ (BlockHilbert n)) :
    ProductHilbert n m ≃ₗᵢ[ℂ] ℓ²(ι,BlockHilbert m) :=
  (hilbertSum n m b).linearIsometryEquiv

theorem partialTransform_column [DecidableEq ι]
    (b : HilbertBasis ι ℂ (BlockHilbert n)) (i : ι) (g : BlockHilbert m) :
    partialTransform n m b (productState volume volume (b i) g) = lp.single 2 i g := by
  apply (partialTransform n m b).symm.injective
  exact ((partialTransform n m b).symm_apply_apply _).trans
    ((hilbertSum n m b).linearIsometryEquiv_symm_apply_single g).symm

theorem expansion (b : HilbertBasis ι ℂ (BlockHilbert n)) (f : ProductHilbert n m) :
    HasSum (fun i => productState volume volume (b i) (partialTransform n m b f i)) f := by
  simpa only [LinearIsometryEquiv.symm_apply_apply,column_apply,partialTransform] using
    (hilbertSum n m b).hasSum_linearIsometryEquiv_symm (partialTransform n m b f)

theorem coefficient_inner (b : HilbertBasis ι ℂ (BlockHilbert n)) (i : ι)
    (g : BlockHilbert m) (f : ProductHilbert n m) :
    inner ℂ (productState volume volume (b i) g) f =
      inner ℂ g (partialTransform n m b f i) := by
  classical
  have he := (partialTransform n m b).inner_map_map (productState volume volume (b i) g) f
  rw [partialTransform_column,lp.inner_single_left] at he
  exact he.symm

theorem partialTransform_product (b : HilbertBasis ι ℂ (BlockHilbert n))
    (f : BlockHilbert n) (g : BlockHilbert m) (i : ι) :
    partialTransform n m b (productState volume volume f g) i = inner ℂ (b i) f • g := by
  apply ext_inner_left ℂ
  intro v
  rw [← coefficient_inner,productState_inner,inner_smul_right]

def lpCoordinate {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (i : ι) : ℓ²(ι,H) →L[ℂ] H :=
  ({ toFun := fun f => f i
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : ℓ²(ι,H) →ₗ[ℂ] H).mkContinuous 1
    (fun f => by simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) f i)

/-- The actual convergent coefficient action of any two factor unitaries. -/
theorem partialTransform_lift (b : HilbertBasis ι ℂ (BlockHilbert n))
    (U : BlockHilbert n ≃ₗᵢ[ℂ] BlockHilbert n) (V : BlockHilbert m ≃ₗᵢ[ℂ] BlockHilbert m)
    (f : ProductHilbert n m) (i : ι) :
    HasSum (fun j => inner ℂ (b i) (U (b j)) • V (partialTransform n m b f j))
      (partialTransform n m b (KFCausalEuclideanTensorUnitary.liftUnitary n m U V f) i) := by
  let L := (lpCoordinate i).comp ((partialTransform n m b).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (KFCausalEuclideanTensorUnitary.liftUnitary n m U V).toContinuousLinearEquiv.toContinuousLinearMap)
  have hs := L.hasSum (expansion n m b f)
  convert hs using 1
  funext j
  change _ = partialTransform n m b
    (KFCausalEuclideanTensorUnitary.liftUnitary n m U V (productState volume volume (b j) _)) i
  rw [KFCausalEuclideanTensorUnitary.liftUnitary_product,partialTransform_product]

theorem product_orthonormal (b : HilbertBasis ι ℂ (BlockHilbert n))
    (c : HilbertBasis κ ℂ (BlockHilbert m)) :
    Orthonormal ℂ (fun i : ι × κ => productState volume volume (b i.1) (c i.2)) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i,j⟩ ⟨k,l⟩
  rw [productState_inner,orthonormal_iff_ite.mp b.orthonormal,
    orthonormal_iff_ite.mp c.orthonormal]
  by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi,hj]

theorem product_total (b : HilbertBasis ι ℂ (BlockHilbert n))
    (c : HilbertBasis κ ℂ (BlockHilbert m)) :
    (Submodule.span ℂ (Set.range (fun i : ι × κ =>
      productState volume volume (b i.1) (c i.2)))).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℂ (Set.range (fun i : ι × κ =>
    productState volume volume (b i.1) (c i.2)))).topologicalClosure
  have hS : IsClosed (S : Set (ProductHilbert n m)) := Submodule.isClosed_topologicalClosure _
  have hi (i : ι) (g : BlockHilbert m) : productState volume volume (b i) g ∈ S := by
    let U := S.comap (rightProduct n m (b i)).toLinearMap
    have hU : U = ⊤ := basis_closed_total c U
      (hS.preimage (rightProduct n m (b i)).continuous) (fun j =>
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i,j),rfl⟩))
    have hg : g ∈ U := by rw [hU]; trivial
    exact hg
  apply closed_submodule_total n m id id denseRange_id denseRange_id S hS
  intro f g
  let U := S.comap (leftProduct n m g).toLinearMap
  have hU : U = ⊤ := basis_closed_total b U
    (hS.preimage (leftProduct n m g).continuous) (fun i => hi i g)
  have hf : f ∈ U := by rw [hU]; trivial
  exact hf

def productBasis (b : HilbertBasis ι ℂ (BlockHilbert n))
    (c : HilbertBasis κ ℂ (BlockHilbert m)) : HilbertBasis (ι × κ) ℂ (ProductHilbert n m) :=
  HilbertBasis.mk (product_orthonormal n m b c) (by rw [product_total])

theorem productBasis_apply (b : HilbertBasis ι ℂ (BlockHilbert n))
    (c : HilbertBasis κ ℂ (BlockHilbert m)) (i : ι × κ) :
    productBasis n m b c i = productState volume volume (b i.1) (c i.2) :=
  congrFun (HilbertBasis.coe_mk _ _) i

#print axioms column_total
#print axioms partialTransform
#print axioms partialTransform_column
#print axioms expansion
#print axioms product_total
#print axioms productBasis
end
end UnifiedTheory.Audit.KFCausalProductHilbertExpansion

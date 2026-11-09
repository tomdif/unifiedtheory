/- Weighted representative identities on tensor tests with dense factor
classes extend to all product L2. Linearity and sequential closedness are
proved using the actual preservation of null sets and L2 convergence. -/
import UnifiedTheory.Audit.KFCausalPartialFourier
import UnifiedTheory.Audit.KFCausalProductPhaseTranslation
import UnifiedTheory.Audit.KFCausalWeightedLpRepresentative
import Mathlib.MeasureTheory.Integral.CompactlySupported

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative
noncomputable section
open MeasureTheory Filter
open scoped Topology CompactlySupported ENNReal
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalEuclideanTensorDensity (tensorEmbedding_dense)
open UnifiedTheory.Audit.KFCausalProductPhaseTranslation (product_norm)
open UnifiedTheory.Audit.KFCausalWeightedLpRepresentative (weighted_representative_limit)

variable (n m : ℕ)

def leftProduct (b : BlockHilbert m) : BlockHilbert n →L[ℂ] ProductHilbert n m :=
  ((productBilinear volume volume).flip b).mkContinuous ‖b‖ (fun a => by
    change ‖productState volume volume a b‖ ≤ ‖b‖*‖a‖
    rw [product_norm,mul_comm])

def rightProduct (a : BlockHilbert n) : BlockHilbert m →L[ℂ] ProductHilbert n m :=
  (productBilinear volume volume a).mkContinuous ‖a‖ (fun b => by
    change ‖productState volume volume a b‖ ≤ ‖a‖*‖b‖
    rw [product_norm])

theorem closed_submodule_total {A B : Type*} (j : A → BlockHilbert n) (k : B → BlockHilbert m)
    (hj : DenseRange j) (hk : DenseRange k) (S : Submodule ℂ (ProductHilbert n m))
    (hS : IsClosed (S : Set (ProductHilbert n m)))
    (hp : ∀ a b, productState volume volume (j a) (k b) ∈ S) : S = ⊤ := by
  have hleft : ∀ a b, productState volume volume a (k b) ∈ S := by
    intro a b
    have hc : IsClosed {a : BlockHilbert n | productState volume volume a (k b) ∈ S} :=
      hS.preimage (leftProduct n m (k b)).continuous
    exact (closure_minimal (by rintro _ ⟨a,rfl⟩; exact hp a b) hc) (hj a)
  have hall : ∀ a b, productState volume volume a b ∈ S := by
    intro a b
    have hc : IsClosed {b : BlockHilbert m | productState volume volume a b ∈ S} :=
      hS.preimage (rightProduct n m a).continuous
    exact (closure_minimal (by rintro _ ⟨b,rfl⟩; exact hleft a b) hc) (hk b)
  have hr : Set.range (tensorEmbedding (volume : Measure (Block n)) (volume : Measure (Block m))) ⊆ S := by
    rintro _ ⟨w,rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using S.zero_mem
    | tmul a b => exact hall a b
    | add w z hw hz => simpa only [map_add] using S.add_mem hw hz
  apply top_unique
  intro f _
  exact (closure_minimal hr hS) (tensorEmbedding_dense n m f)

variable (U : ProductHilbert n m →L[ℂ] ProductHilbert n m)
  (e : Block n × Block m → Block n × Block m)
  (he : Measure.QuasiMeasurePreserving e volume volume) (w : Block n × Block m → ℂ)

def representativeSpace : Submodule ℂ (ProductHilbert n m) where
  carrier := {f | U f =ᵐ[volume] fun x => w x*f (e x)}
  zero_mem' := by
    change U 0 =ᵐ[volume] fun x => w x*(0 : ProductHilbert n m) (e x)
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 volume,he.ae (Lp.coeFn_zero ℂ 2 volume)] with x hx he'
    rw [hx,he']
    simp
  add_mem' := by
    intro f g hf hg
    change U (f+g) =ᵐ[volume] fun x => w x*(f+g) (e x)
    rw [map_add]
    filter_upwards [Lp.coeFn_add (U f) (U g),he.ae (Lp.coeFn_add f g),hf,hg] with x hu hs hf hg
    rw [hu,hs]
    simp only [Pi.add_apply,hf,hg,mul_add]
  smul_mem' := by
    intro c f hf
    change U (c • f) =ᵐ[volume] fun x => w x*(c • f) (e x)
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (U f),he.ae (Lp.coeFn_smul c f),hf] with x hu hs hf
    rw [hu,hs]
    simp only [Pi.smul_apply,smul_eq_mul,hf]
    ring

theorem representativeSpace_closed : IsClosed (representativeSpace n m U e he w : Set (ProductHilbert n m)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro f f₀ hf hlim
  exact weighted_representative_limit e he w f (fun i => U (f i)) f₀ (U f₀)
    hlim ((U.continuous.tendsto f₀).comp hlim) hf

include he in
theorem tensor_representative {A B : Type*} (j : A → BlockHilbert n) (k : B → BlockHilbert m)
    (hj : DenseRange j) (hk : DenseRange k)
    (hp : ∀ a b, U (productState volume volume (j a) (k b)) =ᵐ[volume]
      fun x => w x*(productState volume volume (j a) (k b)) (e x)) (f : ProductHilbert n m) :
    U f =ᵐ[volume] fun x => w x*f (e x) := by
  have hs := closed_submodule_total n m j k hj hk (representativeSpace n m U e he w)
    (representativeSpace_closed n m U e he w) hp
  have hf : f ∈ representativeSpace n m U e he w := by rw [hs]; trivial
  exact hf

def testState (a : C_c(Block n, ℂ)) : BlockHilbert n :=
  (a.continuous.memLp_of_hasCompactSupport a.hasCompactSupport).toLp a

theorem testState_dense : DenseRange (testState n) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun δ hδ => ?_
  obtain ⟨g,hgs,hgn,hgc,hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) hδ.ne'
  let G : C_c(Block n, ℂ) := ⟨⟨g,hgc⟩,hgs⟩
  refine ⟨testState n G,⟨G,rfl⟩,?_⟩
  change testState n G ∈ Metric.closedEBall f δ
  rw [Metric.mem_closedEBall']
  change edist f ((G.continuous.memLp_of_hasCompactSupport G.hasCompactSupport).toLp G) ≤ δ
  rw [← Lp.toLp_coeFn f (Lp.memLp f),Lp.edist_toLp_toLp]
  exact hgn

#print axioms closed_submodule_total
#print axioms representativeSpace_closed
#print axioms tensor_representative
#print axioms testState_dense

end
end UnifiedTheory.Audit.KFCausalWeightedTensorRepresentative

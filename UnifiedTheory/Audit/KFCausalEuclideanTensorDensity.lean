/- Density of finite sums of product L2 states in every Euclidean product
space. The proof uses compact packets covering space and Fourier uniqueness;
the tensor-product density is a conclusion, not an input assumption. -/
import UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
import UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanTensorDensity
noncomputable section
open MeasureTheory
open scoped TensorProduct ContDiff
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness

def bump (n j : ℕ) : ContDiffBump (0 : Block n) where
  rIn := (j : ℝ) + 1
  rOut := (j : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def base (n j : ℕ) (x : Block n) : ℂ := (bump n j x : ℝ)

theorem base_compact (n j : ℕ) : HasCompactSupport (base n j) :=
  (bump n j).hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 from rfl)

theorem base_smooth (n j : ℕ) : ContDiff ℝ ∞ (base n j) :=
  Complex.ofRealCLM.contDiff.comp (bump n j).contDiff

def packet (n j : ℕ) : SchwartzMap (Block n) ℂ :=
  (base_compact n j).toSchwartzMap (base_smooth n j)

theorem packet_one (n j : ℕ) (x : Block n) (hx : ‖x‖ ≤ (j : ℝ) + 1) :
    packet n j x = 1 := by
  change (bump n j x : ℂ) = 1
  rw [(bump n j).one_of_mem_closedBall]
  · rfl
  · simpa only [Metric.mem_closedBall, dist_zero_right, bump] using hx

theorem pair_packet_cover (n m : ℕ) (x : Block n) (y : Block m) :
    ∃ j : ℕ, packet n j x = 1 ∧ packet m j y = 1 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max ‖x‖ ‖y‖)
  refine ⟨j, packet_one n j x ?_, packet_one m j y ?_⟩
  · have := le_max_left ‖x‖ ‖y‖; linarith
  · have := le_max_right ‖x‖ ‖y‖; linarith

theorem modulate_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (w : E → ℂ) (hw : MemLp w 2) (k : E) : MemLp (modulate k w) 2 := by
  have hm : AEStronglyMeasurable (modulate k w) volume :=
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable).mul hw.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [modulate, norm_mul, Circle.norm_coe, one_mul] using
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw

def pairFunction (n m : ℕ) (f : Block n → ℂ) (g : Block m → ℂ) (x : Joint n m) : ℂ :=
  f (split n m x).1 * g (split n m x).2

theorem pair_memLp (n m : ℕ) (f : Block n → ℂ) (g : Block m → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) : MemLp (pairFunction n m f g) 2 :=
  (product_memLp volume volume f g hf hg).comp_measurePreserving (split_preserves_volume n m)

theorem modulate_pair (n m : ℕ) (f : Block n → ℂ) (g : Block m → ℂ) (k : Joint n m) :
    modulate k (pairFunction n m f g) =
      pairFunction n m (modulate (split n m k).1 f) (modulate (split n m k).2 g) := by
  funext x
  simp only [modulate, pairFunction, inner_split, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem zero_of_orthogonal_products (n m : ℕ) (f : ProductHilbert n m)
    (ho : ∀ (g : BlockHilbert n) (h : BlockHilbert m),
      inner ℂ (productState volume volume g h) f = 0) : f = 0 := by
  apply (coordinates n m).injective
  rw [map_zero]
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hz (j : ℕ) :
      (fun x => star (pairFunction n m (packet n j) (packet m j) x) *
        coordinates n m f x) =ᵐ[volume] 0 := by
    apply weighted_zero_of_orthogonal_modulations _ _
      (pair_memLp n m _ _ ((packet n j).memLp 2 volume) ((packet m j).memLp 2 volume))
      (Lp.memLp (coordinates n m f))
    intro k
    rw [modulate_pair]
    let g := modulate (split n m k).1 (packet n j)
    let h := modulate (split n m k).2 (packet m j)
    have hg : MemLp g 2 := modulate_memLp _ ((packet n j).memLp 2 volume) _
    have hh : MemLp h 2 := modulate_memLp _ ((packet m j).memLp 2 volume) _
    have he := (coordinates n m).inner_map_map (productState volume volume (hg.toLp g) (hh.toLp h)) f
    rw [ho] at he
    rw [L2.inner_def] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [coordinates_product_coe n m g h hg hh] with x hx
    change star (g (split n m x).1 * h (split n m x).2) * coordinates n m f x = _
    rw [hx, RCLike.inner_apply']
    rfl
  filter_upwards [ae_all_iff.mpr hz] with x hx
  obtain ⟨j, hj1, hj2⟩ := pair_packet_cover n m (split n m x).1 (split n m x).2
  have hj := hx j
  simpa only [pairFunction, hj1, hj2, mul_one, star_one, one_mul, Pi.zero_apply] using hj

theorem tensorEmbedding_dense (n m : ℕ) :
    DenseRange (tensorEmbedding (volume : Measure (Block n)) (volume : Measure (Block m))) := by
  have hc : (LinearMap.range (tensorMap (volume : Measure (Block n))
      (volume : Measure (Block m)))).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro f hf
    apply zero_of_orthogonal_products n m f
    intro g h
    exact Submodule.inner_right_of_mem_orthogonal
      (show productState volume volume g h ∈ LinearMap.range
        (tensorMap (volume : Measure (Block n)) (volume : Measure (Block m))) from
          ⟨g ⊗ₜ[ℂ] h, rfl⟩) hf
  intro f
  have hm : f ∈ (LinearMap.range (tensorMap (volume : Measure (Block n))
      (volume : Measure (Block m)))).topologicalClosure := by rw [hc]; trivial
  exact hm

#print axioms base_compact
#print axioms base_smooth
#print axioms packet_one
#print axioms pair_packet_cover
#print axioms modulate_memLp
#print axioms pair_memLp
#print axioms modulate_pair
#print axioms zero_of_orthogonal_products
#print axioms tensorEmbedding_dense

end
end UnifiedTheory.Audit.KFCausalEuclideanTensorDensity

/- Product totality for any nowhere-zero L2 clock weight. This allows
clock dressing without assuming that an unbounded map preserves density. -/
import UnifiedTheory.Audit.KFCausalCoupledTrialDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalWeightedProductTotality
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCompactTransverseModulation
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates

theorem modulate_memLp (w : ℝ → ℂ) (hw : MemLp w 2) (p : ℝ) : MemLp (modulate p w) 2 := by
  have hm : AEStronglyMeasurable (modulate p w) volume :=
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hw.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [modulate_norm] using (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw

theorem product_modulate (w : ℝ → ℂ) (n : ℕ) (k : Space) :
    KFCausalEuclideanFourierUniqueness.modulate k (productFunction w (packet n)) =
      productFunction (modulate (k 0) w) (modulatedPacket n (tail k)) := by
  funext x
  simp only [KFCausalEuclideanFourierUniqueness.modulate,product_apply,modulatedPacket_apply,
    modulate,inner_split,AddChar.map_add_eq_mul,Circle.coe_mul]
  rw [mul_comm (k 0) (x 0)]
  ring

theorem ae_zero_of_orthogonal_products (w : ℝ → ℂ) (hw : MemLp w 2) (hnw : ∀ q, w q ≠ 0)
    (f : Space → ℂ) (hf : MemLp f 2)
    (ho : ∀ (p : ℝ) (ψ : SchwartzMap TailSpace ℂ),
      (∫ x, star (productFunction (modulate p w) ψ x)*f x)=0) : f =ᵐ[volume] 0 := by
  have hn (n : ℕ) : (fun x => star (productFunction w (packet n) x)*f x) =ᵐ[volume] 0 := by
    apply KFCausalEuclideanFourierUniqueness.weighted_zero_of_orthogonal_modulations _ f
      (product_memLp _ _ hw ((packet n).memLp 2 volume)) hf
    intro k
    rw [product_modulate]
    exact ho (k 0) (modulatedPacket n (tail k))
  filter_upwards [ae_all_iff.mpr hn] with x hx
  obtain ⟨n,hp⟩ := packet_cover (tail x)
  have hz := hx n
  simp only [product_apply,hp,mul_one,Pi.zero_apply] at hz
  exact (mul_eq_zero.mp hz).resolve_left (star_ne_zero.mpr (hnw (x 0)))

def euclideanFamily (w : ℝ → ℂ) (hw : MemLp w 2) (v : ℝ × SchwartzMap TailSpace ℂ) : FrequencyHilbert :=
  (product_memLp _ _ (modulate_memLp w hw v.1) (v.2.memLp 2 volume)).toLp (productFunction (modulate v.1 w) v.2)

theorem dense_euclidean_span (w : ℝ → ℂ) (hw : MemLp w 2) (hnw : ∀ q, w q ≠ 0) :
    (Submodule.span ℂ (Set.range (euclideanFamily w hw))).topologicalClosure=⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply ae_zero_of_orthogonal_products w hw hnw f (Lp.memLp f)
  intro p ψ
  have hm : euclideanFamily w hw (p,ψ) ∈ Submodule.span ℂ (Set.range (euclideanFamily w hw)) :=
    Submodule.subset_span ⟨(p,ψ),rfl⟩
  have ho := Submodule.inner_right_of_mem_orthogonal hm hf
  rw [L2.inner_def] at ho
  convert ho using 1
  apply integral_congr_ae
  filter_upwards [(product_memLp _ _ (modulate_memLp w hw p) (ψ.memLp 2 volume)).coeFn_toLp] with x hx
  change star (productFunction (modulate p w) ψ x)*f x =
    inner ℂ (((product_memLp _ _ (modulate_memLp w hw p) (ψ.memLp 2 volume)).toLp _) x) (f x)
  rw [hx,RCLike.inner_apply']
  rfl

def physicalFamily (ε : ℝ) (hε : 0 < ε) (w : ℝ → ℂ) (hw : MemLp w 2)
    (v : ℝ × SchwartzMap TailSpace ℂ) : Hilbert :=
  productState ε hε (modulate v.1 w) v.2 (modulate_memLp w hw v.1) (v.2.memLp 2 volume)

theorem lift_product (ε : ℝ) (hε : 0 < ε) (w : ℝ → ℂ) (hw : MemLp w 2)
    (v : ℝ × SchwartzMap TailSpace ℂ) :
    lift ε hε (euclideanFamily w hw v) = physicalFamily ε hε w hw v := by
  change coordinates ε hε (euclideanPullback.symm (euclideanFamily w hw v)) =
    coordinates ε hε ((configuration_memLp _ _ (modulate_memLp w hw v.1) (v.2.memLp 2 volume)).toLp _)
  congr 1

theorem dense_physical_span (ε : ℝ) (hε : 0 < ε) (w : ℝ → ℂ) (hw : MemLp w 2)
    (hnw : ∀ q, w q ≠ 0) :
    (Submodule.span ℂ (Set.range (physicalFamily ε hε w hw))).topologicalClosure=⊤ := by
  let L : FrequencyHilbert →L[ℂ] Hilbert := lift ε hε
  have hd : DenseRange L := (lift ε hε).surjective.denseRange
  have he := hd.topologicalClosure_map_submodule (dense_euclidean_span w hw hnw)
  have ht : (L : FrequencyHilbert → Hilbert) ∘ euclideanFamily w hw = physicalFamily ε hε w hw :=
    funext (lift_product ε hε w hw)
  rw [Submodule.map_span,← Set.range_comp] at he
  change (Submodule.span ℂ (Set.range ((L : FrequencyHilbert → Hilbert) ∘ euclideanFamily w hw))).topologicalClosure=⊤ at he
  rw [ht] at he
  exact he

#print axioms modulate_memLp
#print axioms product_modulate
#print axioms ae_zero_of_orthogonal_products
#print axioms dense_euclidean_span
#print axioms lift_product
#print axioms dense_physical_span

end
end UnifiedTheory.Audit.KFCausalWeightedProductTotality

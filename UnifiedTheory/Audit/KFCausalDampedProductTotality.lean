/- The explicit repaired clock trials paired with Schwartz transverse
packets are total in the full Euclidean L2 space. Countably many compact
packets and ordinary Fourier uniqueness prove the density statement. -/
import UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness
import UnifiedTheory.Audit.KFCausalCompactTransverseModulation
import UnifiedTheory.Audit.KFCausalDampedProductDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedProductTotality
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCompactTransverseModulation
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality

theorem product_modulate (ε a : ℝ) (n : ℕ) (k : Space) :
    KFCausalEuclideanFourierUniqueness.modulate k (productFunction (realTrial ε a) (packet n)) =
      productFunction (modulate (k 0) (realTrial ε a)) (modulatedPacket n (tail k)) := by
  funext x
  simp only [KFCausalEuclideanFourierUniqueness.modulate,product_apply,modulatedPacket_apply,
    modulate,inner_split,AddChar.map_add_eq_mul,Circle.coe_mul]
  rw [mul_comm (k 0) (x 0)]
  ring

theorem ae_zero_of_orthogonal_products (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (f : Space → ℂ) (hf : MemLp f 2)
    (ho : ∀ (p : ℝ) (ψ : SchwartzMap TailSpace ℂ),
      (∫ x, star (productFunction (modulate p (realTrial ε a)) ψ x)*f x)=0) :
    f =ᵐ[volume] 0 := by
  have hn (n : ℕ) : (fun x => star (productFunction (realTrial ε a) (packet n) x)*f x) =ᵐ[volume] 0 := by
    apply KFCausalEuclideanFourierUniqueness.weighted_zero_of_orthogonal_modulations _ f
      (product_memLp _ _ (realTrial_memLp ε a hε ha) ((packet n).memLp 2 volume)) hf
    intro k
    rw [product_modulate]
    exact ho (k 0) (modulatedPacket n (tail k))
  have hall := (ae_all_iff.mpr hn)
  filter_upwards [hall] with x hx
  obtain ⟨n,hp⟩ := packet_cover (tail x)
  have hz := hx n
  simp only [product_apply,hp,mul_one,Pi.zero_apply] at hz
  exact (mul_eq_zero.mp hz).resolve_left (star_ne_zero.mpr (realTrial_ne_zero ε a (x 0)))

def euclideanTrial (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (v : ℝ × SchwartzMap TailSpace ℂ) : FrequencyHilbert :=
  (product_memLp _ _ (modulated_memLp ε a v.1 hε ha) (v.2.memLp 2 volume)).toLp
    (productFunction (modulate v.1 (realTrial ε a)) v.2)

theorem dense_euclidean_trial_span (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (euclideanTrial ε a hε ha))).topologicalClosure=⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply ae_zero_of_orthogonal_products ε a hε ha f (Lp.memLp f)
  intro p ψ
  have hm : euclideanTrial ε a hε ha (p,ψ) ∈
      Submodule.span ℂ (Set.range (euclideanTrial ε a hε ha)) := Submodule.subset_span ⟨(p,ψ),rfl⟩
  have ho := Submodule.inner_right_of_mem_orthogonal hm hf
  rw [L2.inner_def] at ho
  convert ho using 1
  apply integral_congr_ae
  filter_upwards [(product_memLp _ _ (modulated_memLp ε a p hε ha) (ψ.memLp 2 volume)).coeFn_toLp] with x hx
  change star (productFunction (modulate p (realTrial ε a)) ψ x)*f x =
    inner ℂ (((product_memLp _ _ (modulated_memLp ε a p hε ha) (ψ.memLp 2 volume)).toLp _) x) (f x)
  rw [hx,RCLike.inner_apply']
  rfl

#print axioms product_modulate
#print axioms ae_zero_of_orthogonal_products
#print axioms dense_euclidean_trial_span

end
end UnifiedTheory.Audit.KFCausalDampedProductTotality

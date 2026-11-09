/- Weak derivative data against the dense strong-generator domain imply
an actual strong derivative. The proof uses unitary orbit invariance,
scalar integration, and density; it assumes no weak-to-strong principle. -/
import UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : StrongUnitaryGroup H)

theorem inner_transport (x y : H) (t : ℝ) :
    inner ℂ y (U.action t x) = inner ℂ (U.action (-t) y) x := by
  rw [← (U.action (-t)).inner_map_map y (U.action t x),U.compose,add_neg_cancel,U.initial]

theorem weak_orbit_derivative (x z : H)
    (hp : ∀ y : (generator U).domain, inner ℂ (generator U y) x = -inner ℂ (y:H) z)
    (y : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (y:H) (U.action s x)) (inner ℂ (y:H) (U.action t z)) t := by
  have hd := (derivative_at_time U y (generator U y) (generator_derivative U y) (-t)).scomp
    t (hasDerivAt_neg t)
  have hi := hd.inner ℂ (hasDerivAt_const t x)
  have he : inner ℂ (-U.action (-t) (generator U y)) x = inner ℂ (y:H) (U.action t z) := by
    rw [inner_neg_left,← generator_commutes U (-t) y,hp,neg_neg]
    exact (inner_transport U z y t).symm
  simpa only [Function.comp_apply,neg_smul,one_smul,inner_zero_right,zero_add,he,
    inner_transport U x] using hi

variable [CompleteSpace H]

theorem weak_integral_identity (x z : H)
    (hp : ∀ y : (generator U).domain, inner ℂ (generator U y) x = -inner ℂ (y:H) z)
    (t : ℝ) : primitive U z t = U.action t x-x := by
  have he : ∀ y : (generator U).domain,
      inner ℂ (y:H) (primitive U z t) = inner ℂ (y:H) (U.action t x-x) := by
    intro y
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => weak_orbit_derivative U x z hp y s)
      ((continuous_const.inner (U.continuous_orbit z)).intervalIntegrable 0 t)
    change (innerSL ℂ (y:H)) (∫ s in 0..t, U.action s z) = _
    rw [← (innerSL ℂ (y:H)).intervalIntegral_comp_comm
      ((U.continuous_orbit z).intervalIntegrable 0 t)]
    simpa only [innerSL_apply_apply,inner_sub_right,U.initial] using hh
  have hh := (generator_dense U).denseRange_val.equalizer
    (continuous_id.inner continuous_const) (continuous_id.inner continuous_const) (funext he)
  exact ext_inner_left ℂ (fun y => congrFun hh y)

theorem weak_implies_strong (x z : H)
    (hp : ∀ y : (generator U).domain, inner ℂ (generator U y) x = -inner ℂ (y:H) z) :
    HasDerivAt (fun t => U.action t x) z 0 := by
  have he : (fun t => U.action t x) = (fun t => primitive U z t+x) := by
    funext t
    rw [weak_integral_identity U x z hp,sub_add_cancel]
  rw [he]
  simpa only [U.initial] using (primitive_derivative U z 0).add_const x

theorem generator_graph_iff_weak (x z : H) :
    (x,z) ∈ (generator U).graph ↔
      ∀ y : (generator U).domain, inner ℂ (generator U y) x = -inner ℂ (y:H) z := by
  constructor
  · intro hh y
    obtain ⟨v,hv,hz⟩ := (LinearPMap.mem_graph_iff _).mp hh
    have he := generator_skew_symmetric U y v
    rw [hv,hz] at he
    exact eq_neg_of_add_eq_zero_right he
  · intro hp
    exact (generator_graph_iff U x z).mpr (weak_implies_strong U x z hp)

theorem generator_closed : (generator U).IsClosed := by
  have he : ((generator U).graph : Set (H × H)) =
      ⋂ y : (generator U).domain,
        {p : H × H | inner ℂ (generator U y) p.1 = -inner ℂ (y:H) p.2} := by
    ext p
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    exact generator_graph_iff_weak U p.1 p.2
  change IsClosed ((generator U).graph : Set (H × H))
  rw [he]
  exact isClosed_iInter fun y => isClosed_eq
    (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd).neg

#print axioms inner_transport
#print axioms weak_orbit_derivative
#print axioms weak_integral_identity
#print axioms weak_implies_strong
#print axioms generator_graph_iff_weak
#print axioms generator_closed

end
end UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator

/- Totality of the shifted-clock-dressed product family follows from
Fourier uniqueness and the actual onto revised coordinate unitary.
No preservation of density by an unbounded multiplication is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoreStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoreDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)
open UnifiedTheory.Audit.KFCausalClockFloorCoreWeights
open UnifiedTheory.Audit.KFCausalClockFloorCoreStates
open UnifiedTheory.Audit.KFCausalClockFloorProductStates (lift)
open UnifiedTheory.Audit.KFCausalWeightedProductTotality (euclideanFamily dense_euclidean_span)

def family (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (v : ℝ × SchwartzMap TailSpace ℂ) : Hilbert :=
  dressedState ε a v.1 hε ha v.2 (v.2.memLp 2 volume)

theorem lift_family (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (v : ℝ × SchwartzMap TailSpace ℂ) :
    lift ε hε (euclideanFamily (halfScalar ε a hε) (halfScalar_memLp ε a hε ha) v) =
      family ε a hε ha v := by
  rfl

theorem dense_family_span (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (family ε a hε ha))).topologicalClosure = ⊤ := by
  let L : FrequencyHilbert →L[ℂ] Hilbert := lift ε hε
  have hd : DenseRange L := (lift ε hε).surjective.denseRange
  have he := hd.topologicalClosure_map_submodule
    (dense_euclidean_span (halfScalar ε a hε) (halfScalar_memLp ε a hε ha) (halfScalar_ne_zero ε a hε))
  have ht : (L : FrequencyHilbert → Hilbert) ∘ euclideanFamily (halfScalar ε a hε)
      (halfScalar_memLp ε a hε ha) = family ε a hε ha := funext (lift_family ε a hε ha)
  rw [Submodule.map_span,← Set.range_comp] at he
  change (Submodule.span ℂ (Set.range ((L : FrequencyHilbert → Hilbert) ∘
    euclideanFamily (halfScalar ε a hε) (halfScalar_memLp ε a hε ha)))).topologicalClosure = ⊤ at he
  rw [ht] at he
  exact he

#print axioms lift_family
#print axioms dense_family_span

end
end UnifiedTheory.Audit.KFCausalClockFloorCoreDensity

/- Exact Haar reconstruction of coarse links from independent endpoint
half-edges. The enlarged variables retain the original product Haar law
under coarsening; this is not a replacement reference distribution. -/
import UnifiedTheory.Clay.YangMills.PeriodicHalfSplit
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.HaarHalfEdges
noncomputable section
open MeasureTheory RegulatedGauge

variable {I : Type*} (G : Type*) [Group G]

def coarsen (U : I ⊕ I → G) (e : I) : G := U (Sum.inl e) * (U (Sum.inr e))⁻¹

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem coarsen_continuous : Continuous (coarsen (I := I) G) := by
  apply continuous_pi
  intro e
  exact (continuous_apply (Sum.inl e)).mul (continuous_apply (Sum.inr e)).inv

variable [Fintype I] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

local instance haar_right : (compactHaar G).IsMulRightInvariant := by
  exact RegulatedGauge.compactHaar_right G

theorem coarsen_preserving :
    MeasurePreserving (coarsen (I := I) G)
      (Measure.pi (fun _ : I ⊕ I => compactHaar G))
      (Measure.pi (fun _ : I => compactHaar G)) := by
  let μ := Measure.pi (fun _ : I => compactHaar G)
  have hp := measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ I => compactHaar G)
  have hd : MeasurePreserving (fun z : (I → G) × (I → G) => z.1 / z.2)
      (μ.prod μ) μ :=
    measurePreserving_fst.comp (measurePreserving_div_prod μ μ)
  simpa only [Function.comp_def, MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi_apply, coarsen, Pi.div_apply, div_eq_mul_inv] using hd.comp hp

theorem integral_coarsen (F : (I → G) → ℝ) (hF : Continuous F) :
    (∫ U, F (coarsen G U) ∂Measure.pi (fun _ : I ⊕ I => compactHaar G)) =
      ∫ u, F u ∂Measure.pi (fun _ : I => compactHaar G) := by
  have hp := coarsen_preserving (I := I) G
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm

end
end UnifiedTheory.Clay.YangMills.HaarHalfEdges

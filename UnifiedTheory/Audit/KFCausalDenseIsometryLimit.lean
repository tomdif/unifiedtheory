/- Strong convergence on a dense set extends to every state for isometries.
This is a filter statement, so it applies to discrete and real cutoffs. -/
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseIsometryLimit
open Filter
open scoped Topology

variable {E H ι : Type*} [PseudoMetricSpace H]

theorem tendsto_of_dense_isometries (J : E → H) (hJ : DenseRange J)
    (F : ι → H → H) (G : H → H) (hF : ∀ i, Isometry (F i)) (hG : Isometry G)
    (l : Filter ι) (hc : ∀ w, Tendsto (fun i => F i (J w)) l (𝓝 (G (J w)))) (x : H) :
    Tendsto (fun i => F i x) l (𝓝 (G x)) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨w,hw⟩ := hJ.exists_dist_lt x (show 0 < δ/3 from by positivity)
  have hl := Metric.tendsto_nhds.mp (hc w) (δ/3) (by positivity)
  filter_upwards [hl] with i hi
  have ht := dist_triangle4 (F i x) (F i (J w)) (G (J w)) (G x)
  rw [(hF i).dist_eq,hG.dist_eq,dist_comm (J w) x] at ht
  linarith

#print axioms tendsto_of_dense_isometries

end UnifiedTheory.Audit.KFCausalDenseIsometryLimit

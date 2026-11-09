/- Decay of a fixed bounded observation on dense initial data extends
through unitary dynamics to every physical Hilbert vector. -/
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDenseObservationDecay
noncomputable section
open Filter
open scoped Topology
variable {V H K ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

theorem decay (J : V → H) (hJ : DenseRange J) (U : ι → H ≃ₗᵢ[ℂ] H)
    (A : H →L[ℂ] K) (p : Filter ι)
    (hd : ∀ v, Tendsto (fun t => A (U t (J v))) p (𝓝 0)) (f : H) :
    Tendsto (fun t => A (U t f)) p (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨v,hv⟩ := hJ.exists_dist_lt f
    (show 0 < η/(2*(‖A‖+1)) by positivity)
  rw [dist_eq_norm] at hv
  have he := (lt_div_iff₀ (by positivity : 0 < 2*(‖A‖+1))).mp hv
  filter_upwards [(Metric.tendsto_nhds.mp (hd v)) (η/2) (by positivity)] with t ht
  rw [dist_zero_right] at ht ⊢
  have hb : ‖A (U t f)-A (U t (J v))‖ ≤ ‖A‖*‖f-J v‖ := by
    rw [← map_sub,← map_sub]
    exact (A.le_opNorm _).trans_eq (congrArg (fun r : ℝ => ‖A‖*r) ((U t).norm_map _))
  have htri := norm_add_le (A (U t f)-A (U t (J v))) (A (U t (J v)))
  rw [sub_add_cancel] at htri
  nlinarith only [hb,htri,he,ht,norm_nonneg (f-J v)]

#print axioms decay
end
end UnifiedTheory.Audit.KFCausalDenseObservationDecay

/- Uniform continuity of a spacetime derivative gives a norm derivative
of the bounded momentum slice curve, via Banach-valued FTC. -/
import UnifiedTheory.Audit.KFCausalMomentumPairTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeSliceRegularity
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests (slice slice_norm_le)

theorem slice_uniformContinuous (q : (ℝ × ℝ) →ᵇ ℂ) (hq : UniformContinuous q) :
    UniformContinuous (fun t => slice t q) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hqδ⟩ := Metric.uniformContinuous_iff.mp hq (ε/2) (half_pos hε)
  refine ⟨δ,hδ,fun t u htu => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).mpr
  intro p
  have hz : dist (t,p) (u,p) < δ := by simpa [Prod.dist_eq] using htu
  have hh : ‖q (t,p)-q (u,p)‖ < ε/2 := by simpa only [dist_eq_norm] using hqδ hz
  exact hh.le

def curry (q : (ℝ × ℝ) →ᵇ ℂ) (hq : UniformContinuous q) : ℝ →ᵇ (ℝ →ᵇ ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => slice t q)
    (slice_uniformContinuous q hq).continuous ‖q‖ (fun t => slice_norm_le t q)

theorem curry_apply (q : (ℝ × ℝ) →ᵇ ℂ) (hq : UniformContinuous q) (t p : ℝ) :
    curry q hq t p = q (t,p) := rfl

theorem slice_eq_primitive (q r : (ℝ × ℝ) →ᵇ ℂ) (hr : UniformContinuous r)
    (hd : ∀ t p, HasDerivAt (fun u => q (u,p)) (r (t,p)) t) (t : ℝ) :
    slice t q = slice 0 q + ∫ u in 0..t, slice u r := by
  ext p
  have hc := (slice_uniformContinuous r hr).continuous
  have he := (BoundedContinuousFunction.evalCLM ℝ p).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 t)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u p)
    ((r.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 t)
  change q (t,p) = q (0,p)+(∫ u in 0..t, slice u r) p
  calc
    q (t,p) = q (0,p)+(∫ u in 0..t, r (u,p)) := by rw [hf]; ring
    _ = _ := congrArg (fun v => q (0,p)+v) he

theorem slice_hasDerivAt (q r : (ℝ × ℝ) →ᵇ ℂ) (hr : UniformContinuous r)
    (hd : ∀ t p, HasDerivAt (fun u => q (u,p)) (r (t,p)) t) (t : ℝ) :
    HasDerivAt (fun u => slice u q) (slice t r) t := by
  have he : (fun u => slice u q) = (fun u => slice 0 q + ∫ v in 0..u, slice v r) :=
    funext (slice_eq_primitive q r hr hd)
  rw [he]
  exact (((slice_uniformContinuous r hr).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add
    (slice 0 q)

theorem slice_pair_hasDerivAt (q r p s : (ℝ × ℝ) →ᵇ ℂ)
    (hr : UniformContinuous r) (hs : UniformContinuous s)
    (hqr : ∀ t x, HasDerivAt (fun u => q (u,x)) (r (t,x)) t)
    (hps : ∀ t x, HasDerivAt (fun u => p (u,x)) (s (t,x)) t) (t : ℝ) :
    HasDerivAt (fun u => (slice u q,slice u p)) (slice t r,slice t s) t :=
  (slice_hasDerivAt q r hr hqr t).prodMk (slice_hasDerivAt p s hs hps t)

#print axioms slice_uniformContinuous
#print axioms curry_apply
#print axioms slice_eq_primitive
#print axioms slice_hasDerivAt
#print axioms slice_pair_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalSpacetimeSliceRegularity

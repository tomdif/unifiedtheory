/- C1 physical functions with themselves and their shear differential in
L2 belong to the actual shear graph. Scaled compact cutoffs approximate
both graph components; no clock-derivative condition is required. -/
import UnifiedTheory.Audit.KFCausalShearCutoffDifferential
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalShearMaximalDifferential
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalShearCutoffDifferential
open UnifiedTheory.Audit.KFCausalTransverseShearDifferential (compact_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum shear_closed)

theorem scaled_memLp (m : Configuration → ℂ) (hc : Continuous m) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ x, ‖m x‖ ≤ M) (f : Configuration → ℂ)
    (hf : MemLp f 2 volume) (t : ℝ) : MemLp (fun x => m (t • x)*f x) 2 volume := by
  have hm : Continuous (fun x : Configuration => m (t • x)) := hc.comp (continuous_const.smul continuous_id)
  apply (hf.const_mul (M:ℂ)).of_le (hm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM] using
    mul_le_mul_of_nonneg_right (hb (t • x)) (norm_nonneg (f x))

theorem scaled_continuous (m : Configuration → ℂ) (hc : Continuous m) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ x, ‖m x‖ ≤ M) (f : Configuration → ℂ) (hf : MemLp f 2 volume) :
    Continuous (fun t => (scaled_memLp m hc M hM hb f hf t).toLp (fun x => m (t • x)*f x)) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _ (fun x => (M:ℂ)*f x) (hf.const_mul _)
  · intro t
    filter_upwards [] with x
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM] using
      mul_le_mul_of_nonneg_right (hb (t • x)) (norm_nonneg (f x))
  · exact Eventually.of_forall (fun x => (hc.comp (continuous_id.smul continuous_const)).mul continuous_const)

theorem cut_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume) (t : ℝ) : MemLp (cut t f) 2 volume :=
  scaled_memLp cutoff cutoff_smooth.continuous 1 (by norm_num) cutoff_norm f hf t

theorem cut_continuous (f : Configuration → ℂ) (hf : MemLp f 2 volume) :
    Continuous (fun t => (cut_memLp f hf t).toLp (cut t f)) :=
  scaled_continuous cutoff cutoff_smooth.continuous 1 (by norm_num) cutoff_norm f hf

theorem cut_shear_memLp (f : Configuration → ℂ) (hc : ContDiff ℝ 1 f)
    (hf : MemLp f 2 volume) (hd : MemLp (shearDerivative f) 2 volume) (t : ℝ) :
    MemLp (shearDerivative (cut t f)) 2 volume := by
  obtain ⟨M,hM,hb⟩ := error_bound
  rw [funext (cut_shear t f (hc.differentiable (by norm_num)))]
  exact (cut_memLp (shearDerivative f) hd t).add (scaled_memLp error error_continuous M hM hb f hf t)

theorem cut_shear_continuous (f : Configuration → ℂ) (hc : ContDiff ℝ 1 f)
    (hf : MemLp f 2 volume) (hd : MemLp (shearDerivative f) 2 volume) :
    Continuous (fun t => (cut_shear_memLp f hc hf hd t).toLp (shearDerivative (cut t f))) := by
  obtain ⟨M,hM,hb⟩ := error_bound
  have he (t : ℝ) : (cut_shear_memLp f hc hf hd t).toLp (shearDerivative (cut t f)) =
      (cut_memLp (shearDerivative f) hd t).toLp (cut t (shearDerivative f))+
      (scaled_memLp error error_continuous M hM hb f hf t).toLp (fun x => error (t • x)*f x) := by
    apply Lp.ext
    filter_upwards [(cut_shear_memLp f hc hf hd t).coeFn_toLp,
      Lp.coeFn_add ((cut_memLp (shearDerivative f) hd t).toLp (cut t (shearDerivative f)))
        ((scaled_memLp error error_continuous M hM hb f hf t).toLp (fun x => error (t • x)*f x)),
      (cut_memLp (shearDerivative f) hd t).coeFn_toLp,
      (scaled_memLp error error_continuous M hM hb f hf t).coeFn_toLp] with x ha hb' hc' hd'
    rw [ha,hb']
    simp only [Pi.add_apply,hc',hd']
    exact cut_shear t f (hc.differentiable (by norm_num)) x
  simp_rw [he]
  exact (cut_continuous (shearDerivative f) hd).add
    (scaled_continuous error error_continuous M hM hb f hf)

theorem cut_zero (f : Configuration → ℂ) : cut 0 f = f := by
  funext x
  simp only [cut,zero_smul,cutoff_zero,one_mul]

theorem graph_of_shear_differential (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hc : ContDiff ℝ 1 f) (hf : MemLp f 2 volume) (hd : MemLp (shearDerivative f) 2 volume) :
    (hf.toLp f,(-Complex.I*(h:ℂ)) • hd.toLp (shearDerivative f)) ∈ (shearMomentum h).graph := by
  let u (t : ℝ) : Hilbert := (cut_memLp f hf t).toLp (cut t f)
  let v (t : ℝ) : Hilbert := (-Complex.I*(h:ℂ)) •
    (cut_shear_memLp f hc hf hd t).toLp (shearDerivative (cut t f))
  have hu : Continuous u := cut_continuous f hf
  have hv : Continuous v := (cut_shear_continuous f hc hf hd).const_smul _
  have hm : ∀ᶠ t in 𝓝[≠] (0:ℝ), (u t,v t) ∈ (shearMomentum h).graph := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hn : t ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using ht
    exact compact_graph h hh (cut t f) (cut_smooth t f hc) (cut_compact t hn f)
  have hz := (shear_closed h hh).mem_of_tendsto
    ((hu.prodMk hv).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hm
  simpa only [u,v,cut_zero] using hz

theorem domain_of_shear_differential (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hc : ContDiff ℝ 1 f) (hf : MemLp f 2 volume) (hd : MemLp (shearDerivative f) 2 volume) :
    hf.toLp f ∈ (shearMomentum h).domain :=
  LinearPMap.mem_domain_of_mem_graph (graph_of_shear_differential h hh f hc hf hd)

#print axioms scaled_memLp
#print axioms scaled_continuous
#print axioms cut_memLp
#print axioms cut_continuous
#print axioms cut_shear_memLp
#print axioms cut_shear_continuous
#print axioms cut_zero
#print axioms graph_of_shear_differential
#print axioms domain_of_shear_differential
end
end UnifiedTheory.Audit.KFCausalShearMaximalDifferential

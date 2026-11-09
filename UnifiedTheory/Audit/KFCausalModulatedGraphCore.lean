/- Fourier modulations of a nonvanishing graph-admissible weight are a
proved core of the maximal real multiplication graph. Ordinary L2 density
is transferred through bounded graph coordinates; graph density is not assumed. -/
import UnifiedTheory.Audit.KFCausalMultiplierGraphCoordinates
import UnifiedTheory.Audit.KFCausalModulatedLpTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalModulatedGraphCore
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalMultiplierGraphCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness (modulate)
open UnifiedTheory.Audit.KFCausalModulatedLpTotality (state state_coe dense_span)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (m : E → ℝ) (hm : Measurable m) (w : E → ℂ) (hw : MemLp w 2)
  (hmw : MemLp (fun x => (m x:ℂ)*w x) 2)

def graphWeight (x : E) : ℂ := (radius (m x):ℂ)*w x

include hm hw hmw in
theorem graphWeight_memLp : MemLp (graphWeight m w) 2 := by
  have hr : Measurable (fun x => (radius (m x):ℂ)) := by unfold radius; fun_prop
  apply (hw.norm.add hmw.norm).of_le (hr.aestronglyMeasurable.mul hw.1)
  filter_upwards [] with x
  change ‖(radius (m x):ℂ)*w x‖ ≤ ‖‖w x‖+‖(m x:ℂ)*w x‖‖
  rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hb : radius (m x) ≤ 1+|m x| := by
    nlinarith [radius_square (m x),radius_positive (m x),abs_nonneg (m x),sq_abs (m x)]
  have h := mul_le_mul_of_nonneg_right hb (norm_nonneg (w x))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (radius_positive (m x)),add_mul,one_mul] using h

def packet (k : E) : H (μ := (volume : Measure E)) × H (μ := (volume : Measure E)) :=
  (state w hw k,state (fun x => (m x:ℂ)*w x) hmw k)

theorem packet_mem_graph (k : E) : packet m w hw hmw k ∈ graph m hm := by
  apply (graph_iff m hm _ _).mpr
  filter_upwards [state_coe w hw k,state_coe (fun x => (m x:ℂ)*w x) hmw k] with x h0 h1
  rw [h0,h1]
  unfold modulate
  ring

theorem lift_graphWeight_state (k : E) :
    lift m hm (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k) = packet m w hw hmw k := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [lower_coe m hm (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k),
      state_coe (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k,state_coe w hw k] with x h0 h1 h2
    change (lower m hm (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k)) x = (state w hw k) x
    rw [h0,h1,h2]
    have he : (lowerWeight (m x):ℂ)*(radius (m x):ℂ)=1 := by exact_mod_cast lowerWeight_radius (m x)
    unfold modulate graphWeight
    calc
      _ = ((lowerWeight (m x):ℂ)*(radius (m x):ℂ))*((Real.fourierChar (inner ℝ x k):ℂ)*w x) := by ring
      _ = _ := by rw [he,one_mul]
  · apply Lp.ext
    filter_upwards [upper_coe m hm (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k),
      state_coe (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k,
      state_coe (fun x => (m x:ℂ)*w x) hmw k] with x h0 h1 h2
    change (upper m hm (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k)) x =
      (state (fun x => (m x:ℂ)*w x) hmw k) x
    rw [h0,h1,h2]
    have he : (upperWeight (m x):ℂ)*(radius (m x):ℂ)=(m x:ℂ) := by exact_mod_cast upperWeight_radius (m x)
    unfold modulate graphWeight
    calc
      _ = ((upperWeight (m x):ℂ)*(radius (m x):ℂ))*((Real.fourierChar (inner ℝ x k):ℂ)*w x) := by ring
      _ = _ := by rw [he]; ring

/-- Full graph-core equality follows from integrability and the pointwise
nonvanishing weight; it is not an additional density hypothesis. -/
theorem graph_core (hn : ∀ x, w x ≠ 0) :
    (Submodule.span ℂ (Set.range (packet m w hw hmw))).topologicalClosure = graph m hm := by
  let K := Submodule.span ℂ (Set.range (packet m w hw hmw))
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _
      (KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint
        (LinearIsometryEquiv.refl ℂ (H (μ := (volume : Measure E)))) m hm).isClosed
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact packet_mem_graph m hm w hw hmw k
  · have hS : Submodule.span ℂ (Set.range
        (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw))) ≤
        K.topologicalClosure.comap (lift m hm).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k,rfl⟩
      change lift m hm (state (graphWeight m w) (graphWeight_memLp m hm w hw hmw) k) ∈ K.topologicalClosure
      rw [lift_graphWeight_state m hm w hw hmw k]
      exact K.le_topologicalClosure (Submodule.subset_span ⟨k,rfl⟩)
    have hc := Submodule.topologicalClosure_minimal _ hS
      (K.isClosed_topologicalClosure.preimage (lift m hm).continuous)
    have hd := dense_span (graphWeight m w) (graphWeight_memLp m hm w hw hmw)
      (fun x => mul_ne_zero (Complex.ofReal_ne_zero.mpr (radius_positive (m x)).ne') (hn x))
    rw [hd] at hc
    rintro ⟨f,g⟩ hfg
    obtain ⟨h,he⟩ := lift_surjective_graph m hm f g hfg
    have hh := hc (show h ∈ (⊤ : Submodule ℂ (H (μ := (volume : Measure E)))) from trivial)
    change lift m hm h ∈ K.topologicalClosure at hh
    rw [he] at hh
    exact hh

#print axioms graphWeight_memLp
#print axioms packet_mem_graph
#print axioms lift_graphWeight_state
#print axioms graph_core

end
end UnifiedTheory.Audit.KFCausalModulatedGraphCore

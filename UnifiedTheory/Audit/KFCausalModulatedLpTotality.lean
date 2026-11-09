/- A nowhere-zero L2 weight has a total family of Fourier modulations.
This is Hilbert-norm totality; no unbounded-operator domain is assumed. -/
import UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalModulatedLpTotality
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem modulate_norm (k : E) (w : E → ℂ) (x : E) :
    ‖modulate k w x‖ = ‖w x‖ := by simp [modulate]

theorem modulate_memLp (k : E) (w : E → ℂ) (hw : MemLp w 2) :
    MemLp (modulate k w) 2 := by
  apply hw.of_le
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable.mul hw.1)
  filter_upwards [] with x
  exact (modulate_norm k w x).le

def state (w : E → ℂ) (hw : MemLp w 2) (k : E) : Lp ℂ 2 (volume : Measure E) :=
  (modulate_memLp k w hw).toLp (modulate k w)

theorem state_coe (w : E → ℂ) (hw : MemLp w 2) (k : E) :
    state w hw k =ᵐ[volume] modulate k w := (modulate_memLp k w hw).coeFn_toLp

theorem state_zero (w : E → ℂ) (hw : MemLp w 2) : state w hw 0 = hw.toLp w := by
  apply Lp.ext
  filter_upwards [state_coe w hw 0,hw.coeFn_toLp] with x hx hy
  simpa [modulate] using hx.trans (by simpa [modulate] using hy.symm)

theorem dense_span (w : E → ℂ) (hw : MemLp w 2) (hn : ∀ x, w x ≠ 0) :
    (Submodule.span ℂ (Set.range (state w hw))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  intro f hf
  have ho (k : E) : (∫ x, star (modulate k w x)*f x) = 0 := by
    have hm : state w hw k ∈ Submodule.span ℂ (Set.range (state w hw)) :=
      Submodule.subset_span ⟨k,rfl⟩
    have hi := Submodule.inner_right_of_mem_orthogonal hm hf
    rw [L2.inner_def] at hi
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [state_coe w hw k] with x hx
    rw [hx,RCLike.inner_apply']
    rfl
  have hz := weighted_zero_of_orthogonal_modulations w f hw (Lp.memLp f) ho
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz] with x hx
  exact (mul_eq_zero.mp hx).resolve_left (star_ne_zero.mpr (hn x))

#print axioms modulate_norm
#print axioms modulate_memLp
#print axioms state_coe
#print axioms state_zero
#print axioms dense_span

end
end UnifiedTheory.Audit.KFCausalModulatedLpTotality

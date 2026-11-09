/- The actual reduced clock-response combination also passes through
the clustered limit. Both scalar clock multipliers have proved bounds. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredWholeClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredReducedClock
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredWholeClock
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalClockResponseTransport (clock coefficient)

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

theorem reduced_scalar_bound (ε y s E R D : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hE : ‖E‖ ≤ D) (hR : ‖R‖ ≤ D) :
    ‖coefficient ε y s*E-R/clock ε s‖ ≤ (5/ε)*D := by
  have hD : 0 ≤ D := (norm_nonneg E).trans hE
  have hq : ‖coefficient ε y s‖ ≤ 4/ε := by
    simpa only [Complex.norm_real] using KFCausalGaussianResponseIntegrability.coefficient_bound ε y s hε hy
  have ht : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have ht0 : 0 < clock ε s := hε.trans_le ht
  calc
    _ ≤ ‖coefficient ε y s*E‖+‖R/clock ε s‖ := norm_sub_le _ _
    _ = ‖coefficient ε y s‖*‖E‖+‖R‖/clock ε s := by
      rw [norm_mul,norm_div,Real.norm_of_nonneg ht0.le]
    _ ≤ (4/ε)*D+D/ε := add_le_add (mul_le_mul hq hE (norm_nonneg _) (by positivity))
      ((div_le_div_of_nonneg_right hR ht0.le).trans (div_le_div_of_nonneg_left hD hε ht))
    _ = _ := by ring

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y : ℝ)

def reduced (δ : ℝ) (x : Whole) : ℝ :=
  coefficient ε y x.1*energy f c α β ε y δ x-transport f c α β ε y δ x/clock ε x.1
def limitReduced (x : Whole) : ℝ :=
  coefficient ε y x.1*limitEnergy f c α β ε y x-limitTransport f c α β ε y x/clock ε x.1

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

include hε hy hc in
theorem reduced_continuity (δ : ℝ) (hδ : 0 < δ) :
    Continuous (reduced f c α β ε y δ) ∧ Continuous (limitReduced f c α β ε y) := by
  obtain ⟨hE,hR,hL,hT⟩ := joint_continuity f c α β ε y hε hy hc δ hδ
  have hq : Continuous (fun x : Whole => coefficient ε y x.1) :=
    (KFCausalGaussianResponseIntegrability.coefficient_continuous ε y hε hy).comp continuous_fst
  have ht : Continuous (fun x : Whole => clock ε x.1) := by unfold clock; fun_prop
  have hn (x : Whole) : clock ε x.1 ≠ 0 := by unfold clock; positivity
  exact ⟨(hq.mul hE).sub (hR.div ht hn),(hq.mul hL).sub (hT.div ht hn)⟩

include hα hβ hw hε hy hc2 in
theorem reduced_envelope : ∃ D : Whole → ℝ, Integrable D wholeMeasure ∧
    ∀ᵐ x ∂wholeMeasure, (∀ δ : ℝ, 0 < δ → ‖reduced f c α β ε y δ x‖ ≤ D x) ∧
      ‖limitReduced f c α β ε y x‖ ≤ D x := by
  obtain ⟨D,hDi,_,hD⟩ := product_envelope f c α β ε y hα hβ hw hε hy hc2
  refine ⟨fun x => (5/ε)*D x,hDi.const_mul _,?_⟩
  filter_upwards [hD] with x hx
  exact ⟨fun δ hδ => reduced_scalar_bound ε y x.1 _ _ _ hε hy (hx.1 δ hδ).1 (hx.1 δ hδ).2,
    reduced_scalar_bound ε y x.1 _ _ _ hε hy hx.2.1 hx.2.2⟩

include hα hβ hw hε hy hc hc2 in
theorem reduced_integrability (δ : ℝ) (hδ : 0 < δ) :
    Integrable (reduced f c α β ε y δ) wholeMeasure ∧ Integrable (limitReduced f c α β ε y) wholeMeasure := by
  obtain ⟨D,hDi,hD⟩ := reduced_envelope f c α β ε y hα hβ hw hε hy hc2
  have ht := reduced_continuity f c α β ε y hε hy hc δ hδ
  exact ⟨hDi.mono' ht.1.aestronglyMeasurable (hD.mono (fun _ hx => hx.1 δ hδ)),
    hDi.mono' ht.2.aestronglyMeasurable (hD.mono (fun _ hx => hx.2))⟩

theorem reduced_tendsto (x : Whole) :
    Tendsto (fun δ => reduced f c α β ε y δ x) (𝓝[>] 0) (𝓝 (limitReduced f c α β ε y x)) :=
  ((energy_tendsto f c α β ε y x).const_mul _).sub ((transport_tendsto f c α β ε y x).div_const _)

include hα hβ hw hε hy hc hc2 in
theorem reduced_integral_tendsto :
    Tendsto (fun δ => ∫ x, reduced f c α β ε y δ x ∂wholeMeasure) (𝓝[>] 0)
      (𝓝 (∫ x, limitReduced f c α β ε y x ∂wholeMeasure)) := by
  obtain ⟨D,hDi,hD⟩ := reduced_envelope f c α β ε y hα hβ hw hε hy hc2
  apply tendsto_integral_filter_of_dominated_convergence D
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (reduced_continuity f c α β ε y hε hy hc δ hδ).1.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hD.mono (fun _ hx => hx.1 δ hδ)
  · exact hDi
  · exact Filter.Eventually.of_forall (reduced_tendsto f c α β ε y)

include hα hβ hw hε hy hc hc2 in
theorem full_clock_reduced_tendsto :
    Tendsto (fun δ => ∫ s, Real.pi/4*∫ p, reduced f c α β ε y δ (s,p) ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ s, Real.pi/4*∫ p, limitReduced f c α β ε y (s,p) ∂jointMeasure)) := by
  have hL := (reduced_integrability f c α β ε y hα hβ hw hε hy hc hc2 1 (by norm_num)).2
  rw [integral_const_mul,← integral_prod _ hL]
  apply Tendsto.congr' _ ((reduced_integral_tendsto f c α β ε y hα hβ hw hε hy hc hc2).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [integral_const_mul,← integral_prod _ (reduced_integrability f c α β ε y hα hβ hw hε hy hc hc2 δ hδ).1]
  rfl

#print axioms reduced_scalar_bound
#print axioms reduced_continuity
#print axioms reduced_envelope
#print axioms reduced_integrability
#print axioms reduced_tendsto
#print axioms reduced_integral_tendsto
#print axioms full_clock_reduced_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredReducedClock

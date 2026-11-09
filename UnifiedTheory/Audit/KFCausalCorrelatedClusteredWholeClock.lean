/- Full clock integration of correlated clustered energy and frozen-
coefficient transport response. Independent L2 clock amplitudes have a
derived product envelope uniform over positive width spacings. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredWholeClock
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight coefficientMass coefficientMass_nonnegative)
open KFCausalCorrelatedClusteredClockBounds
open KFCausalClockFloorRelativeShift (scale scale_smooth)

abbrev Whole := ℝ × Joint
def wholeMeasure : Measure Whole := volume.prod jointMeasure

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

theorem ae_halfline : ∀ᵐ x ∂wholeMeasure, 0 ≤ x.2.2 :=
  MeasureTheory.Measure.quasiMeasurePreserving_snd.ae KFCausalClusteredWidthEnergyLimit.ae_halfline

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y : ℝ)

def energy (δ : ℝ) (x : Whole) : ℝ := density (reweight f (c x.1)) α β δ (scale ε y x.1) x.2
def transport (δ : ℝ) (x : Whole) : ℝ :=
  response (reweight f (c x.1)) α β δ (scale ε y x.1) (deriv (scale ε y) x.1) x.2
def limitEnergy (x : Whole) : ℝ := limitDensity (reweight f (c x.1)) α β (scale ε y x.1) x.2
def limitTransport (x : Whole) : ℝ :=
  limitResponse (reweight f (c x.1)) α β (scale ε y x.1) (deriv (scale ε y) x.1) x.2

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

include hα hβ hw hε hy hc2 in
theorem product_envelope : ∃ D : Whole → ℝ, Integrable D wholeMeasure ∧ (∀ x, 0 ≤ D x) ∧
    ∀ᵐ x ∂wholeMeasure,
      (∀ δ : ℝ, 0 < δ → ‖energy f c α β ε y δ x‖ ≤ D x ∧ ‖transport f c α β ε y δ x‖ ≤ D x) ∧
      ‖limitEnergy f c α β ε y x‖ ≤ D x ∧ ‖limitTransport f c α β ε y x‖ ≤ D x := by
  obtain ⟨D,hDi,hD0,hD⟩ := all_coefficients_envelope f α β hα hβ hw
  refine ⟨fun x => coefficientMass (c x.1)*D x.2,
    (coefficientMass_integrable c hc2).mul_prod hDi,
    fun x => mul_nonneg (coefficientMass_nonnegative _) (hD0 _),?_⟩
  filter_upwards [ae_halfline] with x hx
  exact hD ε y x.1 hε hy (c x.1) x.2 hx

include hε hy hc in
theorem joint_continuity (δ : ℝ) (hδ : 0 < δ) :
    Continuous (energy f c α β ε y δ) ∧ Continuous (transport f c α β ε y δ) ∧
    Continuous (limitEnergy f c α β ε y) ∧ Continuous (limitTransport f c α β ε y) := by
  have hr := (scale_smooth ε y hε hy).continuous
  have hv := (scale_smooth ε y hε hy).continuous_deriv (by norm_num)
  exact ⟨KFCausalCorrelatedClusteredClockContinuity.density_continuous f c α β _ hc hr δ hδ,
    KFCausalCorrelatedClusteredClockContinuity.response_continuous f c α β _ _ hc hr hv δ,
    KFCausalCorrelatedClusteredClockContinuity.limitDensity_continuous f c α β _ hc hr,
    KFCausalCorrelatedClusteredClockContinuity.limitResponse_continuous f c α β _ _ hc hr hv⟩

include hα hβ hw hε hy hc hc2 in
theorem integrability (δ : ℝ) (hδ : 0 < δ) :
    Integrable (energy f c α β ε y δ) wholeMeasure ∧ Integrable (transport f c α β ε y δ) wholeMeasure ∧
    Integrable (limitEnergy f c α β ε y) wholeMeasure ∧ Integrable (limitTransport f c α β ε y) wholeMeasure := by
  obtain ⟨D,hDi,_,hD⟩ := product_envelope f c α β ε y hα hβ hw hε hy hc2
  obtain ⟨hE,hR,hL,hT⟩ := joint_continuity f c α β ε y hε hy hc δ hδ
  refine ⟨hDi.mono' hE.aestronglyMeasurable ?_,hDi.mono' hR.aestronglyMeasurable ?_,
    hDi.mono' hL.aestronglyMeasurable ?_,hDi.mono' hT.aestronglyMeasurable ?_⟩
  all_goals filter_upwards [hD] with x hx
  · exact (hx.1 δ hδ).1
  · exact (hx.1 δ hδ).2
  · exact hx.2.1
  · exact hx.2.2

theorem energy_tendsto (x : Whole) :
    Tendsto (fun δ => energy f c α β ε y δ x) (𝓝[>] 0) (𝓝 (limitEnergy f c α β ε y x)) :=
  density_tendsto (reweight f (c x.1)) α β (scale ε y x.1) x.2

theorem transport_tendsto (x : Whole) :
    Tendsto (fun δ => transport f c α β ε y δ x) (𝓝[>] 0) (𝓝 (limitTransport f c α β ε y x)) :=
  response_tendsto (reweight f (c x.1)) α β (scale ε y x.1) (deriv (scale ε y) x.1) x.2

include hα hβ hw hε hy hc hc2 in
theorem energy_integral_tendsto :
    Tendsto (fun δ => ∫ x, energy f c α β ε y δ x ∂wholeMeasure) (𝓝[>] 0)
      (𝓝 (∫ x, limitEnergy f c α β ε y x ∂wholeMeasure)) := by
  obtain ⟨D,hDi,_,hD⟩ := product_envelope f c α β ε y hα hβ hw hε hy hc2
  apply tendsto_integral_filter_of_dominated_convergence D
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (joint_continuity f c α β ε y hε hy hc δ hδ).1.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [hD] with x hx
    exact (hx.1 δ hδ).1
  · exact hDi
  · exact Filter.Eventually.of_forall (energy_tendsto f c α β ε y)

include hα hβ hw hε hy hc hc2 in
theorem transport_integral_tendsto :
    Tendsto (fun δ => ∫ x, transport f c α β ε y δ x ∂wholeMeasure) (𝓝[>] 0)
      (𝓝 (∫ x, limitTransport f c α β ε y x ∂wholeMeasure)) := by
  obtain ⟨D,hDi,_,hD⟩ := product_envelope f c α β ε y hα hβ hw hε hy hc2
  apply tendsto_integral_filter_of_dominated_convergence D
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (joint_continuity f c α β ε y hε hy hc δ hδ).2.1.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [hD] with x hx
    exact (hx.1 δ hδ).2
  · exact hDi
  · exact Filter.Eventually.of_forall (transport_tendsto f c α β ε y)

include hα hβ hw hε hy hc hc2 in
theorem full_clock_energy_tendsto :
    Tendsto (fun δ => ∫ s, Real.pi/4*∫ p, energy f c α β ε y δ (s,p) ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ s, Real.pi/4*∫ p, limitEnergy f c α β ε y (s,p) ∂jointMeasure)) := by
  have hL := (integrability f c α β ε y hα hβ hw hε hy hc hc2 1 (by norm_num)).2.2.1
  rw [integral_const_mul,← integral_prod _ hL]
  apply Tendsto.congr' _ ((energy_integral_tendsto f c α β ε y hα hβ hw hε hy hc hc2).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [integral_const_mul,← integral_prod _ (integrability f c α β ε y hα hβ hw hε hy hc hc2 δ hδ).1]
  rfl

include hα hβ hw hε hy hc hc2 in
theorem full_clock_transport_tendsto :
    Tendsto (fun δ => ∫ s, Real.pi/4*∫ p, transport f c α β ε y δ (s,p) ∂jointMeasure) (𝓝[>] 0)
      (𝓝 (∫ s, Real.pi/4*∫ p, limitTransport f c α β ε y (s,p) ∂jointMeasure)) := by
  have hL := (integrability f c α β ε y hα hβ hw hε hy hc hc2 1 (by norm_num)).2.2.2
  rw [integral_const_mul,← integral_prod _ hL]
  apply Tendsto.congr' _ ((transport_integral_tendsto f c α β ε y hα hβ hw hε hy hc hc2).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [integral_const_mul,← integral_prod _ (integrability f c α β ε y hα hβ hw hε hy hc hc2 δ hδ).2.1]
  rfl

#print axioms ae_halfline
#print axioms product_envelope
#print axioms joint_continuity
#print axioms integrability
#print axioms energy_tendsto
#print axioms transport_tendsto
#print axioms energy_integral_tendsto
#print axioms transport_integral_tendsto
#print axioms full_clock_energy_tendsto
#print axioms full_clock_transport_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredWholeClock

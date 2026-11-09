/- Transfer the joint positive Gram error to actual physical Hilbert
vectors with arbitrary independent continuous L2 clock coefficients.
The representative hypothesis identifies finite vectors, not their limit. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputGraphLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalTransfer
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredWholeClock (wholeMeasure)
open KFCausalCorrelatedClusteredL2Error (difference errorMass)
open KFCausalReciprocalNeutralDifference (join join_property)
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalReciprocalNeutralPhysicalSliceNorm (wave norm_integral_le_joint)
open KFCausalCorrelatedClusteredInputProfiles (wave_difference)
open KFCausalCorrelatedClusteredPhysicalCauchy (density_difference)
open KFCausalClockFloorRelativeShift (scale)

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y : ℝ)

def represented (δ : ℝ) (x : Configuration) : ℂ :=
  wave (count f) α β (widths f δ) (scale ε y x.1)
    (coefficients (reweight f (c x.1)) δ) (sources f) (polynomials f) x.2

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

include hα hβ hw hε hy in
theorem slice_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (s : ℝ) :
    (∫ q, ‖represented f c α β ε y δ (s,q)-represented f c α β ε y η (s,q)‖^2) ≤
      Real.pi/4*∫ q, difference f c α β ε y δ η (s,q) ∂jointMeasure := by
  let g := reweight f (c s)
  have hs := norm_integral_le_joint (count g+count g) α β (join (widths g δ) (widths g η))
    (join (coefficients g δ) (fun i => -coefficients g η i))
    (join (sources g) (sources g)) (join (polynomials g) (polynomials g)) ε y s
    hα hβ hw hε hy
    (join_property (widths g δ) (widths g η) (fun t => 1 ≤ t)
      (widths_admissible g δ hδ.le) (widths_admissible g η hη.le))
  simp_rw [wave_difference,density_difference g α β δ η hδ hη (scale ε y s)] at hs
  exact hs

variable (u : ℝ → Hilbert)
  (hu : ∀ δ, 0 < δ → u δ =ᵐ[volume] represented f c α β ε y δ)

include hu

theorem difference_coe (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    (u δ-u η : Hilbert) =ᵐ[volume]
      fun x => represented f c α β ε y δ x-represented f c α β ε y η x := by
  filter_upwards [Lp.coeFn_sub (u δ) (u η),hu δ hδ,hu η hη] with x hs h1 h2
  simp only [hs,Pi.sub_apply,h1,h2]

include hα hβ hw hε hy hc hc2 in
theorem distance_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖u δ-u η‖^2 ≤ 2*errorMass f c α β ε y δ+2*errorMass f c α β ε y η := by
  have he := difference_coe f c α β ε y u hu δ η hδ hη
  have hm := (Lp.memLp (u δ-u η)).ae_eq he
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hj := KFCausalCorrelatedClusteredL2Error.difference_integrable f c α β ε y
    hα hβ hw hε hy hc hc2 δ η hδ hη
  have hn : ‖u δ-u η‖^2 = ∫ x, ‖represented f c α β ε y δ x-represented f c α β ε y η x‖^2 := by
    rw [KFCausalPositiveMultiplierEnergy.l2_norm_square]
    exact integral_congr_ae (he.fun_comp (fun z => ‖z‖^2))
  rw [hn]
  change (∫ x : ℝ × KFCausalTransverseDilationFlow.Transverse,
    ‖represented f c α β ε y δ x-represented f c α β ε y η x‖^2 ∂volume.prod volume) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ s, Real.pi/4*∫ q, difference f c α β ε y δ η (s,q) ∂jointMeasure :=
      integral_mono hi.integral_prod_left (hj.integral_prod_left.const_mul (Real.pi/4))
        (slice_bound f c α β ε y hα hβ hw hε hy δ η hδ hη)
    _ = Real.pi/4*∫ x, difference f c α β ε y δ η x ∂wholeMeasure := by
      rw [integral_const_mul,← integral_prod _ hj]
      rfl
    _ ≤ _ := KFCausalCorrelatedClusteredL2Error.difference_integral_bound f c α β ε y
      hα hβ hw hε hy hc hc2 δ η hδ hη

include hα hβ hw hε hy hc hc2 in
theorem exists_limit : ∃ v : Hilbert, Tendsto u (𝓝[>] 0) (𝓝 v) := by
  apply KFCausalSquaredErrorCompleteness.exists_limit u (fun δ => 2*errorMass f c α β ε y δ)
  · simpa only [mul_zero] using
      (KFCausalCorrelatedClusteredL2Error.errorMass_tendsto f c α β ε y hα hβ hw hε hy hc hc2).const_mul 2
  · exact distance_bound f c α β ε y hα hβ hw hε hy hc hc2 u hu

#print axioms slice_bound
#print axioms difference_coe
#print axioms distance_bound
#print axioms exists_limit
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalTransfer

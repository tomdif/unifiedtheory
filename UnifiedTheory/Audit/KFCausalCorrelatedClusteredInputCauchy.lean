/- The zero-shift positive Gram form gives a vanishing bound for
differences of the actual physical input states. The independent input
clock amplitudes are square integrable and every interference term is kept. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputCauchy
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredInputProfiles
open KFCausalCorrelatedClusteredWholeClock (wholeMeasure)
open KFCausalCorrelatedClusteredL2Error (difference errorMass)
open KFCausalReciprocalNeutralDifference (join join_property)
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalReciprocalNeutralPhysicalSliceNorm (wave norm_integral_le_joint)
open KFCausalCorrelatedClusteredPhysicalCauchy (density_difference)
open KFCausalImaginaryShearInitialMultiplier (scale_zero)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε a p
local notation "U" => finiteState f ε h a p hε hh ha

include hε hh in
theorem slice_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (s : ℝ) :
    (∫ q, ‖represented f ε h a p δ (s,q)-represented f ε h a p η (s,q)‖^2) ≤
      Real.pi/4*∫ q, difference f c α β ε 0 δ η (s,q) ∂jointMeasure := by
  let g := reweight f (c s)
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp only [abs_zero]; positivity
  have hs := norm_integral_le_joint (count g+count g) α β (join (widths g δ) (widths g η))
    (join (coefficients g δ) (fun i => -coefficients g η i))
    (join (sources g) (sources g)) (join (polynomials g) (polynomials g)) ε 0 s
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (join_property (widths g δ) (widths g η) (fun t => 1 ≤ t)
      (widths_admissible g δ hδ.le) (widths_admissible g η hη.le))
  rw [scale_zero ε s hε] at hs
  simp_rw [wave_difference,density_difference g α β δ η hδ hη 1] at hs
  simpa only [represented,difference,KFCausalCorrelatedClusteredL2Error.finiteFactor,scale_zero ε s hε] using hs

theorem state_distance_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖U δ-U η‖^2 ≤ 2*errorMass f c α β ε 0 δ+2*errorMass f c α β ε 0 η := by
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp only [abs_zero]; positivity
  have hc (i : Fin m) : Continuous (fun s => c s i) := inputAmplitude_continuous ε (a i) (p i)
  have hc2 (i : Fin m) : MemLp (fun s => c s i) 2 volume := inputAmplitude_memLp ε (a i) (p i) hε (ha i)
  have hi := difference_integrable f ε h a p hε hh ha δ η hδ hη
  have hj := KFCausalCorrelatedClusteredL2Error.difference_integrable f c α β ε 0
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hc hc2 δ η hδ hη
  rw [norm_difference_integral f ε h a p hε hh ha δ η hδ hη]
  change (∫ x : ℝ × KFCausalTransverseDilationFlow.Transverse,
    ‖represented f ε h a p δ x-represented f ε h a p η x‖^2 ∂volume.prod volume) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ s, Real.pi/4*∫ q, difference f c α β ε 0 δ η (s,q) ∂jointMeasure :=
      integral_mono hi.integral_prod_left (hj.integral_prod_left.const_mul (Real.pi/4))
        (slice_bound f ε h a p hε hh δ η hδ hη)
    _ = Real.pi/4*∫ x, difference f c α β ε 0 δ η x ∂wholeMeasure := by
      rw [integral_const_mul,← integral_prod _ hj]
      rfl
    _ ≤ _ := KFCausalCorrelatedClusteredL2Error.difference_integral_bound f c α β ε 0
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hc hc2 δ η hδ hη

include hε hh ha in
theorem input_error_tendsto : Tendsto (errorMass f c α β ε 0) (𝓝[>] 0) (𝓝 0) := by
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp only [abs_zero]; positivity
  exact KFCausalCorrelatedClusteredL2Error.errorMass_tendsto f c α β ε 0
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (fun i => inputAmplitude_continuous ε (a i) (p i)) (fun i => inputAmplitude_memLp ε (a i) (p i) hε (ha i))

#print axioms slice_bound
#print axioms state_distance_bound
#print axioms input_error_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputCauchy

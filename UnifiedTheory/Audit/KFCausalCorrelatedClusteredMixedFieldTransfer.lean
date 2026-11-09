/- Transfer the full correlated Gram error to mixed field powers.
The finite representative premise identifies actual Hilbert vectors;
neither convergence nor weighted integrability is assumed for them. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredNeutralPowers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMixedFieldTransfer
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredWholeClock (wholeMeasure)
open KFCausalCorrelatedClusteredL2Error (difference errorMass)
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalCorrelatedClusteredPhysicalTransfer (represented)
open KFCausalCorrelatedClusteredNeutralPowers

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y z : ℝ) (n : ℕ)
variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (hy0 : y ≠ 0)
local notation "F" => neutralPower f n
local notation "C" => weightedCoefficients c ε y z n

include hα hβ hw hε hy in
theorem represented_slice_memLp (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    MemLp (fun q => represented f c α β ε y δ (s,q)) 2 volume :=
  KFCausalReciprocalNeutralPhysicalSliceNorm.wave_memLp (count f) α β (widths f δ)
    (coefficients (reweight f (c s)) δ) (sources f) (polynomials f) ε y s
    hα hβ hw hε hy (widths_admissible f δ hδ.le)

include hα hβ hw hε hy hz hy0 in
theorem slice_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (s : ℝ) :
    (∫ q, ‖fieldProfile f c α β ε y z n δ (s,q)-fieldProfile f c α β ε y z n η (s,q)‖^2) ≤
      Real.pi/4*∫ q, difference F C α β ε y δ η (s,q) ∂jointMeasure := by
  have hm := (represented_slice_memLp F C α β ε y hα hβ hw hε hy δ hδ s).sub
    (represented_slice_memLp F C α β ε y hα hβ hw hε hy η hη s)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  calc
    _ ≤ ∫ q, ‖represented F C α β ε y δ (s,q)-represented F C α β ε y η (s,q)‖^2 := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _)) hi
      filter_upwards [] with q
      exact pow_le_pow_left₀ (norm_nonneg _)
        (difference_bound f c α β ε y z n hε hy hz hy0 δ η (s,q)) 2
    _ ≤ _ := KFCausalCorrelatedClusteredPhysicalTransfer.slice_bound F C α β ε y
      hα hβ hw hε hy δ η hδ hη s

variable (hc : ∀ i : Fin m, Continuous (fun s : ℝ => weightedCoefficients c ε y z n s i))
  (hc2 : ∀ i : Fin m, MemLp (fun s : ℝ => weightedCoefficients c ε y z n s i) 2 volume)
  (u : ℝ → Hilbert)
  (hu : ∀ δ, 0 < δ → u δ =ᵐ[volume] fieldProfile f c α β ε y z n δ)

include hu in
theorem difference_coe (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    (u δ-u η : Hilbert) =ᵐ[volume]
      fun x => fieldProfile f c α β ε y z n δ x-fieldProfile f c α β ε y z n η x := by
  filter_upwards [Lp.coeFn_sub (u δ) (u η),hu δ hδ,hu η hη] with x hs h1 h2
  simp only [hs,Pi.sub_apply,h1,h2]

include hα hβ hw hε hy hz hy0 hc hc2 hu in
theorem distance_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖u δ-u η‖^2 ≤ 2*errorMass F C α β ε y δ+2*errorMass F C α β ε y η := by
  have he := difference_coe f c α β ε y z n u hu δ η hδ hη
  have hm := (Lp.memLp (u δ-u η)).ae_eq he
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hj := KFCausalCorrelatedClusteredL2Error.difference_integrable F C α β ε y
    hα hβ hw hε hy hc hc2 δ η hδ hη
  have hn : ‖u δ-u η‖^2 =
      ∫ x, ‖fieldProfile f c α β ε y z n δ x-fieldProfile f c α β ε y z n η x‖^2 := by
    rw [KFCausalPositiveMultiplierEnergy.l2_norm_square]
    exact integral_congr_ae (he.fun_comp (fun t => ‖t‖^2))
  rw [hn]
  change (∫ x : ℝ × KFCausalTransverseDilationFlow.Transverse,
    ‖fieldProfile f c α β ε y z n δ x-fieldProfile f c α β ε y z n η x‖^2 ∂volume.prod volume) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ s, Real.pi/4*∫ q, difference F C α β ε y δ η (s,q) ∂jointMeasure :=
      integral_mono hi.integral_prod_left (hj.integral_prod_left.const_mul (Real.pi/4))
        (slice_bound f c α β ε y z n hα hβ hw hε hy hz hy0 δ η hδ hη)
    _ = Real.pi/4*∫ x, difference F C α β ε y δ η x ∂wholeMeasure := by
      rw [integral_const_mul,← integral_prod _ hj]
      rfl
    _ ≤ _ := KFCausalCorrelatedClusteredL2Error.difference_integral_bound F C α β ε y
      hα hβ hw hε hy hc hc2 δ η hδ hη

include hα hβ hw hε hy hz hy0 hc hc2 hu in
theorem exists_limit : ∃ v : Hilbert, Tendsto u (𝓝[>] 0) (𝓝 v) := by
  apply KFCausalSquaredErrorCompleteness.exists_limit u (fun δ => 2*errorMass F C α β ε y δ)
  · simpa only [mul_zero] using
      (KFCausalCorrelatedClusteredL2Error.errorMass_tendsto F C α β ε y hα hβ hw hε hy hc hc2).const_mul 2
  · exact distance_bound f c α β ε y z n hα hβ hw hε hy hz hy0 hc hc2 u hu

#print axioms represented_slice_memLp
#print axioms slice_bound
#print axioms difference_coe
#print axioms distance_bound
#print axioms exists_limit
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMixedFieldTransfer

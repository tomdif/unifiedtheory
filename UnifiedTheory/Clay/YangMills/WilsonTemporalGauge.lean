/- Exact removal of temporal gauge averaging on gauge-invariant tests.
The unaveraged kernel is identified with the original interacting transfer
on that physical sector, not substituted for it on arbitrary functions. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundLocalComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTemporalGauge
noncomputable section
open MeasureTheory RegulatedGauge WilsonTimeSlab WilsonSlabGauge

variable {n : ℕ} [NeZero n]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Spatial factors and every kinetic link remain in this unaveraged kernel. -/
def rawKernel (chi : G → ℂ) (beta c : ℝ) (u v : SpatialLinks n G) : ℝ :=
  spatialWeight chi beta c u * kineticWeight chi beta c u v * spatialWeight chi beta c v

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem rawKernel_continuous (chi : G → ℂ) (hchi : Continuous chi) (beta c : ℝ) :
    Continuous (fun uv : SpatialLinks n G × SpatialLinks n G =>
      rawKernel chi beta c uv.1 uv.2) := by
  unfold rawKernel spatialWeight kineticWeight kineticAction potential spatialHolonomy
  fun_prop

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem rawKernel_pos (chi : G → ℂ) (beta c : ℝ) (u v : SpatialLinks n G) :
    0 < rawKernel chi beta c u v := by
  unfold rawKernel spatialWeight kineticWeight
  positivity

/-- Haar gauge projection may be removed exactly when the full tested
function is gauge invariant. This retains the original interacting kernel. -/
theorem invariant_integral (chi : G → ℂ) (hchi : Continuous chi)
    (hclass : ClassFunction G chi) (beta c : ℝ) (f : SpatialLinks n G → ℝ)
    (hf : Continuous f) (hinv : ∀ h u, f (gaugeSlice h u) = f u)
    (u : SpatialLinks n G) :
    (∫ v, kernel chi beta c u v * f v ∂spatialHaar) =
      ∫ v, rawKernel chi beta c u v * f v ∂spatialHaar := by
  let F : SpatialLinks n G → ℝ := fun v => spatialWeight chi beta c v * f v
  let k : SpatialLinks n G → ℝ := fun v => kineticWeight chi beta c u v
  have hF : Continuous F := by
    unfold F spatialWeight potential spatialHolonomy
    fun_prop
  have hk : Continuous k := by unfold k kineticWeight kineticAction; fun_prop
  have hFinv : ∀ h v, F (gaugeSlice h v) = F v := by
    intro h v
    simp only [F, spatialWeight_gauge chi hclass, hinv]
  have hp := gaugeAverage_pairing F k hF hk
  simp only [gaugeAverage_fixed F hFinv] at hp
  calc
    _ = spatialWeight chi beta c u * ∫ v, F v * gaugeAverage k v ∂spatialHaar := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      rw [kernel_eq_gauge_average chi hclass]
      change _ = spatialWeight chi beta c u *
        ((spatialWeight chi beta c v * f v) *
          ∫ h, kineticWeight chi beta c u (gaugeSlice h v) ∂temporalHaar)
      ring
    _ = spatialWeight chi beta c u * ∫ v, F v * k v ∂spatialHaar := by rw [hp]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      unfold F k rawKernel
      ring

open WilsonSlabOperator WilsonGroundLocalComparison
variable (n : ℕ) [NeZero n]

theorem ground_invariant (beta : ℝ) (hbeta : 0 ≤ beta)
    (h : SliceGauge n Q) (u : Slice n) :
    ground n beta hbeta (gaugeSlice h u) = ground n beta hbeta u :=
  (WilsonPositiveGroundState.exists_positive_top_eigenfunction n beta hbeta).choose_spec.2.2.2.1 h u

/-- The actually constructed ground also solves the unaveraged equation. -/
theorem ground_raw_equation (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) :
    (∫ v, rawKernel WilsonSingleLinkStaples.character beta 2 u v * ground n beta hbeta v
      ∂WilsonSlabOperator.measure n) = ‖transfer n beta‖ * ground n beta hbeta u := by
  exact (invariant_integral WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    beta 2 (ground n beta hbeta) (ground n beta hbeta).continuous
    (ground_invariant n beta hbeta) u).symm.trans (ground_equation n beta hbeta u)

/-- A genuine positive normalized transition with the same action as the
physical transfer on invariant tests. -/
def rawTransition (beta : ℝ) (hbeta : 0 ≤ beta) (u v : Slice n) : ℝ :=
  rawKernel WilsonSingleLinkStaples.character beta 2 u v * ground n beta hbeta v /
    (‖transfer n beta‖ * ground n beta hbeta u)

theorem rawTransition_pos (beta : ℝ) (hbeta : 0 ≤ beta) (u v : Slice n) :
    0 < rawTransition n beta hbeta u v := by
  exact div_pos (mul_pos (rawKernel_pos _ _ _ u v) (ground_pos n beta hbeta v))
    (mul_pos (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1
      (ground_pos n beta hbeta u))

theorem rawTransition_mass (beta : ℝ) (hbeta : 0 ≤ beta) (u : Slice n) :
    (∫ v, rawTransition n beta hbeta u v ∂WilsonSlabOperator.measure n) = 1 := by
  unfold rawTransition
  rw [integral_div, ground_raw_equation]
  exact div_self (mul_ne_zero
    (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1.ne'
    (ground_pos n beta hbeta u).ne')

/-- The two normalized transitions agree on every continuous invariant observable. -/
theorem invariant_transition (beta : ℝ) (hbeta : 0 ≤ beta) (f : Slice n → ℝ)
    (hf : Continuous f) (hinv : ∀ h u, f (gaugeSlice h u) = f u) (u : Slice n) :
    (∫ v, WilsonGroundLocalComparison.transition n beta hbeta u v * f v
      ∂WilsonSlabOperator.measure n) =
      ∫ v, rawTransition n beta hbeta u v * f v ∂WilsonSlabOperator.measure n := by
  have h := invariant_integral WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    beta 2 (fun v => ground n beta hbeta v * f v)
    ((ground n beta hbeta).continuous.mul hf)
    (fun h v => by dsimp only; rw [ground_invariant n beta hbeta, hinv]) u
  simp only [WilsonGroundLocalComparison.transition, GroundStateDirichlet.transition,
    rawTransition]
  simp_rw [div_mul_eq_mul_div, mul_assoc]
  rw [integral_div, integral_div]
  exact congrArg (fun z : ℝ => z / (‖transfer n beta‖ * ground n beta hbeta u)) h

end
end UnifiedTheory.Clay.YangMills.WilsonTemporalGauge

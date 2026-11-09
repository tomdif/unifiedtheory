/- Squared differences of the joint Gram factors. These estimates retain
interference and compare two positive spacings, not just their norms.
The representation is auxiliary; physical Hilbert identification is separate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredWholeClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredL2Error
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredWholeClock
open KFCausalClockFloorRelativeShift (scale scale_smooth)

theorem norm_sub_square (a b : ℂ) : ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_sub_le a b
  have h0 := norm_nonneg (a-b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

theorem energy_nonnegative (A : ℕ → ℂ) : 0 ≤ energyOf A := by
  unfold energyOf
  positivity

theorem energy_sub (A B : ℕ → ℂ) :
    energyOf (fun k => A k-B k) ≤ 2*energyOf A+2*energyOf B := by
  have h0 := norm_sub_square (A 0) (B 0)
  have h1 := norm_sub_square (A 1) (B 1)
  have h2 := norm_sub_square (A 2) (B 2)
  unfold energyOf
  linarith

theorem component_bound (A : ℕ → ℂ) (k : Fin 3) : ‖A k.val‖^2 ≤ 4*energyOf A := by
  have h0 := sq_nonneg ‖A 0‖
  have h1 := sq_nonneg ‖A 1‖
  have h2 := sq_nonneg ‖A 2‖
  fin_cases k <;> unfold energyOf <;> norm_num <;> linarith

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y : ℝ)

def finiteFactor (δ : ℝ) (x : Whole) (k : ℕ) : ℂ :=
  factor (reweight f (c x.1)) k α β δ (scale ε y x.1) x.2
def limitingFactor (x : Whole) (k : ℕ) : ℂ :=
  limitFactor (reweight f (c x.1)) k α β (scale ε y x.1) x.2
def error (δ : ℝ) (x : Whole) : ℝ :=
  energyOf (fun k => finiteFactor f c α β ε y δ x k-limitingFactor f c α β ε y x k)
def difference (δ η : ℝ) (x : Whole) : ℝ :=
  energyOf (fun k => finiteFactor f c α β ε y δ x k-finiteFactor f c α β ε y η x k)
def errorMass (δ : ℝ) : ℝ := Real.pi/4*∫ x, error f c α β ε y δ x ∂wholeMeasure

theorem error_nonnegative (δ : ℝ) (x : Whole) : 0 ≤ error f c α β ε y δ x := energy_nonnegative _
theorem difference_nonnegative (δ η : ℝ) (x : Whole) : 0 ≤ difference f c α β ε y δ η x := energy_nonnegative _
theorem errorMass_nonnegative (δ : ℝ) : 0 ≤ errorMass f c α β ε y δ :=
  mul_nonneg (by positivity) (integral_nonneg (error_nonnegative f c α β ε y δ))

theorem error_bound (δ : ℝ) (hδ : 0 < δ) (x : Whole) :
    error f c α β ε y δ x ≤ 2*energy f c α β ε y δ x+2*limitEnergy f c α β ε y x := by
  unfold error energy limitEnergy limitDensity finiteFactor limitingFactor
  rw [density_factors _ _ _ _ hδ]
  exact energy_sub _ _

theorem difference_bound (δ η : ℝ) (x : Whole) :
    difference f c α β ε y δ η x ≤ 2*error f c α β ε y δ x+2*error f c α β ε y η x := by
  have he := energy_sub
    (fun k => finiteFactor f c α β ε y δ x k-limitingFactor f c α β ε y x k)
    (fun k => finiteFactor f c α β ε y η x k-limitingFactor f c α β ε y x k)
  simpa only [sub_sub_sub_cancel_right] using he

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

include hε hy hc in
theorem error_continuous (δ : ℝ) : Continuous (error f c α β ε y δ) := by
  have hr := (scale_smooth ε y hε hy).continuous
  have hk (k : ℕ) := ((KFCausalCorrelatedClusteredClockContinuity.factor_continuous f c α β
    (scale ε y) hc hr k δ).sub (KFCausalCorrelatedClusteredClockContinuity.limitFactor_continuous
    f c α β (scale ε y) hc hr k)).norm.pow 2
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

include hε hy hc in
theorem difference_continuous (δ η : ℝ) : Continuous (difference f c α β ε y δ η) := by
  have hr := (scale_smooth ε y hε hy).continuous
  have hk (k : ℕ) := ((KFCausalCorrelatedClusteredClockContinuity.factor_continuous f c α β
    (scale ε y) hc hr k δ).sub (KFCausalCorrelatedClusteredClockContinuity.factor_continuous
    f c α β (scale ε y) hc hr k η)).norm.pow 2
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

include hα hβ hw hε hy hc2 in
theorem error_envelope : ∃ D : Whole → ℝ, Integrable D wholeMeasure ∧ (∀ x, 0 ≤ D x) ∧
    ∀ᵐ x ∂wholeMeasure, ∀ δ : ℝ, 0 < δ → ‖error f c α β ε y δ x‖ ≤ D x := by
  obtain ⟨D,hDi,hD0,hD⟩ := product_envelope f c α β ε y hα hβ hw hε hy hc2
  refine ⟨fun x => 4*D x,hDi.const_mul 4,fun x => mul_nonneg (by norm_num) (hD0 x),?_⟩
  filter_upwards [hD] with x hx δ hδ
  rw [Real.norm_eq_abs,abs_of_nonneg (error_nonnegative f c α β ε y δ x)]
  have hE := (le_abs_self (energy f c α β ε y δ x)).trans ((hx.1 δ hδ).1)
  have hL := (le_abs_self (limitEnergy f c α β ε y x)).trans hx.2.1
  have he := error_bound f c α β ε y δ hδ x
  linarith

include hα hβ hw hε hy hc hc2 in
theorem error_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (error f c α β ε y δ) wholeMeasure := by
  obtain ⟨D,hDi,_,hD⟩ := error_envelope f c α β ε y hα hβ hw hε hy hc2
  apply hDi.mono' (error_continuous f c α β ε y hε hy hc δ).aestronglyMeasurable
  filter_upwards [hD] with x hx
  exact hx δ hδ

theorem error_tendsto (x : Whole) :
    Tendsto (fun δ => error f c α β ε y δ x) (𝓝[>] 0) (𝓝 0) := by
  have hk (k : ℕ) := (((factor_tendsto (reweight f (c x.1)) k α β
    (scale ε y x.1) x.2).sub_const (limitingFactor f c α β ε y x k)).norm.pow 2)
  have he := ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)
  simpa only [limitingFactor,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_div,add_zero] using he

include hα hβ hw hε hy hc hc2 in
theorem errorMass_tendsto : Tendsto (errorMass f c α β ε y) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨D,hDi,_,hD⟩ := error_envelope f c α β ε y hα hβ hw hε hy hc2
  have he : Tendsto (fun δ => ∫ x, error f c α β ε y δ x ∂wholeMeasure) (𝓝[>] 0) (𝓝 (∫ _ : Whole, (0:ℝ) ∂wholeMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence D
    · exact Filter.Eventually.of_forall (fun δ => (error_continuous f c α β ε y hε hy hc δ).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [hD] with x hx
      exact hx δ hδ
    · exact hDi
    · exact Filter.Eventually.of_forall (error_tendsto f c α β ε y)
  simpa only [integral_zero,mul_zero] using he.const_mul (Real.pi/4)

include hα hβ hw hε hy hc hc2 in
theorem difference_integrable (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    Integrable (difference f c α β ε y δ η) wholeMeasure := by
  have hi := ((error_integrable f c α β ε y hα hβ hw hε hy hc hc2 δ hδ).const_mul 2).add
    ((error_integrable f c α β ε y hα hβ hw hε hy hc hc2 η hη).const_mul 2)
  apply hi.mono' (difference_continuous f c α β ε y hε hy hc δ η).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (difference_nonnegative f c α β ε y δ η x)]
  exact difference_bound f c α β ε y δ η x

include hα hβ hw hε hy hc hc2 in
theorem difference_integral_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    Real.pi/4*∫ x, difference f c α β ε y δ η x ∂wholeMeasure ≤
      2*errorMass f c α β ε y δ+2*errorMass f c α β ε y η := by
  have hiδ := (error_integrable f c α β ε y hα hβ hw hε hy hc hc2 δ hδ).const_mul 2
  have hiη := (error_integrable f c α β ε y hα hβ hw hε hy hc hc2 η hη).const_mul 2
  have he := integral_mono (difference_integrable f c α β ε y hα hβ hw hε hy hc hc2 δ η hδ hη)
    (hiδ.add hiη) (difference_bound f c α β ε y δ η)
  have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ Real.pi/4 by positivity)
  dsimp only [Pi.add_apply] at hp
  rw [integral_add hiδ hiη,integral_const_mul,integral_const_mul] at hp
  unfold errorMass
  nlinarith [Real.pi_pos]

#print axioms norm_sub_square
#print axioms energy_nonnegative
#print axioms energy_sub
#print axioms component_bound
#print axioms error_nonnegative
#print axioms difference_nonnegative
#print axioms errorMass_nonnegative
#print axioms error_bound
#print axioms difference_bound
#print axioms error_continuous
#print axioms difference_continuous
#print axioms error_envelope
#print axioms error_integrable
#print axioms error_tendsto
#print axioms errorMass_tendsto
#print axioms difference_integrable
#print axioms difference_integral_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredL2Error

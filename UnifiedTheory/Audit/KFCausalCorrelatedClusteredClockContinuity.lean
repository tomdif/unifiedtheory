/- Joint measurability on clock times transverse coordinates, allowing
independent continuous clock amplitudes in every correlated block. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockContinuity
noncomputable section
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalClusteredClockFactors (E Ed G Gd F Fd Z Zd N Nd B0 B1)

variable {m : ℕ} (f : Family m) (c : ℝ → Fin m → ℂ) (α β : ℝ)
  (r v : ℝ → ℂ) (hc : ∀ i, Continuous (fun s => c s i)) (hr : Continuous r) (hv : Continuous v)

include hc hr in
theorem factor_continuous (k : ℕ) (δ : ℝ) :
    Continuous (fun x : ℝ × Joint => factor (reweight f (c x.1)) k α β δ (r x.1) x.2) := by
  unfold factor reweight KFCausalClusteredClockFactors.factor E G F Z N
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
    KFCausalClusteredWidthProfiles.quotient
  unfold KFCausalReciprocalWedgeGeometry.gamma KFCausalChargedPairCoordinates.fieldSlope
  dsimp only
  fun_prop

include hc hr in
theorem limitFactor_continuous (k : ℕ) :
    Continuous (fun x : ℝ × Joint => limitFactor (reweight f (c x.1)) k α β (r x.1) x.2) := by
  unfold limitFactor reweight KFCausalClusteredClockFactors.limitFactor E G F Z N
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  unfold KFCausalReciprocalWedgeGeometry.gamma KFCausalChargedPairCoordinates.fieldSlope
  dsimp only
  fun_prop

include hc hr hv in
theorem slope_continuous (k : ℕ) (δ : ℝ) :
    Continuous (fun x : ℝ × Joint => KFCausalCorrelatedClusteredProfiles.slope
      (reweight f (c x.1)) k α β δ (r x.1) (v x.1) x.2) := by
  unfold KFCausalCorrelatedClusteredProfiles.slope reweight KFCausalClusteredClockFactors.slope
    B0 B1 E Ed G Gd F Fd Z Zd N Nd KFCausalReciprocalWedgeGeometry.chart
    KFCausalReciprocalNeutralKernel.neutral KFCausalClusteredWidthProfiles.quotient
  unfold KFCausalReciprocalWedgeGeometry.gamma KFCausalChargedPairCoordinates.fieldSlope
  dsimp only
  fun_prop

include hc hr hv in
theorem limitSlope_continuous (k : ℕ) :
    Continuous (fun x : ℝ × Joint => limitSlope (reweight f (c x.1)) k α β (r x.1) (v x.1) x.2) := by
  unfold limitSlope reweight KFCausalClusteredClockFactors.limitSlope
    B0 B1 E Ed G Gd F Fd Z Zd N Nd KFCausalReciprocalWedgeGeometry.chart
    KFCausalReciprocalNeutralKernel.neutral
  unfold KFCausalReciprocalWedgeGeometry.gamma KFCausalChargedPairCoordinates.fieldSlope
  dsimp only
  fun_prop

include hc hr in
theorem density_continuous (δ : ℝ) (hδ : 0 < δ) :
    Continuous (fun x : ℝ × Joint => density (reweight f (c x.1)) α β δ (r x.1) x.2) := by
  simp_rw [density_factors _ _ _ _ hδ]
  unfold energyOf
  exact (((factor_continuous f c α β r hc hr 0 δ).norm.pow 2).add
    (((factor_continuous f c α β r hc hr 1 δ).norm.pow 2).div_const 2)).add
    (((factor_continuous f c α β r hc hr 2 δ).norm.pow 2).div_const 4)

include hc hr in
theorem limitDensity_continuous :
    Continuous (fun x : ℝ × Joint => limitDensity (reweight f (c x.1)) α β (r x.1) x.2) := by
  unfold limitDensity energyOf
  exact (((limitFactor_continuous f c α β r hc hr 0).norm.pow 2).add
    (((limitFactor_continuous f c α β r hc hr 1).norm.pow 2).div_const 2)).add
    (((limitFactor_continuous f c α β r hc hr 2).norm.pow 2).div_const 4)

include hc hr hv in
theorem response_continuous (δ : ℝ) :
    Continuous (fun x : ℝ × Joint => response (reweight f (c x.1)) α β δ (r x.1) (v x.1) x.2) := by
  have h (k : ℕ) := (factor_continuous f c α β r hc hr k δ).star.mul
    (slope_continuous f c α β r v hc hr hv k δ)
  unfold response responseOf
  simpa only [Complex.star_def] using
    ((continuous_const.mul (Complex.continuous_re.comp (h 0))).add ((continuous_const.mul (Complex.continuous_re.comp (h 1))).div_const 2)).add ((continuous_const.mul (Complex.continuous_re.comp (h 2))).div_const 4)

include hc hr hv in
theorem limitResponse_continuous :
    Continuous (fun x : ℝ × Joint => limitResponse (reweight f (c x.1)) α β (r x.1) (v x.1) x.2) := by
  have h (k : ℕ) := (limitFactor_continuous f c α β r hc hr k).star.mul
    (limitSlope_continuous f c α β r v hc hr hv k)
  unfold limitResponse responseOf
  simpa only [Complex.star_def] using
    ((continuous_const.mul (Complex.continuous_re.comp (h 0))).add ((continuous_const.mul (Complex.continuous_re.comp (h 1))).div_const 2)).add ((continuous_const.mul (Complex.continuous_re.comp (h 2))).div_const 4)

#print axioms factor_continuous
#print axioms limitFactor_continuous
#print axioms slope_continuous
#print axioms limitSlope_continuous
#print axioms density_continuous
#print axioms limitDensity_continuous
#print axioms response_continuous
#print axioms limitResponse_continuous
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockContinuity

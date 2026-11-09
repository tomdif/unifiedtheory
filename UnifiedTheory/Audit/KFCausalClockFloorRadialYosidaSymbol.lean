/- The bounded rational cutoff of the actual charge-averaged growing
kinetic multiplier. This constructs the physical operator and its charge
covariance; preservation of the growing form is a separate obligation. -/
import UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
import UnifiedTheory.Audit.KFCausalChargeGaussianGeometry

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSymbol
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalNormalizedChargeFlow
open KFCausalClockFloorRotatedAntiSymbol
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalContractiveMultiplier

def radial (ε h : ℝ) (x : Joint 2 4) : ℝ :=
  (chargedWeight ε h 0 x+chargedWeight ε h 1 x)/2

theorem radial_nonnegative (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 2 4) :
    0 ≤ radial ε h x :=
  div_nonneg (add_nonneg (chargedWeight_nonnegative ε hε h 0 x)
    (chargedWeight_nonnegative ε hε h 1 x)) (by norm_num)

theorem radial_coordinates (ε h : ℝ) (x : Joint 2 4) :
    radial ε h x =
      (momentumScale h^2*(x (.inl 0)^2+x (.inl 1)^2)+
        x (.inr 1)^2+x (.inr 2)^2)/(2*clock ε (x (.inr 0))) := by
  simp only [radial,chargedWeight,momentum,position,symmetricIndex,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem radial_flow (ε h : ℝ) (hh : h ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    radial ε h (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x)=
      radial ε h x := by
  have hr := KFCausalChargeGaussianGeometry.radius_flow (momentumScale h)
    (momentumScale_ne_zero h hh) θ x
  rw [KFCausalChargeGaussianGeometry.radius_coordinates,
    KFCausalChargeGaussianGeometry.radius_coordinates] at hr
  rw [radial_coordinates,radial_coordinates,flow_clock,hr]

def symbol (ε h N : ℝ) (x : Joint 2 4) : ℝ :=
  N*radial ε h x/(N+radial ε h x)

theorem symbol_nonnegative (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) : 0 ≤ symbol ε h N x := by
  unfold symbol
  exact div_nonneg (mul_nonneg hN.le (radial_nonnegative ε hε h x))
    (add_nonneg hN.le (radial_nonnegative ε hε h x))

theorem symbol_le (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) : symbol ε h N x ≤ N := by
  have hr := radial_nonnegative ε hε h x
  unfold symbol
  apply (div_le_iff₀ (by positivity : 0 < N+radial ε h x)).mpr
  nlinarith

theorem symbol_le_radial (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) : symbol ε h N x ≤ radial ε h x := by
  have hr := radial_nonnegative ε hε h x
  unfold symbol
  apply (div_le_iff₀ (by positivity : 0 < N+radial ε h x)).mpr
  nlinarith [sq_nonneg (radial ε h x)]

theorem symbol_continuous (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) :
    Continuous (symbol ε h N) := by
  have hr : Continuous (radial ε h) :=
    ((chargedWeight_continuous ε hε h 0).add
      (chargedWeight_continuous ε hε h 1)).div_const 2
  exact (continuous_const.mul hr).div (continuous_const.add hr)
    (fun x => (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h x)).ne')

theorem symbol_flow (ε h N : ℝ) (hh : h ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    symbol ε h N (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x)=
      symbol ε h N x := by
  simp only [symbol,radial_flow ε h hh]

private theorem normalized_bound (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) : ‖((symbol ε h N x/N : ℝ):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    (div_nonneg (symbol_nonnegative ε hε h N hN x) hN.le)]
  exact (div_le_one hN).mpr (symbol_le ε hε h N hN x)

def action (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) : Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    (((N:ℂ) • multiplyL (fun x => ((symbol ε h N x/N:ℝ):ℂ))
      (Complex.continuous_ofReal.comp ((symbol_continuous ε hε h N hN).div_const N)).measurable
      (normalized_bound ε hε h N hN)).comp
        (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

theorem action_coe (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (f : Hilbert) :
    chargeCoordinates (action ε hε h N hN f) =ᵐ[volume]
      fun x => (symbol ε h N x:ℂ)*(chargeCoordinates f) x := by
  change chargeCoordinates (chargeCoordinates.symm _) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  filter_upwards [Lp.coeFn_smul (N:ℂ) (multiplyL _ _ _ (chargeCoordinates f)),
    multiplyL_coe (fun x => ((symbol ε h N x/N:ℝ):ℂ))
      (Complex.continuous_ofReal.comp ((symbol_continuous ε hε h N hN).div_const N)).measurable
      (normalized_bound ε hε h N hN) (chargeCoordinates f)] with x hs hm
  change ((N:ℂ) • multiplyL _ _ _ (chargeCoordinates f)) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hm,Complex.ofReal_div]
  field_simp [hN.ne']

theorem action_norm (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (f : Hilbert) :
    ‖action ε hε h N hN f‖ ≤ N*‖f‖ := by
  rw [← chargeCoordinates.norm_map (action ε hε h N hN f),← chargeCoordinates.norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [action_coe ε hε h N hN f] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (symbol_nonnegative ε hε h N hN x)]
  exact mul_le_mul_of_nonneg_right (symbol_le ε hε h N hN x) (norm_nonneg _)

theorem action_charge (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    action ε hε h N hN (KFCausalPhysicalCircleAction.action h hh θ f)=
      KFCausalPhysicalCircleAction.action h hh θ (action ε hε h N hN f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  let c := momentumScale h
  have hc : c ≠ 0 := momentumScale_ne_zero h hh
  filter_upwards [action_coe ε hε h N hN (KFCausalPhysicalCircleAction.action h hh θ f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates f),
    KFCausalMixedCircleAction.action_coe c hc θ (chargeCoordinates (action ε hε h N hN f)),
    (flow_preserves_volume c hc θ).quasiMeasurePreserving.ae (action_coe ε hε h N hN f)]
      with x hm hu ha hf
  rw [hm,KFCausalPhysicalCircleAction.action_coordinates,hu,
    KFCausalPhysicalCircleAction.action_coordinates,ha]
  change chargeCoordinates (action ε hε h N hN f) (flowEquiv c hc θ x)=_ at hf
  simp only [Function.comp_apply]
  rw [hf,symbol_flow ε h N hh θ x]

#print axioms radial_nonnegative
#print axioms radial_coordinates
#print axioms radial_flow
#print axioms symbol_nonnegative
#print axioms symbol_le
#print axioms symbol_le_radial
#print axioms symbol_continuous
#print axioms symbol_flow
#print axioms action_coe
#print axioms action_norm
#print axioms action_charge
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSymbol

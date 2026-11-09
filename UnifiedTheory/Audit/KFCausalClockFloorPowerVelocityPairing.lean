/- Powers of the actual physical multipliers and their signed velocity
pairings on arbitrary L2 vectors, not only on coherent packets. -/
import UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator driftOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing (real_multiplier_pairing)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol shiftedDefect_physical_coe)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing (realDefect_chart)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar (realDefect_le_one)
open UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar
open UnifiedTheory.Audit.KFCausalMultiplierVelocityPairing (velocity_pairing_bound)

theorem multiplier_power_coe {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (m : X → ℂ)
    (hA : ∀ f, A f =ᵐ[μ] fun x => m x*f x) (n : ℕ) (f : Lp ℂ 2 μ) :
    (A^n) f =ᵐ[μ] fun x => (m x)^n*f x := by
  induction n with
  | zero => simp only [pow_zero,ContinuousLinearMap.one_apply,one_mul]; exact Filter.EventuallyEq.rfl
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply]
    filter_upwards [hA ((A^n) f),ih] with x hx hy
    rw [hx,hy,pow_succ]
    ring

theorem selfadjoint_power_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (hA : ∀ f g, inner ℂ (A f) g = inner ℂ f (A g))
    (n : ℕ) (f g : E) : inner ℂ ((A^n) f) g = inner ℂ f ((A^n) g) := by
  induction n generalizing f g with
  | zero => simp only [pow_zero,ContinuousLinearMap.one_apply]
  | succ n ih =>
    calc
      _ = inner ℂ ((A^n) f) (A g) := by rw [pow_succ',ContinuousLinearMap.mul_apply,hA]
      _ = inner ℂ f ((A^n) (A g)) := ih f (A g)
      _ = _ := by rw [pow_succ,ContinuousLinearMap.mul_apply]

variable (ε : ℝ) (hε : 0 < ε)
local notation "D" => defectOperator ε hε

theorem defect_power_coe (n : ℕ) (f : Hilbert) :
    (D^n) f =ᵐ[volume] fun x => ((defect ε x.1)^n:ℝ)*f x := by
  simpa only [Complex.ofReal_pow] using multiplier_power_coe volume D
    (fun x => (defect ε x.1:ℂ)) (defectOperator_coe ε hε) n f

theorem defect_power_inner (n : ℕ) (f g : Hilbert) :
    inner ℂ ((D^n) f) g = inner ℂ f ((D^n) g) :=
  selfadjoint_power_inner D (defect_inner ε hε) n f g

theorem defect_power_im_zero (n : ℕ) (f : Hilbert) : (inner ℂ f ((D^n) f)).im = 0 := by
  have he := inner_im_symm (𝕜 := ℂ) ((D^n) f) f
  rw [defect_power_inner] at he
  change (inner ℂ f ((D^n) f)).im = -(inner ℂ f ((D^n) f)).im at he
  linarith

def powerDriftOperator (n : ℕ) : Hilbert →L[ℂ] Hilbert :=
  ((n+1:ℝ):ℂ) • (D^n).comp (driftOperator ε hε)

theorem powerDriftOperator_coe (n : ℕ) (f : Hilbert) :
    powerDriftOperator ε hε n f =ᵐ[volume] fun x => (powerDrift ε n (defect ε x.1):ℂ)*f x := by
  filter_upwards [Lp.coeFn_smul ((n+1:ℝ):ℂ) ((D^n) (driftOperator ε hε f)),
    defect_power_coe ε hε n (driftOperator ε hε f),driftOperator_coe ε hε f] with x hs hd hp
  change (((n+1:ℝ):ℂ) • ((D^n) (driftOperator ε hε f))) x = _
  rw [hs,Pi.smul_apply,smul_eq_mul,hd,hp]
  simp only [powerDrift,Complex.ofReal_mul]
  ring

theorem powerDrift_pairing_nonpositive (n : ℕ) (f : Hilbert) :
    (inner ℂ f (powerDriftOperator ε hε n f)).re ≤ 0 := by
  rw [real_multiplier_pairing volume _ _ _ (powerDriftOperator_coe ε hε n f)]
  apply integral_nonpos_of_ae
  filter_upwards [] with x
  apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  apply powerDrift_nonpositive ε hε n _
  exact ⟨(KFCausalClockFloorCanonicalDefect.defect_positive ε x.1 hε).le,
    (realDefect_chart ε hε x.1) ▸ realDefect_le_one ε hε _⟩

theorem power_velocity_pairing_error (h : ℝ) (hne : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (n : ℕ) (f : Hilbert) :
    |(-2/h)*(inner ℂ f (((shiftedDefect ε hε h hb)^(n+1)) f)).im-
      (inner ℂ f (powerDriftOperator ε hε n f)).re| ≤ (errorConstant ε n*|h|)*‖f‖^2 := by
  have he := velocity_pairing_bound (fun x => (physicalSymbol ε h x)^(n+1))
    (fun x => powerDrift ε n (defect ε x.1)) (fun _ => 1) (-2/h) (errorConstant ε n*|h|)
    f (((shiftedDefect ε hε h hb)^(n+1)) f) (powerDriftOperator ε hε n f) f
    (multiplier_power_coe volume _ _ (shiftedDefect_physical_coe ε hε h hb) (n+1) f)
    (powerDriftOperator_coe ε hε n f) (Filter.Eventually.of_forall (fun _ => by simp))
    (fun x => by
      have hs := powerVelocity_error ε hε h hne hb n (KFCausalRegularizedLongitudinalChart.chart ε x.1)
      rw [realDefect_chart ε hε] at hs
      simpa only [mul_one] using hs)
  have hs : (inner ℂ f f).re = ‖f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  simpa only [hs] using he

#print axioms multiplier_power_coe
#print axioms selfadjoint_power_inner
#print axioms defect_power_coe
#print axioms defect_power_inner
#print axioms defect_power_im_zero
#print axioms powerDriftOperator_coe
#print axioms powerDrift_pairing_nonpositive
#print axioms power_velocity_pairing_error

end
end UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing

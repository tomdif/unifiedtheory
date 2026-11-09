/- The actual field-derivative correction is absorbed into the positive
longitudinal response plus a weighted derivative moment. This applies to
real field multiples of arbitrary complex L2 states and their continuous
charge orbits. The remaining moment has no asserted energy control. -/
import UnifiedTheory.Audit.KFCausalMatterScalarAbsorption
import UnifiedTheory.Audit.KFCausalMatterCorrectionQuadraticBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMatterLongitudinalAbsorption
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection)
open UnifiedTheory.Audit.KFCausalRealShearCorrectionBound (shearCorrection_coe)
open UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing (mixed_real_inner)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope fieldSlope)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (weight moment moment_integral moment_continuous)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient scalar_absorption)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "C" => shearCorrection ε hε h hb
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb

theorem common_phase_absorption (a b : Configuration → ℝ) (g u d : Hilbert)
    (hu : u =ᵐ[volume] fun x => (a x:ℂ)*g x)
    (hd : d =ᵐ[volume] fun x => (b x:ℂ)*g x) :
    |derivativeCorrection ε hε h hb u d| ≤ responseL u+coefficient ε h*moment ε hε d := by
  have hE := ((L2.integrable_inner (𝕜 := ℂ) u (C d)).re).const_mul (2:ℝ)
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) u (C d))
  change (∫ x, (inner ℂ (u x) (C d x)).re) = (∫ x, inner ℂ (u x) (C d x)).re at hr
  have he : derivativeCorrection ε hε h hb u d = ∫ x, 2*(inner ℂ (u x) (C d x)).re := by
    unfold derivativeCorrection
    rw [L2.inner_def,← hr,integral_const_mul]
  have hL := (KFCausalClockFloorVacuumMomentumResponse.density_integrable ε hε h hb u).const_mul (1/ε)
  have hM := ((moment_integral ε hε d).1).const_mul (coefficient ε h)
  have hp : ∀ᵐ x ∂volume, |2*(inner ℂ (u x) (C d x)).re| ≤
      (1/ε)*((physicalSymbol ε h x*(1-physicalSymbol ε h x)).re*‖u x‖^2)+
        coefficient ε h*(weight ε x*‖d x‖^2) := by
    filter_upwards [hu,hd,shearCorrection_coe ε hε h hb d] with x hu hd hc
    rw [hc,hu,hd,mixed_real_inner]
    simp only [Complex.div_ofReal_re,Complex.sub_re,Complex.ofReal_re,
      norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    have hs := mul_le_mul_of_nonneg_right (scalar_absorption ε hε h hb x (a x) (b x)) (sq_nonneg ‖g x‖)
    have ha : |2*(((KFCausalClockFloorCanonicalDefect.defect ε x.1-
        (physicalSymbol ε h x).re)/ε)*a x*b x*‖g x‖^2)| =
        |2*((KFCausalClockFloorCanonicalDefect.defect ε x.1-(physicalSymbol ε h x).re)/ε)*a x*b x| *‖g x‖^2 := by
      rw [show 2*(((KFCausalClockFloorCanonicalDefect.defect ε x.1-
          (physicalSymbol ε h x).re)/ε)*a x*b x*‖g x‖^2) =
          (2*((KFCausalClockFloorCanonicalDefect.defect ε x.1-(physicalSymbol ε h x).re)/ε)*a x*b x)*‖g x‖^2 by ring,
        abs_mul,abs_of_nonneg (sq_nonneg ‖g x‖)]
    rw [ha]
    convert hs using 1
    ring
  rw [he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ x, (1/ε)*((physicalSymbol ε h x*(1-physicalSymbol ε h x)).re*‖u x‖^2)+
        coefficient ε h*(weight ε x*‖d x‖^2) := integral_mono_ae hE.abs (hL.add hM) hp
    _ = _ := by
      rw [integral_add hL hM,integral_const_mul,integral_const_mul,
        ← KFCausalClockFloorVacuumMomentumResponse.pairing_integral ε hε h hb u,
        ← (moment_integral ε hε d).2]
      rfl

theorem field_absorption (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g u d : Hilbert)
    (hu : (g,u) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x) :
    |derivativeCorrection ε hε h hb u d| ≤ responseL u+coefficient ε h*moment ε hε d := by
  apply common_phase_absorption ε hε h hb
    (fun x => (l x.2)^(i.val+1))
    (fun x => (i.val+1:ℕ)*(l x.2)^i.val*fieldSlope l x.2) g u d
  · simpa only [Complex.ofReal_pow] using (fieldPower_graph l i g u).mp hu
  · filter_upwards [hd] with x hx
    rw [hx]
    simp only [powerSlope,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]

theorem average_absorption (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g u d : ℝ → Hilbert)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hd : ∀ θ, d θ =ᵐ[volume] fun x => powerSlope l i x*g θ x)
    (hc : Continuous u) (hcd : Continuous d) :
    |∫ θ, derivativeCorrection ε hε h hb (u θ) (d θ) ∂angleMeasure| ≤
      (∫ θ, responseL (u θ) ∂angleMeasure)+
        coefficient ε h*(∫ θ, moment ε hε (d θ) ∂angleMeasure) := by
  have hC : Continuous (fun θ => derivativeCorrection ε hε h hb (u θ) (d θ)) :=
    continuous_const.mul (Complex.continuous_re.comp (hc.inner ((C).continuous.comp hcd)))
  have hL := (continuous_angle_memLp _
    ((KFCausalClockFloorVacuumMomentumResponse.response_continuous ε hε h hb).comp hc)).integrable (by norm_num)
  have hM := (continuous_angle_memLp _ ((moment_continuous ε hε).comp hcd)).integrable (by norm_num)
  change Integrable (fun θ => responseL (u θ)) angleMeasure at hL
  change Integrable (fun θ => moment ε hε (d θ)) angleMeasure at hM
  have hi := abs_integral_le_integral_abs.trans
    (integral_mono ((continuous_angle_memLp _ hC).integrable (by norm_num)).abs
      (hL.add (hM.const_mul (coefficient ε h)))
      (fun θ => field_absorption ε hε h hb l i (g θ) (u θ) (d θ) (hu θ) (hd θ)))
  simp only [Pi.add_apply] at hi
  rw [integral_add hL (hM.const_mul (coefficient ε h)),integral_const_mul] at hi
  exact hi

#print axioms common_phase_absorption
#print axioms field_absorption
#print axioms average_absorption
end
end UnifiedTheory.Audit.KFCausalMatterLongitudinalAbsorption

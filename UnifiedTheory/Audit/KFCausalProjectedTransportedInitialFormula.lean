/- The initial transported charge mean has an explicit polynomial
representative. Closed real-multiplier graphs justify the polynomial
means; only bounded clock maps are commuted with the Bochner integral. -/
import UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial
import UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedTransportedInitialFormula
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials (modes)
open UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs (scalar)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus (transport transport_coe)
open UnifiedTheory.Audit.KFCausalActualTransportedField (profile transport_symbol)
open UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit (weightedInput angle_continuous)
open UnifiedTheory.Audit.KFCausalStructuredTransportedMatterOrbit (transportedInput)
open UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs (meanWeightedInput)
open UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant (meanInitial)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier (realPullback_graph)
open UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial
  (mode_real mode_re_continuous transportedValue weighted_modes_sum physical_transported_value)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (displacement)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (S : StructuredState) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)

theorem mean_mode_coe (k : Fin 3) (t : Interval) :
    meanWeightedInput ε h hε hh hb S (modes l i k).toWeight t =ᵐ[volume]
      fun x => (modes l i k).value x*meanInputAt ε h hε hh hb S t x := by
  have hg := KFCausalProjectedFieldSlopeMultiplier.mean_real_multiplier_graph ε h hε hh hb S
    (modes l i k).toWeight (fun x => ((modes l i k).value x).re)
    (mode_re_continuous l i k).measurable (mode_real l i k) t
  have he := (realPullback_graph (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun x => ((modes l i k).value x).re) (mode_re_continuous l i k).measurable _ _).mp hg
  simpa only [← mode_real] using he

theorem mean_initial_modes : meanInitial ε h hε hh hb S l i =
    ∑ k, transport (scalar (modes l i k) h • profile ε h hε hb hh) 0
      (meanWeightedInput ε h hε hh hb S (modes l i k).toWeight 0) := by
  have hc (k : Fin 3) : Continuous (fun θ => weightedInput ε h hε hh hb S
      (modes l i k).toWeight (2*Real.pi*θ) 0) :=
    (angle_continuous ε h hε hh hb S (modes l i k).toWeight
      ⟨0,by constructor <;> norm_num⟩).1.comp (continuous_const.mul continuous_id)
  have hi (k : Fin 3) := (continuous_angle_memLp _ (hc k)).integrable (by norm_num)
  have ht (k : Fin 3) : Integrable (fun θ =>
      transport (scalar (modes l i k) h • profile ε h hε hb hh) 0
        (weightedInput ε h hε hh hb S (modes l i k).toWeight (2*Real.pi*θ) 0)) angleMeasure :=
    (continuous_angle_memLp _ ((transport _ 0).continuous.comp (hc k))).integrable (by norm_num)
  unfold meanInitial transportedInput
  rw [integral_finset_sum Finset.univ (fun k _ => ht k)]
  apply Finset.sum_congr rfl
  intro k _
  exact (transport _ 0).integral_comp_comm (hi k)

theorem transported_mode_coe (k : Fin 3) :
    transport (scalar (modes l i k) h • profile ε h hε hb hh) 0
      (meanWeightedInput ε h hε hh hb S (modes l i k).toWeight 0) =ᵐ[volume]
      fun x => Complex.exp (-(modes l i k).degree*displacement ε h x.1)*
        (modes l i k).value x*meanInputAt ε h hε hh hb S 0 x := by
  filter_upwards [transport_coe (scalar (modes l i k) h • profile ε h hε hb hh) 0
      (meanWeightedInput ε h hε hh hb S (modes l i k).toWeight 0),
    mean_mode_coe ε h hε hh hb S l i k ⟨0,by constructor <;> norm_num⟩] with x ht hp
  change meanWeightedInput ε h hε hh hb S (modes l i k).toWeight 0 x = _ at hp
  rw [ht,hp,transport_symbol ε h hε hb hh (modes l i k)]
  rw [show ((0-1:ℝ):ℂ)*((modes l i k).degree:ℂ)*displacement ε h x.1 =
    -((modes l i k).degree:ℂ)*displacement ε h x.1 by push_cast; ring]
  ring

theorem mean_initial_coe : meanInitial ε h hε hh hb S l i =ᵐ[volume]
    fun x => transportedValue (displacement ε h x.1) l i x*meanInputAt ε h hε hh hb S 0 x := by
  rw [mean_initial_modes]
  have hs := KFCausalTransportedMatterInterpolation.finite_sum_representatives Finset.univ
    (fun k => transport (scalar (modes l i k) h • profile ε h hε hb hh) 0
      (meanWeightedInput ε h hε hh hb S (modes l i k).toWeight 0))
    (fun k x => Complex.exp (-(modes l i k).degree*displacement ε h x.1)*
      (modes l i k).value x*meanInputAt ε h hε hh hb S 0 x)
    (fun k _ => transported_mode_coe ε h hε hh hb S l i k)
  filter_upwards [hs] with x hx
  rw [hx,← Finset.sum_mul,weighted_modes_sum]

omit l in
theorem physical_initial_coe : meanInitial ε h hε hh hb S pointField i =ᵐ[volume]
    fun x => ((x.2 4:ℂ)+(3*Complex.exp (-displacement ε h x.1/2)-2)*
      ((x.2 2:ℂ)+(x.2 3:ℂ)))^(i.val+1)*meanInputAt ε h hε hh hb S 0 x := by
  simpa only [physical_transported_value] using mean_initial_coe ε h hε hh hb S pointField i

#print axioms mean_mode_coe
#print axioms mean_initial_modes
#print axioms transported_mode_coe
#print axioms mean_initial_coe
#print axioms physical_initial_coe
end
end UnifiedTheory.Audit.KFCausalProjectedTransportedInitialFormula

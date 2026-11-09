/- The physical gauge phase is strongly differentiable on the actual
chart-coordinate multiplication domain. This condition is on the test
vector, and asserts no chart-domain preservation by physical evolution. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy
import UnifiedTheory.Audit.KFCausalL2PhaseDerivative
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (rate)

def chartOperator (ε : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  KFCausalUnitaryRealMultiplier.realPullback (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun x : Configuration => chart ε x.1) ((chart_continuous ε).comp continuous_fst).measurable

theorem chartOperator_selfAdjoint (ε : ℝ) : IsSelfAdjoint (chartOperator ε) :=
  KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint _ _ _

theorem chartOperator_graph (ε : ℝ) (f g : Hilbert) :
    (f,g) ∈ (chartOperator ε).graph ↔ g =ᵐ[volume] fun x => (chart ε x.1:ℂ)*f x :=
  KFCausalUnitaryRealMultiplier.realPullback_graph (LinearIsometryEquiv.refl ℂ Hilbert) _ _ f g

def gauge (ε h t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := modulation ε (rate h t)

theorem gauge_coe (ε h : ℝ) (hne : h ≠ 0) (t : ℝ) (f : Hilbert) :
    gauge ε h t f =ᵐ[volume] fun x =>
      Complex.exp (Complex.I*((t*((-2/h)*chart ε x.1):ℝ):ℂ))*f x := by
  filter_upwards [modulation_coe ε (rate h t) f] with x hx
  change modulation ε (rate h t) f x = _
  rw [hx,phase,Real.fourierChar_apply]
  have he : 2*Real.pi*(rate h t*chart ε x.1) = t*((-2/h)*chart ε x.1) := by
    unfold rate
    field_simp
  rw [he,mul_comm (↑(t*((-2/h)*chart ε x.1)):ℂ) Complex.I]

theorem gauge_add (ε h : ℝ) (hne : h ≠ 0) (s t : ℝ) (f : Hilbert) :
    gauge ε h (s+t) f = gauge ε h s (gauge ε h t f) := by
  apply Lp.ext
  filter_upwards [gauge_coe ε h hne (s+t) f,gauge_coe ε h hne s (gauge ε h t f),
    gauge_coe ε h hne t f] with x h1 h2 h3
  rw [h1,h2,h3]
  conv_rhs => rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem gauge_inverse (ε h t : ℝ) (f : Hilbert) : gauge ε h (-t) (gauge ε h t f) = f := by
  change modulation ε (rate h (-t)) (modulation ε (rate h t) f) = f
  rw [show rate h (-t) = -rate h t by unfold rate; ring,modulation_inverse]

theorem gauge_pairing (ε h t : ℝ) (f g : Hilbert) :
    inner ℂ (gauge ε h (-t) f) g = inner ℂ f (gauge ε h t g) := by
  have he := (gauge ε h (-t)).inner_map_map f (gauge ε h t g)
  rwa [gauge_inverse] at he

theorem gauge_derivative_zero (ε h : ℝ) (hne : h ≠ 0) (f g : Hilbert)
    (hfg : (f,g) ∈ (chartOperator ε).graph) :
    HasDerivAt (fun t => gauge ε h t f) ((Complex.I*((-2/h:ℝ):ℂ)) • g) 0 := by
  have hg : (((-2/h:ℝ):ℂ) • g : Hilbert) =ᵐ[volume]
      fun x => (((-2/h)*chart ε x.1:ℝ):ℂ)*f x := by
    filter_upwards [Lp.coeFn_smul (((-2/h:ℝ):ℂ)) g,(chartOperator_graph ε f g).mp hfg] with x h1 h2
    simp only [Pi.smul_apply,smul_eq_mul] at h1
    rw [h1,h2,Complex.ofReal_mul,mul_assoc]
  have hd := KFCausalL2PhaseDerivative.derivative_zero (fun t => gauge ε h t f)
    (fun x => (-2/h)*chart ε x.1) f (((-2/h:ℝ):ℂ) • g) (fun t => gauge_coe ε h hne t f) hg
  simpa only [smul_smul] using hd

theorem gauge_derivative (ε h : ℝ) (hne : h ≠ 0) (f g : Hilbert)
    (hfg : (f,g) ∈ (chartOperator ε).graph) (t : ℝ) :
    HasDerivAt (fun z => gauge ε h z f) ((Complex.I*((-2/h:ℝ):ℂ)) • gauge ε h t g) t := by
  have h0 := gauge_derivative_zero ε h hne f g hfg
  have hs : HasDerivAt (fun z => gauge ε h (z-t) f) ((Complex.I*((-2/h:ℝ):ℂ)) • g) t := by
    have hh : HasDerivAt (fun z => gauge ε h z f) ((Complex.I*((-2/h:ℝ):ℂ)) • g) (t-t) := by
      simpa only [sub_self] using h0
    exact hh.comp_sub_const t t
  have hd := ((gauge ε h t : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hs
  change HasDerivAt (fun z => gauge ε h t (gauge ε h (z-t) f))
    (gauge ε h t ((Complex.I*((-2/h:ℝ):ℂ)) • g)) t at hd
  have he (z : ℝ) : t+(z-t)=z := by ring
  simpa only [← gauge_add ε h hne,he,map_smul] using hd

#print axioms chartOperator_selfAdjoint
#print axioms chartOperator_graph
#print axioms gauge_coe
#print axioms gauge_add
#print axioms gauge_inverse
#print axioms gauge_pairing
#print axioms gauge_derivative_zero
#print axioms gauge_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorGaugeDerivative

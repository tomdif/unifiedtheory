/- The actual averaged static form has the maximal square-root multiplier
as an extension, with exactly equal form energy. The coordinate symbol
retains all five transverse derivatives. This does not yet identify a
common static/growing operator core or the full form intersection. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticFormIdentity
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticMultiplierForm
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalComplementaryChargeSymbol
open KFCausalClockFloorAveragedComplementaryMoment
open KFCausalClockFloorStaticFormIdentity
open KFCausalUnitaryRealMultiplier (realPullback realPullback_domain)
open KFCausalRealMultiplierSelfAdjoint (realPullback_selfAdjoint realPullback_norm_square)
open KFCausalClockFloorAveragedEnergy
open KFCausalAveragedOutputRescaling (staticOutputLp)

def symbol (ε h : ℝ) (x : Joint 5 1) : ℝ :=
  (clock ε (x (.inr 0))+complementaryWeight ε h 0 x+complementaryWeight ε h 1 x)/2

def rootSymbol (ε h : ℝ) (x : Joint 5 1) : ℝ := Real.sqrt (symbol ε h x)

theorem symbol_positive (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 5 1) :
    0 < symbol ε h x := by
  exact div_pos (add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (clock_positive ε _ hε.le)
      (complementaryWeight_nonnegative ε hε h 0 x))
    (complementaryWeight_nonnegative ε hε h 1 x)) (by norm_num)

theorem symbol_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Continuous (symbol ε h) := by
  exact ((show Continuous (fun x : Joint 5 1 => clock ε (x (.inr 0))) by
    unfold clock; fun_prop).add (complementaryWeight_continuous ε hε h 0)).add
      (complementaryWeight_continuous ε hε h 1) |>.div_const 2

theorem rootSymbol_square (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 5 1) :
    rootSymbol ε h x ^ 2 = symbol ε h x := Real.sq_sqrt (symbol_positive ε hε h x).le

theorem symbol_coordinates (ε h : ℝ) (x : Joint 5 1) :
    symbol ε h x = (clock ε (x (.inr 0))+
      ((KFCausalNormalizedChargeFlow.momentumScale h)^2*
        (x (.inl 2)^2+x (.inl 3)^2+x (.inl 4)^2)+x (.inl 0)^2+x (.inl 1)^2)/
        clock ε (x (.inr 0)))/2 := by
  change (clock ε (x (.inr 0))+
    (((KFCausalNormalizedChargeFlow.momentumScale h*x (.inl 2))^2+
      (-x (.inl 0))^2+0^2)/clock ε (x (.inr 0)))+
    (((KFCausalNormalizedChargeFlow.momentumScale h*x (.inl 3))^2+
      (-x (.inl 1))^2+(KFCausalNormalizedChargeFlow.momentumScale h*x (.inl 4))^2)/
        clock ε (x (.inr 0))))/2 = _
  ring

def rootOperator (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback dualPhysical (rootSymbol ε h) ((symbol_continuous ε hε h).sqrt.measurable)

theorem rootOperator_selfAdjoint (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    IsSelfAdjoint (rootOperator ε hε h) :=
  realPullback_selfAdjoint dualPhysical (rootSymbol ε h) ((symbol_continuous ε hε h).sqrt.measurable)

private theorem weighted_density (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : Hilbert) (x : Joint 5 1) :
    ‖(rootSymbol ε h x:ℂ)*(dualPhysical f) x‖^2 =
      (clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2+
       complementaryWeight ε h 0 x*‖(dualPhysical f) x‖^2+
       complementaryWeight ε h 1 x*‖(dualPhysical f) x‖^2)/2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,rootSymbol_square ε hε h]
  unfold symbol
  ring

private theorem three_moment_memLp (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hc : Integrable (fun x => clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2))
    (h0 : Integrable (fun x => complementaryWeight ε h 0 x*‖(dualPhysical f) x‖^2))
    (h1 : Integrable (fun x => complementaryWeight ε h 1 x*‖(dualPhysical f) x‖^2)) :
    MemLp (fun x => (rootSymbol ε h x:ℂ)*(dualPhysical f) x) 2 := by
  have ha := (Complex.continuous_ofReal.comp (symbol_continuous ε hε h).sqrt).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (dualPhysical f))
  apply (memLp_two_iff_integrable_sq_norm ha).mpr
  exact (((hc.add h0).add h1).div_const 2).congr
    (Filter.Eventually.of_forall (fun x => (weighted_density ε hε h f x).symm))

private theorem three_moment_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : f ∈ (rootOperator ε hε h).domain)
    (hc : Integrable (fun x => clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2))
    (h0 : Integrable (fun x => complementaryWeight ε h 0 x*‖(dualPhysical f) x‖^2))
    (h1 : Integrable (fun x => complementaryWeight ε h 1 x*‖(dualPhysical f) x‖^2)) :
    ‖rootOperator ε hε h ⟨f,hf⟩‖^2 =
      (clockMoment ε f+complementaryMoment ε h 0 f+complementaryMoment ε h 1 f)/2 := by
  change ‖realPullback dualPhysical (rootSymbol ε h)
    ((symbol_continuous ε hε h).sqrt.measurable) ⟨f,hf⟩‖^2 = _
  rw [realPullback_norm_square]
  simp_rw [rootSymbol_square ε hε h]
  have he : (fun x => symbol ε h x*‖(dualPhysical f) x‖^2) =
      fun x => (clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2+
        complementaryWeight ε h 0 x*‖(dualPhysical f) x‖^2+
        complementaryWeight ε h 1 x*‖(dualPhysical f) x‖^2)/2 := by
    funext x; unfold symbol; ring
  rw [he,integral_div]
  have hsum := integral_add (hc.add h0) h1
  simp only [Pi.add_apply] at hsum
  rw [hsum,integral_add hc h0]
  rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε) (hh : h ≠ 0)
  (m g κ t : ℝ)
local notation "V" => AveragedSpace ε hε h hb hh m g κ t
local notation "J" => embedding ε hε h hb hh m g κ t
local notation "A" => energyOutput ε hε h hb hh m g κ t

theorem averaged_root_memLp (u : V) :
    MemLp (fun x => (rootSymbol ε h x:ℂ)*(dualPhysical (J u)) x) 2 :=
  three_moment_memLp ε hε h (J u)
    (averaged_clockMoment_integrable ε hε h hb hh m g κ t u)
    (averaged_complementaryDensity_integrable ε hε h hb hh m g κ t 0 u)
    (averaged_complementaryDensity_integrable ε hε h hb hh m g κ t 1 u)

theorem averaged_root_domain (u : V) : J u ∈ (rootOperator ε hε h).domain :=
  (realPullback_domain dualPhysical (rootSymbol ε h)
    ((symbol_continuous ε hε h).sqrt.measurable) (J u)).mpr
      (averaged_root_memLp ε hε h hb hh m g κ t u)

theorem averaged_root_norm (u : V) :
    ‖rootOperator ε hε h ⟨J u,averaged_root_domain ε hε h hb hh m g κ t u⟩‖^2 =
      ‖staticOutputLp (A u)‖^2 :=
  (three_moment_norm ε hε h (J u) (averaged_root_domain ε hε h hb hh m g κ t u)
    (averaged_clockMoment_integrable ε hε h hb hh m g κ t u)
    (averaged_complementaryDensity_integrable ε hε h hb hh m g κ t 0 u)
    (averaged_complementaryDensity_integrable ε hε h hb hh m g κ t 1 u)).trans
      (averaged_static_energy ε hε h hb hh m g κ t u).symm

#print axioms symbol_positive
#print axioms symbol_continuous
#print axioms rootSymbol_square
#print axioms symbol_coordinates
#print axioms rootOperator_selfAdjoint
#print axioms averaged_root_memLp
#print axioms averaged_root_domain
#print axioms averaged_root_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticMultiplierForm

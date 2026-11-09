/- Exact charge average of the squared, inverse-clock weighted
antisymmetric momentum multipliers. These are scalar identities for the
actual mixed-coordinate rotation; no state moment is assumed finite. -/
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalClassicalChargeMean

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (weightedAntiSymbol)
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates (antiSymbol)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def symmetricIndex (i : Fin 2) : Fin 4 := ![1,2] i
def momentum (h : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ := momentumScale h*x (.inl i)
def position (i : Fin 2) (x : Joint 2 4) : ℝ := x (.inr (symmetricIndex i))
def chargedWeight (ε h : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ :=
  (momentum h i x^2+position i x^2)/clock ε (x (.inr 0))

theorem chargedWeight_nonnegative (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (x : Joint 2 4) :
    0 ≤ chargedWeight ε h i x :=
  div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (clock_positive ε _ hε.le).le

theorem momentum_reverse (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (θ : ℝ) (x : Joint 2 4) :
    momentum h i (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-θ) x) =
      Real.cos θ*momentum h i x+Real.sin θ*position i x := by
  have hc := momentumScale_ne_zero h hh
  fin_cases i
  · have he := congrArg Prod.fst (flow_first_plane (momentumScale h) hc (-θ) x)
    simp only [Real.cos_neg,Real.sin_neg] at he
    change momentumScale h * (flowEquiv (momentumScale h) hc (-θ) x) (.inl 0) =
      Real.cos θ*(momentumScale h*x (.inl 0))+Real.sin θ*x (.inr 1)
    rw [he]
    field_simp
    ring
  · have he := congrArg Prod.fst (flow_second_plane (momentumScale h) hc (-θ) x)
    simp only [Real.cos_neg,Real.sin_neg] at he
    change momentumScale h * (flowEquiv (momentumScale h) hc (-θ) x) (.inl 1) =
      Real.cos θ*(momentumScale h*x (.inl 1))+Real.sin θ*x (.inr 2)
    rw [he]
    field_simp
    ring

theorem rotated_square (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (θ : ℝ) (x : Joint 2 4) :
    weightedAntiSymbol ε h i (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-θ) x)^2 =
      (Real.cos θ*momentum h i x+Real.sin θ*position i x)^2*(2/clock ε (x (.inr 0))) := by
  have ha (y : Joint 2 4) : antiSymbol h i y = (2*scale)*momentum h i y := by
    unfold antiSymbol momentum momentumScale
    ring
  rw [weightedAntiSymbol,ha,momentum_reverse h hh,flow_clock,div_pow,
    Real.sq_sqrt (clock_positive ε _ hε.le).le,mul_pow,mul_pow,scale_square]
  ring

theorem rotated_square_mean (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (x : Joint 2 4) :
    (∫ θ, weightedAntiSymbol ε h i
      (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-(2*Real.pi*θ)) x)^2 ∂angleMeasure) =
      chargedWeight ε h i x := by
  simp_rw [rotated_square ε hε h hh]
  rw [← mean_eq_angle (fun θ => (Real.cos θ*momentum h i x+Real.sin θ*position i x)^2*
    (2/clock ε (x (.inr 0)))),mean_mul_const]
  have he := affine_square_mean (momentum h i x) (position i x) 0
  simp only [add_zero,zero_pow (by decide : 2 ≠ 0)] at he
  rw [he]
  unfold chargedWeight
  ring

theorem rotated_square_integrable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (x : Joint 2 4) :
    Integrable (fun θ => weightedAntiSymbol ε h i
      (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-(2*Real.pi*θ)) x)^2) angleMeasure := by
  simp_rw [rotated_square ε hε h hh]
  have hc : Continuous (fun θ : ℝ =>
      (Real.cos (2*Real.pi*θ)*momentum h i x+Real.sin (2*Real.pi*θ)*position i x)^2*
        (2/clock ε (x (.inr 0)))) := by fun_prop
  exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem chargedWeight_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    Continuous (chargedWeight ε h i) := by
  unfold chargedWeight momentum position clock
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (clock_positive ε (x (.inr 0)) hε.le).ne'

theorem weightedAntiSymbol_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    Continuous (weightedAntiSymbol ε h i) := by
  unfold weightedAntiSymbol antiSymbol clock
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (Real.sqrt_pos.mpr (clock_positive ε (x (.inr 0)) hε.le)).ne'

#print axioms chargedWeight_nonnegative
#print axioms momentum_reverse
#print axioms rotated_square
#print axioms rotated_square_mean
#print axioms rotated_square_integrable
#print axioms chargedWeight_continuous
#print axioms weightedAntiSymbol_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol

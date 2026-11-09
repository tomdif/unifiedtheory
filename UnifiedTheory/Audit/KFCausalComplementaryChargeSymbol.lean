/- Exact averaged squares for the two remaining kinetic directions in the
complementary representation. The neutral momentum term is retained; its
cross terms vanish under the normalized charge average. -/
import UnifiedTheory.Audit.KFCausalChargeDualMomentum
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
import UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph
import UnifiedTheory.Audit.KFCausalClassicalChargeMean

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalPairedRotation (rotate)
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def antiDualIndex (i : Fin 2) : Fin 5 := ![0,1] i
def symmetricDualIndex (i : Fin 2) : Fin 5 := ![2,3] i
def complementaryPosition (i : Fin 2) (x : Joint 5 1) : ℝ := -x (.inl (antiDualIndex i))
def complementaryMomentum (h : ℝ) (i : Fin 2) (x : Joint 5 1) : ℝ := momentumScale h*x (.inl (symmetricDualIndex i))
def neutralMomentum (h : ℝ) (x : Joint 5 1) : ℝ := momentumScale h*x (.inl 4)
def neutralTerm (h : ℝ) (i : Fin 2) (x : Joint 5 1) : ℝ := ![0,neutralMomentum h x] i
def complementarySquare (h : ℝ) (i : Fin 2) (x : Joint 5 1) : ℝ :=
  complementaryMomentum h i x^2+complementaryPosition i x^2+neutralTerm h i x^2

def rotatedVector (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (i : Fin 2) : Joint 2 4 :=
  flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ (symmetricVector i)

theorem rotatedVector_clock (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (i : Fin 2) : rotatedVector h hh θ i (.inr 0) = 0 := by
  rw [rotatedVector,flow_clock]
  fin_cases i <;> rfl

theorem rotatedSymbol_formula (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (i : Fin 2) (x : Joint 5 1) :
    dualSymbol h (rotatedVector h hh θ i) x =
      2*scale*(Real.cos θ*complementaryMomentum h i x+Real.sin θ*complementaryPosition i x)+neutralTerm h i x := by
  have hc := momentumScale_ne_zero h hh
  fin_cases i <;>
    simp [dualSymbol,transverseBlock,repackIsometry,repackEquiv,repack,split_fst,PiLp.inner_apply,
      RCLike.inner_apply,Fin.sum_univ_succ,rotatedVector,flow_apply,dilate,rotate,symmetricVector,
      rightVector,symmetricBlock,complementaryMomentum,complementaryPosition,neutralTerm,
      neutralMomentum,antiDualIndex,symmetricDualIndex]
  all_goals
    change momentumScale h * _ = _
    field_simp
    ring

def complementaryWeight (ε h : ℝ) (i : Fin 2) (x : Joint 5 1) : ℝ :=
  complementarySquare h i x/clock ε (x (.inr 0))

def rotatedWeightedSymbol (ε h : ℝ) (hh : h ≠ 0) (θ : ℝ) (i : Fin 2) (x : Joint 5 1) : ℝ :=
  dualSymbol h (rotatedVector h hh θ i) x/Real.sqrt (clock ε (x (.inr 0)))

theorem complementarySquare_nonnegative (h : ℝ) (i : Fin 2) (x : Joint 5 1) : 0 ≤ complementarySquare h i x := by
  unfold complementarySquare
  positivity

theorem complementaryWeight_nonnegative (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (x : Joint 5 1) :
    0 ≤ complementaryWeight ε h i x :=
  div_nonneg (complementarySquare_nonnegative h i x) (clock_positive ε _ hε.le).le

theorem rotatedWeighted_square (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (i : Fin 2) (x : Joint 5 1) :
    rotatedWeightedSymbol ε h hh θ i x^2 =
      (Real.cos θ*(2*scale*complementaryMomentum h i x)+
        Real.sin θ*(2*scale*complementaryPosition i x)+neutralTerm h i x)^2/clock ε (x (.inr 0)) := by
  rw [rotatedWeightedSymbol,div_pow,Real.sq_sqrt (clock_positive ε _ hε.le).le,rotatedSymbol_formula]
  ring

theorem rotatedWeighted_mean (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (x : Joint 5 1) :
    (∫ θ, rotatedWeightedSymbol ε h hh (2*Real.pi*θ) i x^2 ∂angleMeasure) = complementaryWeight ε h i x := by
  simp_rw [rotatedWeighted_square ε hε h hh]
  rw [← mean_eq_angle (fun θ =>
    (Real.cos θ*(2*scale*complementaryMomentum h i x)+Real.sin θ*(2*scale*complementaryPosition i x)+
      neutralTerm h i x)^2/clock ε (x (.inr 0)))]
  simp only [div_eq_mul_inv,mean_mul_const,affine_square_mean]
  unfold complementaryWeight complementarySquare
  ring_nf
  rw [scale_square]
  ring

theorem rotatedWeighted_integrable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (x : Joint 5 1) :
    Integrable (fun θ => rotatedWeightedSymbol ε h hh (2*Real.pi*θ) i x^2) angleMeasure := by
  simp_rw [rotatedWeighted_square ε hε h hh]
  have hc : Continuous (fun θ : ℝ =>
    (Real.cos (2*Real.pi*θ)*(2*scale*complementaryMomentum h i x)+
      Real.sin (2*Real.pi*θ)*(2*scale*complementaryPosition i x)+neutralTerm h i x)^2/clock ε (x (.inr 0))) := by fun_prop
  exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem complementaryWeight_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    Continuous (complementaryWeight ε h i) := by
  unfold complementaryWeight complementarySquare complementaryMomentum complementaryPosition neutralTerm neutralMomentum clock
  fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact (clock_positive ε (x (.inr 0)) hε.le).ne'

#print axioms rotatedVector_clock
#print axioms rotatedSymbol_formula
#print axioms complementarySquare_nonnegative
#print axioms complementaryWeight_nonnegative
#print axioms rotatedWeighted_square
#print axioms rotatedWeighted_mean
#print axioms rotatedWeighted_integrable
#print axioms complementaryWeight_continuous

end
end UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol

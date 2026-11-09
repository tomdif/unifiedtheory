/- An explicit spectator density prescription: integrate neutral frequency,
then restrict clock integration to a finite interval. This is a density,
not a trace of the heat operator on the full physical Hilbert space. -/
import UnifiedTheory.Audit.KFCausalFreeClockThermalObstruction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFreeThermalDensity
noncomputable section
open MeasureTheory
open KFCausalFreeChargedPartition
open KFCausalClockFloorFlow (clock)

def gaussianRate (ε h s β : ℝ) : ℝ := β*(2*Real.pi*h)^2/(2*clock ε s)

theorem gaussianRate_positive (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (s β : ℝ) (hβ : 0 < β) : 0 < gaussianRate ε h s β := by
  unfold gaussianRate
  have hc := KFCausalClockFloorCanonicalDefect.clock_positive ε s hε.le
  positivity

theorem partition_gaussian (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t s ξ β : ℝ) (hβ : 0 < β) :
    partition ε h t s ξ β = partition ε h t s 0 β*Real.exp (-gaussianRate ε h s β*ξ^2) := by
  rw [partition_eq ε hε h hh t s ξ β hβ,partition_eq ε hε h hh t s 0 β hβ]
  have he : -β*ground ε h t s ξ =
      -β*ground ε h t s 0-gaussianRate ε h s β*ξ^2 := by
    unfold ground gaussianRate
    ring
  rw [he,sub_eq_add_neg,Real.exp_add]
  rw [neg_mul]
  ring

theorem neutral_integrable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t s β : ℝ) (hβ : 0 < β) :
    Integrable (fun ξ => partition ε h t s ξ β) volume := by
  have he := (integrable_exp_neg_mul_sq (gaussianRate_positive ε hε h hh s β hβ)).const_mul
    (partition ε h t s 0 β)
  exact he.congr (Filter.Eventually.of_forall fun ξ => (partition_gaussian ε hε h hh t s ξ β hβ).symm)

def density (ε h t s β : ℝ) : ℝ := ∫ ξ : ℝ, partition ε h t s ξ β

theorem density_eq (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t s β : ℝ) (hβ : 0 < β) :
    density ε h t s β = partition ε h t s 0 β*Real.sqrt (Real.pi/gaussianRate ε h s β) := by
  unfold density
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun ξ => partition_gaussian ε hε h hh t s ξ β hβ))]
  rw [integral_const_mul,integral_gaussian]

theorem partition_clock_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t ξ β : ℝ) (hβ : 0 < β) : Continuous (fun s => partition ε h t s ξ β) := by
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hn (s : ℝ) : clock ε s ≠ 0 :=
    (KFCausalClockFloorCanonicalDefect.clock_positive ε s hε.le).ne'
  have hg : Continuous (gap ε h t) := continuous_const.div hc hn
  have hgr : Continuous (fun s => ground ε h t s ξ) := by
    unfold ground
    exact (hc.div_const 2).add (continuous_const.div (continuous_const.mul hc)
      (fun s => mul_ne_zero (by norm_num) (hn s))) |>.add hg
  have he : Continuous (fun s => Real.exp (-β*gap ε h t s)) :=
    Real.continuous_exp.comp (continuous_const.mul hg)
  have hd (s : ℝ) : (1-Real.exp (-β*gap ε h t s))^3 ≠ 0 := by
    apply pow_ne_zero
    have hl : Real.exp (-β*gap ε h t s) < 1 := by
      rw [Real.exp_lt_one_iff]
      simpa only [neg_mul] using neg_neg_of_pos (mul_pos hβ (gap_positive ε hε h hh t s))
    linarith
  have hp : Continuous (fun s => Real.exp (-β*ground ε h t s ξ)*
      ((1+Real.exp (-β*gap ε h t s))/(1-Real.exp (-β*gap ε h t s))^3)) :=
    (Real.continuous_exp.comp (continuous_const.mul hgr)).mul
    ((continuous_const.add he).div ((continuous_const.sub he).pow 3) hd)
  exact hp.congr (fun s => (partition_eq ε hε h hh t s ξ β hβ).symm)

theorem density_clock_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t β : ℝ) (hβ : 0 < β) : Continuous (fun s => density ε h t s β) := by
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hn (s : ℝ) : 2*clock ε s ≠ 0 := by
    have hp := KFCausalClockFloorCanonicalDefect.clock_positive ε s hε.le
    positivity
  have hr : Continuous (fun s => gaussianRate ε h s β) :=
    continuous_const.div (continuous_const.mul hc) hn
  have he : Continuous (fun s => partition ε h t s 0 β*
      Real.sqrt (Real.pi/gaussianRate ε h s β)) :=
    (partition_clock_continuous ε hε h hh t 0 β hβ).mul
    (continuous_const.div hr (fun s => (gaussianRate_positive ε hε h hh s β hβ).ne')).sqrt
  exact he.congr (fun s => (density_eq ε hε h hh t s β hβ).symm)

theorem density_integrableOn_clock_window (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t β : ℝ) (hβ : 0 < β) (a b : ℝ) :
    IntegrableOn (fun s => density ε h t s β) (Set.Icc a b) volume :=
  (density_clock_continuous ε hε h hh t β hβ).continuousOn.integrableOn_Icc

#print axioms partition_gaussian
#print axioms neutral_integrable
#print axioms density_eq
#print axioms density_integrableOn_clock_window
end
end UnifiedTheory.Audit.KFCausalFreeThermalDensity

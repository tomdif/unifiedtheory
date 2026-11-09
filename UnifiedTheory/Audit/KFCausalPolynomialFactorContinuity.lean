/- The source-circle coefficient construction gives continuous actual
energy-factor outputs for every finite polynomial along bounded source
curves. Joint continuity justifies integration over the compact circle. -/
import UnifiedTheory.Audit.KFCausalParameterizedFactorContinuity
import UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialFactorContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates (sourceBound circleSource circleSource_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (powerOutput output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

theorem sourceBound_le (b : Fin 5 → ℂ) : sourceBound b ≤ 2*sourceSize b+10 := by
  calc
    _ ≤ ∑ j : Fin 5, (2*‖b j‖^2+2) := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (‖b j‖-1)]
    _ = _ := by
      simp only [sourceSize,Finset.sum_add_distrib,← Finset.mul_sum]
      norm_num

def jointSource (b : ℝ → Fin 5 → ℂ) (i : Fin 5) (z : ℝ × ℝ) : Fin 5 → ℂ :=
  circleSource (b z.1) i z.2

theorem jointSource_continuous (b : ℝ → Fin 5 → ℂ) (hb : Continuous b) (i : Fin 5) :
    Continuous (jointSource b i) := by
  apply continuous_pi
  intro j
  by_cases hj : j=i
  · simpa only [jointSource,circleSource,if_pos hj] using
      ((continuous_apply j).comp (hb.comp continuous_fst)).add
        (circle_continuous.comp continuous_snd)
  · simpa only [jointSource,circleSource,if_neg hj,add_zero] using
      (continuous_apply j).comp (hb.comp continuous_fst)

theorem jointSource_bound (B : ℝ) (b : ℝ → Fin 5 → ℂ)
    (hb : ∀ θ, sourceSize (b θ) ≤ B) (i : Fin 5) (z : ℝ × ℝ) :
    sourceSize (jointSource b i z) ≤ 2*B+10 := by
  have h := (circleSource_bound (b z.1) i z.2).trans (sourceBound_le (b z.1))
  exact h.trans (by linarith [hb z.1])

theorem angle_mean_continuous (f : ℝ → ℝ → Hilbert) (hf : Continuous f.uncurry) :
    Continuous (fun θ => ∫ φ, f θ φ ∂angleMeasure) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))
  simpa only [integral_Icc_eq_integral_Ioc,angleMeasure] using hc

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (F B : ℝ)
  (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
  (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
  (hp : ∀ θ, |p θ| ≤ F) (hB : ∀ θ, sourceSize (b θ) ≤ B)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
include hCc hpc hbc hp hB

theorem powerOutput_continuous (i : Fin 5) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (fun θ => powerOutput ε a h hε ha hh (C θ) (p θ) (b θ) i hb n v l j) := by
  have hj := KFCausalParameterizedFactorContinuity.factor_continuous ε a h hε ha hh hb F (2*B+10)
    (fun z : ℝ × ℝ => weight n z.2) (fun z => p z.1) (jointSource b i)
    ((weight_continuous n).comp continuous_snd) (hpc.comp continuous_fst)
    (jointSource_continuous b hbc i)
    (fun z => (weight_norm n z.2).le) (fun z => hp z.1) (jointSource_bound B b hB i) v l j
  change Continuous (fun θ => (C θ*normalization n) •
    ∫ φ, KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
      (weight n φ) (p θ) (circleSource (b θ) i φ) h hb v l j ∂angleMeasure)
  exact (hCc.mul continuous_const).smul (angle_mean_continuous _ hj)

theorem output_continuous (i : Fin 5) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (fun θ => output ε a h hε ha hh (C θ) (p θ) (b θ) i hb P v l j) := by
  apply continuous_finset_sum
  intro n _
  exact continuous_const.smul
    (powerOutput_continuous ε a h hε ha hh hb F B C p b hCc hpc hbc hp hB i n v l j)

#print axioms sourceBound_le
#print axioms jointSource_continuous
#print axioms jointSource_bound
#print axioms angle_mean_continuous
#print axioms powerOutput_continuous
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalPolynomialFactorContinuity

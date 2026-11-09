/- Continuous four-dimensional test-function map and positive
two-point form from the mass-shell law. Fourier normalization is Mathlib's
2*pi convention. This proves continuity and positivity, not locality. -/
import UnifiedTheory.Audit.KFCausalMassShellSchwartzRestriction
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalMassShellTwoPoint
noncomputable section
open MeasureTheory
open scoped BigOperators
open KFCausalRelativisticMassShell KFCausalMassShellSchwartzRestriction

variable (ρ : Measure ℝ) [IsFiniteMeasure ρ] (δ : ℝ) (hδ : 0 < δ)

include hδ in
theorem dominating_memLp : MemLp (fun x : ShellPoint => (1+‖x.2‖)^(-2 : ℝ))
    2 (shellMeasure ρ δ) :=
  ((spatialDecay_memLp.comp_snd ρ).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (shellMeasure_le ρ δ hδ)

def dominatingVector : Lp ℝ 2 (shellMeasure ρ δ) :=
  (dominating_memLp ρ δ hδ).toLp (fun x : ShellPoint => (1+‖x.2‖)^(-2 : ℝ))

theorem restriction_norm_bound (F : Test) :
    ‖restriction ρ δ hδ F‖ ≤ decayConstant F * ‖dominatingVector ρ δ hδ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [restriction_coe ρ δ hδ F, (dominating_memLp ρ δ hδ).coeFn_toLp] with x hf hg
  change ‖restriction ρ δ hδ F x‖ ≤ decayConstant F * ‖dominatingVector ρ δ hδ x‖
  rw [hf]
  change _ ≤ decayConstant F * ‖(dominating_memLp ρ δ hδ).toLp _ x‖
  rw [hg, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact waveFunction_bound δ F x

def restrictionCLM : Test →L[ℂ] OneParticle ρ δ :=
  SchwartzMap.mkCLMtoNormedSpace (restriction ρ δ hδ)
    (map_add _) (map_smul _) (by
      refine ⟨Finset.Iic (2,0), 4*‖dominatingVector ρ δ hδ‖, by positivity, ?_⟩
      intro F
      have hb := restriction_norm_bound ρ δ hδ F
      simpa only [decayConstant, schwartzSeminormFamily,
        mul_assoc, mul_comm, mul_left_comm] using hb)

abbrev EuclideanFour := WithLp 2 (ℝ × Momentum)

def euclideanCoordinates : EuclideanFour ≃L[ℝ] (ℝ × Momentum) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℝ Momentum

def fourierOnTest : Test →L[ℂ] Test :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euclideanCoordinates.symm).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euclideanCoordinates))

def testVector : Test →L[ℂ] OneParticle ρ δ := (restrictionCLM ρ δ hδ).comp fourierOnTest

def twoPoint (F G : Test) : ℂ := inner ℂ (testVector ρ δ hδ F) (testVector ρ δ hδ G)

theorem twoPoint_continuous : Continuous (fun p : Test × Test => twoPoint ρ δ hδ p.1 p.2) :=
  ((testVector ρ δ hδ).continuous.comp continuous_fst).inner
    ((testVector ρ δ hδ).continuous.comp continuous_snd)

theorem twoPoint_positive {J : Type*} (S : Finset J) (F : J → Test) (c : J → ℂ) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, starRingEnd ℂ (c i) * c j *
      twoPoint ρ δ hδ (F i) (F j)).re := by
  have he : (∑ i ∈ S, ∑ j ∈ S, starRingEnd ℂ (c i) * c j *
      twoPoint ρ δ hδ (F i) (F j)) =
      inner ℂ (∑ i ∈ S, c i • testVector ρ δ hδ (F i))
        (∑ i ∈ S, c i • testVector ρ δ hδ (F i)) := by
    simp only [sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right, twoPoint, mul_assoc, mul_left_comm]
  rw [he]
  exact inner_self_nonneg (𝕜 := ℂ)

end
end UnifiedTheory.Audit.KFCausalMassShellTwoPoint

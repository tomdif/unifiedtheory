/- Equality on derivative tests determines the finite signed net force,
expressed without assuming uniqueness of its positive decomposition. -/
import UnifiedTheory.Audit.KFCausalForceFourierSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNetForceUniqueness
noncomputable section
open MeasureTheory Set SchwartzMap BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalForceFourierSeparation

def Equivalent (F G : FluxPair) : Prop :=
  F.positive+G.negative = G.positive+F.negative

theorem charFun_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : ℝ) :
    charFun (μ+ν) v = charFun μ v+charFun ν v := by
  simp only [charFun_eq_integral_innerProbChar]
  exact integral_add_measure ((innerProbChar v).integrable μ) ((innerProbChar v).integrable ν)

theorem equivalent_of_fourier_eq (F G : FluxPair) (h : F.fourier = G.fourier) :
    Equivalent F G := by
  apply Measure.ext_of_charFun
  funext v
  rw [charFun_add,charFun_add]
  have he := congrFun h v
  change (charFun F.positive v-charFun F.negative v)/2 =
    (charFun G.positive v-charFun G.negative v)/2 at he
  linear_combination 2*he

theorem equivalent_of_derivative_tests (F G : FluxPair)
    (h : ∀ f : 𝓢(ℝ,ℂ), F.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction =
      G.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) : Equivalent F G :=
  equivalent_of_fourier_eq F G (fourier_eq_of_derivative_tests F G h)

theorem evaluate_eq (F G : FluxPair) (h : Equivalent F G) (q : ℝ →ᵇ ℂ) :
    F.evaluate q = G.evaluate q := by
  have he := congrArg (fun μ : Measure ℝ => ∫ x, q x ∂μ) h
  dsimp only at he
  rw [integral_add_measure (q.integrable F.positive) (q.integrable G.negative),
    integral_add_measure (q.integrable G.positive) (q.integrable F.negative)] at he
  change ((∫ x, q x ∂F.positive)-(∫ x, q x ∂F.negative))/2 =
    ((∫ x, q x ∂G.positive)-(∫ x, q x ∂G.negative))/2
  linear_combination he/2

theorem equivalent_of_same_balance (F G : FluxPair) (μ ν : Measure ℝ)
    (hF : ∀ f : 𝓢(ℝ,ℂ), (∫ p, f p ∂ν)-(∫ p, f p ∂μ) =
      F.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction)
    (hG : ∀ f : 𝓢(ℝ,ℂ), (∫ p, f p ∂ν)-(∫ p, f p ∂μ) =
      G.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) : Equivalent F G :=
  equivalent_of_derivative_tests F G (fun f => (hF f).symm.trans (hG f))

#print axioms charFun_add
#print axioms equivalent_of_fourier_eq
#print axioms equivalent_of_derivative_tests
#print axioms evaluate_eq
#print axioms equivalent_of_same_balance
end
end UnifiedTheory.Audit.KFCausalNetForceUniqueness

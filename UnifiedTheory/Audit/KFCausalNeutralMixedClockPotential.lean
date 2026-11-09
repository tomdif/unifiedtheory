/- Exact potential energy and signed response of finite neutral states
with mixed clock widths and frequencies. Every cross term is retained
in the absolutely integrable kernels. Couplings are all one. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockPotential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse (physicalWeights)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalNeutralFiniteGram (energyKernel)
open UnifiedTheory.Audit.KFCausalNeutralFiniteResponse (realKernel reducedResponse)
open UnifiedTheory.Audit.KFCausalNeutralFinitePotential (energyKernel_weights reducedResponse_weights)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockPairing
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState

variable (ε h : ℝ) (N : ℕ) (a p : Fin N → ℝ) (b C : Fin N → ℂ)
  (P : Fin N → Polynomial ℂ)
local notation "w" => physicalWeights 1 1 1

def wholeEnergy (s : ℝ) : ℂ :=
  ∑ n : Fin 3, (w n:ℂ)*mixedKernel ε h N a p b C P n s
def wholeResponse (s : ℝ) : ℂ :=
  ∑ n : Fin 3, (w n:ℂ)*mixedResponse ε h N a p b C P n s

theorem wholeEnergy_frozen (s : ℝ) :
    wholeEnergy ε h N a p b C P s =
      energyKernel ε (-h/2) (groundWidth h) (neutralWidth h)
        N b (clockCoefficients ε h N a p C s) P s := by
  simp only [wholeEnergy,mixedKernel_frozen,energyKernel_weights]

theorem wholeResponse_frozen (s : ℝ) :
    wholeResponse ε h N a p b C P s =
      reducedResponse ε (-h/2) (groundWidth h) (neutralWidth h)
        N b (clockCoefficients ε h N a p C s) P s := by
  simp only [wholeResponse,mixedResponse_frozen,reducedResponse_weights]

variable (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "u" n => output ε h hε hh N a p ha b C P hb (index n)
local notation "v" n => momentumOutput ε h hε hh N a p ha b C P hb (index n)

def potentialEnergy : ℝ := ∑ n : Fin 3, w n*‖u n‖^2
def potentialResponse : ℝ := ∑ n : Fin 3, w n*((-2/h)*(inner ℂ (u n) (v n)).im)

include hε hh ha hb in
theorem wholeEnergy_integrable : Integrable (wholeEnergy ε h N a p b C P) volume :=
  integrable_finset_sum Finset.univ fun n _ =>
    (mixedKernel_integrable ε h N a p b C P hε hh ha hb n).const_mul (w n:ℂ)

include hε hh ha hb in
theorem wholeResponse_integrable : Integrable (wholeResponse ε h N a p b C P) volume :=
  integrable_finset_sum Finset.univ fun n _ =>
    (mixedResponse_integrable ε h N a p b C P hε hh ha hb n).const_mul (w n:ℂ)

theorem complexEnergy_integral :
    (∫ s, wholeEnergy ε h N a p b C P s) =
      (potentialEnergy ε h N a p b C P hε hh ha hb:ℂ) := by
  unfold wholeEnergy
  rw [integral_finset_sum Finset.univ (fun n _ =>
    (mixedKernel_integrable ε h N a p b C P hε hh ha hb n).const_mul (w n:ℂ))]
  simp_rw [integral_const_mul,mixedKernel_pairing ε h N a p b C P hε hh ha hb]
  simp only [potentialEnergy,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]

theorem complexResponse_integral :
    (∫ s, wholeResponse ε h N a p b C P s) =
      (potentialResponse ε h N a p b C P hε hh ha hb:ℂ) := by
  unfold wholeResponse
  rw [integral_finset_sum Finset.univ (fun n _ =>
    (mixedResponse_integrable ε h N a p b C P hε hh ha hb n).const_mul (w n:ℂ))]
  simp_rw [integral_const_mul,mixedResponse_pairing ε h N a p b C P hε hh ha hb]
  simp only [potentialResponse,Complex.ofReal_sum,Complex.ofReal_mul]

include hε hh ha hb in
theorem realEnergy_integrable :
    Integrable (fun s => (wholeEnergy ε h N a p b C P s).re) volume :=
  (wholeEnergy_integrable ε h N a p b C P hε hh ha hb).re

include hε hh ha hb in
theorem realResponse_integrable :
    Integrable (fun s => (wholeResponse ε h N a p b C P s).re) volume :=
  (wholeResponse_integrable ε h N a p b C P hε hh ha hb).re

theorem realEnergy_integral :
    (∫ s, (wholeEnergy ε h N a p b C P s).re) =
      potentialEnergy ε h N a p b C P hε hh ha hb := by
  have he : (∫ s, (wholeEnergy ε h N a p b C P s).re) =
      (∫ s, wholeEnergy ε h N a p b C P s).re :=
    integral_re (wholeEnergy_integrable ε h N a p b C P hε hh ha hb)
  rw [complexEnergy_integral ε h N a p b C P hε hh ha hb,Complex.ofReal_re] at he
  exact he

theorem realResponse_integral :
    (∫ s, (wholeResponse ε h N a p b C P s).re) =
      potentialResponse ε h N a p b C P hε hh ha hb := by
  have he : (∫ s, (wholeResponse ε h N a p b C P s).re) =
      (∫ s, wholeResponse ε h N a p b C P s).re :=
    integral_re (wholeResponse_integrable ε h N a p b C P hε hh ha hb)
  rw [complexResponse_integral ε h N a p b C P hε hh ha hb,Complex.ofReal_re] at he
  exact he

#print axioms wholeEnergy_frozen
#print axioms wholeResponse_frozen
#print axioms wholeEnergy_integrable
#print axioms wholeResponse_integrable
#print axioms complexEnergy_integral
#print axioms complexResponse_integral
#print axioms realEnergy_integrable
#print axioms realResponse_integrable
#print axioms realEnergy_integral
#print axioms realResponse_integral
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockPotential

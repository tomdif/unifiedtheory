/- The three physical ordered-potential factors of a finite neutral
state equal the integrals of its weighted energy and response kernels.
The vacuum, quadratic and quartic couplings are all one. -/
import UnifiedTheory.Audit.KFCausalNeutralFinitePairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralFinitePotential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (pair)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse (physicalWeights)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalNeutralCrossDensity (reducedKernel)
open UnifiedTheory.Audit.KFCausalNeutralFiniteGram
open UnifiedTheory.Audit.KFCausalNeutralFiniteResponse (realKernel reducedResponse)
open UnifiedTheory.Audit.KFCausalNeutralCrossPairing
open UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState
open UnifiedTheory.Audit.KFCausalNeutralFinitePairing

theorem energyKernel_weights (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (s : ℝ) :
    energyKernel ε y α β N b C P s =
      ∑ n : Fin 3, (physicalWeights 1 1 1 n:ℂ)*finiteKernel ε y α β N b C P n s := by
  simp [energyKernel,physicalWeights,Fin.sum_univ_succ]
  ring

theorem finiteResponse_formula (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (n : ℕ) (s : ℝ) :
    finiteResponse ε y α β N b C P n s =
      (KFCausalClockResponseTransport.coefficient ε y s:ℂ)*finiteKernel ε y α β N b C P n s-
        finiteDerivative ε y α β N b C P n s/(KFCausalClockResponseTransport.clock ε s:ℂ) := by
  simp only [finiteResponse,reducedKernel,finiteKernel,finiteDerivative,
    Finset.mul_sum,Finset.sum_div,Finset.sum_sub_distrib]

theorem reducedResponse_weights (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (s : ℝ) :
    reducedResponse ε y α β N b C P s =
      ∑ n : Fin 3, (physicalWeights 1 1 1 n:ℂ)*finiteResponse ε y α β N b C P n s := by
  simp only [finiteResponse_formula]
  simp [reducedResponse,energyKernel,energyDerivative,physicalWeights,Fin.sum_univ_succ]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "u" n => output ε a h hε ha hh N b C P hb (index n)
local notation "v" n => momentumOutput ε a h hε ha hh N b C P hb (index n)
local notation "w" => physicalWeights 1 1 1
local notation "T" => realKernel ε (-h/2) α β N b C P
local notation "R" => reducedResponse ε (-h/2) α β N b C P

def potentialEnergy : ℝ := ∑ n : Fin 3, w n*‖u n‖^2
def potentialResponse : ℝ := ∑ n : Fin 3, w n*((-2/h)*(inner ℂ (u n) (v n)).im)

include hε ha hh hb in
theorem wholeEnergy_integrable :
    Integrable (fun s => pair ε a a 0 0 (-h/2) s*energyKernel ε (-h/2) α β N b C P s) volume := by
  have hi := integrable_finset_sum Finset.univ fun n _ =>
    (finiteClockEnergy_integrable ε a h hε ha hh hb N b C P n).const_mul (w n:ℂ)
  convert hi using 1
  funext s
  rw [energyKernel_weights]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

include hε ha hh hb in
theorem wholeResponse_integrable :
    Integrable (fun s => pair ε a a 0 0 (-h/2) s*R s) volume := by
  have hi := integrable_finset_sum Finset.univ fun n _ =>
    (finiteClockResponse_integrable ε a h hε ha hh hb N b C P n).const_mul (w n:ℂ)
  convert hi using 1
  funext s
  rw [reducedResponse_weights]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem complexEnergy_integral :
    (∫ s, pair ε a a 0 0 (-h/2) s*energyKernel ε (-h/2) α β N b C P s) =
      (potentialEnergy ε a h hε ha hh hb N b C P:ℂ) := by
  have he (s : ℝ) : pair ε a a 0 0 (-h/2) s*energyKernel ε (-h/2) α β N b C P s =
      ∑ n : Fin 3, (w n:ℂ)*(pair ε a a 0 0 (-h/2) s*finiteKernel ε (-h/2) α β N b C P n s) := by
    rw [energyKernel_weights]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [he]
  rw [integral_finset_sum Finset.univ (fun n _ =>
    (finiteClockEnergy_integrable ε a h hε ha hh hb N b C P n).const_mul (w n:ℂ))]
  simp_rw [integral_const_mul,finiteClockEnergy_pairing ε a h hε ha hh hb]
  simp only [potentialEnergy,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]

theorem complexResponse_integral :
    (∫ s, pair ε a a 0 0 (-h/2) s*R s) =
      (potentialResponse ε a h hε ha hh hb N b C P:ℂ) := by
  have he (s : ℝ) : pair ε a a 0 0 (-h/2) s*R s =
      ∑ n : Fin 3, (w n:ℂ)*(pair ε a a 0 0 (-h/2) s*finiteResponse ε (-h/2) α β N b C P n s) := by
    rw [reducedResponse_weights]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [he]
  rw [integral_finset_sum Finset.univ (fun n _ =>
    (finiteClockResponse_integrable ε a h hε ha hh hb N b C P n).const_mul (w n:ℂ))]
  simp_rw [integral_const_mul,finiteClockResponse_pairing ε a h hε ha hh hb]
  simp only [potentialResponse,Complex.ofReal_sum,Complex.ofReal_mul]

include hε ha hh hb in
theorem realEnergy_integrable : Integrable (fun s => clockWeight ε a h s*T s) volume := by
  have hi : Integrable (fun s =>
      (pair ε a a 0 0 (-h/2) s*energyKernel ε (-h/2) α β N b C P s).re) volume :=
    (wholeEnergy_integrable ε a h hε ha hh hb N b C P).re
  simpa only [pair_eq_clockWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,realKernel] using hi

include hε ha hh hb in
theorem realResponse_integrable : Integrable (fun s => clockWeight ε a h s*(R s).re) volume := by
  have hi : Integrable (fun s => (pair ε a a 0 0 (-h/2) s*R s).re) volume :=
    (wholeResponse_integrable ε a h hε ha hh hb N b C P).re
  simpa only [pair_eq_clockWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using hi

theorem realEnergy_integral :
    (∫ s, clockWeight ε a h s*T s) = potentialEnergy ε a h hε ha hh hb N b C P := by
  have he : (∫ s, (pair ε a a 0 0 (-h/2) s*energyKernel ε (-h/2) α β N b C P s).re) =
      (∫ s, pair ε a a 0 0 (-h/2) s*energyKernel ε (-h/2) α β N b C P s).re :=
    integral_re (wholeEnergy_integrable ε a h hε ha hh hb N b C P)
  rw [complexEnergy_integral ε a h hε ha hh hb] at he
  simpa only [pair_eq_clockWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,realKernel] using he

theorem realResponse_integral :
    (∫ s, clockWeight ε a h s*(R s).re) = potentialResponse ε a h hε ha hh hb N b C P := by
  have he : (∫ s, (pair ε a a 0 0 (-h/2) s*R s).re) =
      (∫ s, pair ε a a 0 0 (-h/2) s*R s).re :=
    integral_re (wholeResponse_integrable ε a h hε ha hh hb N b C P)
  rw [complexResponse_integral ε a h hε ha hh hb] at he
  simpa only [pair_eq_clockWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using he

#print axioms energyKernel_weights
#print axioms finiteResponse_formula
#print axioms reducedResponse_weights
#print axioms wholeEnergy_integrable
#print axioms wholeResponse_integrable
#print axioms complexEnergy_integral
#print axioms complexResponse_integral
#print axioms realEnergy_integrable
#print axioms realResponse_integrable
#print axioms realEnergy_integral
#print axioms realResponse_integral
end
end UnifiedTheory.Audit.KFCausalNeutralFinitePotential

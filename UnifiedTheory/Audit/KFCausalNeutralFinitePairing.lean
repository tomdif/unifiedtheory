/- Integrate finite source Gram kernels and signed cross responses,
identifying them with the actual output of a single superposed state. -/
import UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralFinitePairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (pair)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalNeutralCrossKernel
open UnifiedTheory.Audit.KFCausalNeutralCrossDensity (reducedKernel)
open UnifiedTheory.Audit.KFCausalNeutralFiniteGram
open UnifiedTheory.Audit.KFCausalNeutralCrossPairing
open UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState

def finiteResponse (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, reducedKernel ε y α β (b i) (b j) (C i) (C j) (P i) (P j) n s

theorem sum_inner_pairs (N : ℕ) (f g : Fin N → Hilbert) :
    (∑ i, ∑ j, inner ℂ (f i) (g j)) = inner ℂ (∑ i, f i) (∑ j, g j) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]

theorem diagonal_scalar (h : ℝ) (z : ℂ) :
    (Complex.I/(h:ℂ))*(z-star z) = (((-2/h)*z.im:ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,Complex.mul_im]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (N : ℕ) (b C : Fin N → ℂ)
  (P : Fin N → Polynomial ℂ) (n : Fin 3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "K" => finiteKernel ε (-h/2) α β N b C P n
local notation "R" => finiteResponse ε (-h/2) α β N b C P n
local notation "u" => output ε a h hε ha hh N b C P hb (index n)
local notation "v" => momentumOutput ε a h hε ha hh N b C P hb (index n)

include hε ha hh hb in
theorem finiteClockEnergy_integrable :
    Integrable (fun s => pair ε a a 0 0 (-h/2) s*K s) volume := by
  have hi := integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      clockEnergy_integrable ε a h hε ha hh hb (b i) (b j) (C i) (C j) (P i) (P j) n
  simpa only [finiteKernel,Finset.mul_sum] using hi

include hε ha hh hb in
theorem finiteClockResponse_integrable :
    Integrable (fun s => pair ε a a 0 0 (-h/2) s*R s) volume := by
  have hi := integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      clockResponse_integrable ε a h hε ha hh hb (b i) (b j) (C i) (C j) (P i) (P j) n
  simpa only [finiteResponse,Finset.mul_sum] using hi

theorem finiteClockEnergy_pairing :
    (∫ s, pair ε a a 0 0 (-h/2) s*K s) = (‖u‖^2:ℂ) := by
  have hi (i j : Fin N) := clockEnergy_integrable ε a h hε ha hh hb
    (b i) (b j) (C i) (C j) (P i) (P j) n
  simp only [finiteKernel,Finset.mul_sum]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j)]
  simp_rw [clockEnergy_pairing ε a h hε ha hh hb]
  rw [sum_inner_pairs,inner_self_eq_norm_sq_to_K]
  rfl

theorem finiteClockResponse_pairing :
    (∫ s, pair ε a a 0 0 (-h/2) s*R s) = (((-2/h)*(inner ℂ u v).im:ℝ):ℂ) := by
  have hi (i j : Fin N) := clockResponse_integrable ε a h hε ha hh hb
    (b i) (b j) (C i) (C j) (P i) (P j) n
  simp only [finiteResponse,Finset.mul_sum]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j)]
  simp_rw [clockResponse_pairing ε a h hε ha hh hb]
  simp only [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [sum_inner_pairs,sum_inner_pairs]
  change (Complex.I/(h:ℂ))*(inner ℂ u v-inner ℂ v u) = _
  rw [← inner_conj_symm v u]
  exact diagonal_scalar h _

#print axioms sum_inner_pairs
#print axioms diagonal_scalar
#print axioms finiteClockEnergy_integrable
#print axioms finiteClockResponse_integrable
#print axioms finiteClockEnergy_pairing
#print axioms finiteClockResponse_pairing
end
end UnifiedTheory.Audit.KFCausalNeutralFinitePairing

/- The clock amplitudes of a finite neutral superposition can be absorbed
into its complex coefficients separately at each clock coordinate.
This is an algebraic identity for the reduced response, not a claim
that the derivative of those coefficients vanishes. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockState
import UnifiedTheory.Audit.KFCausalNeutralFinitePotential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (pair)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalNeutralCrossKernel
open UnifiedTheory.Audit.KFCausalNeutralCrossDensity (reducedKernel)
open UnifiedTheory.Audit.KFCausalNeutralFiniteGram (finiteKernel)
open UnifiedTheory.Audit.KFCausalNeutralFinitePairing (finiteResponse sum_inner_pairs diagonal_scalar)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockCrossPairing
open UnifiedTheory.Audit.KFCausalNeutralMixedClockState

variable (ε h : ℝ) (N : ℕ) (a p : Fin N → ℝ) (b C : Fin N → ℂ)
  (P : Fin N → Polynomial ℂ)

def clockCoefficients (s : ℝ) (i : Fin N) : ℂ :=
  clockAmplitude ε (a i) (p i) (-h/2) s*C i

def mixedKernel (n : ℕ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, pair ε (a i) (a j) (p i) (p j) (-h/2) s*
    crossKernel ε (-h/2) (groundWidth h) (neutralWidth h)
      (b i) (b j) (C i) (C j) (P i) (P j) n s

def mixedResponse (n : ℕ) (s : ℝ) : ℂ :=
  ∑ i, ∑ j, pair ε (a i) (a j) (p i) (p j) (-h/2) s*
    reducedKernel ε (-h/2) (groundWidth h) (neutralWidth h)
      (b i) (b j) (C i) (C j) (P i) (P j) n s

theorem mixedKernel_frozen (n : ℕ) (s : ℝ) :
    mixedKernel ε h N a p b C P n s =
      finiteKernel ε (-h/2) (groundWidth h) (neutralWidth h)
        N b (clockCoefficients ε h N a p C s) P n s := by
  unfold mixedKernel finiteKernel
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [crossKernel,clockCoefficients,pair,star_mul]
  ring

theorem mixedResponse_frozen (n : ℕ) (s : ℝ) :
    mixedResponse ε h N a p b C P n s =
      finiteResponse ε (-h/2) (groundWidth h) (neutralWidth h)
        N b (clockCoefficients ε h N a p C s) P n s := by
  unfold mixedResponse finiteResponse
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [reducedKernel,crossKernel,crossDerivative,clockCoefficients,pair,star_mul]
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
  (hb : |h| ≤ 2*Real.pi*ε/3) (n : Fin 3)
local notation "u" => output ε h hε hh N a p ha b C P hb (index n)
local notation "v" => momentumOutput ε h hε hh N a p ha b C P hb (index n)

include hε hh ha hb in
theorem mixedKernel_integrable : Integrable (mixedKernel ε h N a p b C P n) volume :=
  integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      clockEnergy_integrable ε (a i) h (p i) hε (ha i) hh hb (a j) (p j) (ha j)
        (b i) (b j) (C i) (C j) (P i) (P j) n

include hε hh ha hb in
theorem mixedResponse_integrable : Integrable (mixedResponse ε h N a p b C P n) volume :=
  integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      clockResponse_integrable ε (a i) h (p i) hε (ha i) hh hb (a j) (p j) (ha j)
        (b i) (b j) (C i) (C j) (P i) (P j) n

theorem mixedKernel_pairing :
    (∫ s, mixedKernel ε h N a p b C P n s) = (‖u‖^2:ℂ) := by
  have hi (i j : Fin N) := clockEnergy_integrable ε (a i) h (p i)
    hε (ha i) hh hb (a j) (p j) (ha j) (b i) (b j) (C i) (C j) (P i) (P j) n
  have hp (i j : Fin N) := clockEnergy_pairing ε (a i) h (p i)
    hε (ha i) hh hb (a j) (p j) (ha j) (b i) (b j) (C i) (C j) (P i) (P j) n
  unfold mixedKernel
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j)]
  simp_rw [hp]
  rw [sum_inner_pairs,inner_self_eq_norm_sq_to_K]
  rfl

theorem mixedResponse_pairing :
    (∫ s, mixedResponse ε h N a p b C P n s) =
      (((-2/h)*(inner ℂ u v).im:ℝ):ℂ) := by
  have hi (i j : Fin N) := clockResponse_integrable ε (a i) h (p i)
    hε (ha i) hh hb (a j) (p j) (ha j) (b i) (b j) (C i) (C j) (P i) (P j) n
  have hp (i j : Fin N) := clockResponse_pairing ε (a i) h (p i)
    hε (ha i) hh hb (a j) (p j) (ha j) (b i) (b j) (C i) (C j) (P i) (P j) n
  unfold mixedResponse
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j)]
  simp_rw [hp]
  simp only [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [sum_inner_pairs,sum_inner_pairs]
  change (Complex.I/(h:ℂ))*(inner ℂ u v-inner ℂ v u) = _
  rw [← inner_conj_symm v u]
  exact diagonal_scalar h _

#print axioms mixedKernel_frozen
#print axioms mixedResponse_frozen
#print axioms mixedKernel_integrable
#print axioms mixedResponse_integrable
#print axioms mixedKernel_pairing
#print axioms mixedResponse_pairing
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockPairing

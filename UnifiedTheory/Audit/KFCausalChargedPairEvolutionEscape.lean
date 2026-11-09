/- The actual completed-form evolution of the centered neutral packet
leaves the restricted neutral closure at every sufficiently nearby
noninitial time. A proved nonzero transition derivative detects this
departure; zero-charge membership of the test state is already proved. -/
import UnifiedTheory.Audit.KFCausalChargedPairTransitionInitial
import Mathlib.Analysis.Calculus.Deriv.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedPairEvolutionEscape
noncomputable section
open Filter
open scoped Topology
open KFCausalChargedPairHamiltonianForm
open KFCausalChargedPairHamiltonianCoupling (formPairing_ne_zero)
open KFCausalChargedPairPotentialCoupling (baseState)
open KFCausalChargedPairDomain (state)
open KFCausalChargedPairCharge (state_neutralClosure_orthogonal)
open KFCausalChargedPairTransitionInitial
open KFCausalClockFloorTransitionDerivative
open KFCausalClockFloorAveragedEvolution
open KFCausalNeutralSwapConstraint (neutralStates)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "ψ₀" => baseState ε a h hε ha hh
local notation "ψ" => state ε a h hε ha hh
local notation "U" => evolution ε hε h hh hb 1 1 1

def amplitude (s t : ℝ) : ℂ := inner ℂ (U s t ψ₀) ψ

theorem amplitude_eq_transition (s : ℝ) :
    amplitude ε a h hε ha hh hb s =
      transition ε hε h hh hb 1 1 1 s
        (baseLift ε a h hε ha hh hb 1 1 1 0)
        (pairedLift ε a h hε ha hh hb 1 1 1 0) := rfl

theorem amplitude_initial (s : ℝ) : amplitude ε a h hε ha hh hb s s = 0 := by
  have he := DFunLike.congr_fun (evolution_initial ε hε h hh hb 1 1 1 s) ψ₀
  change U s s ψ₀ = ψ₀ at he
  rw [amplitude,he]
  exact base_pairing_zero ε a h hε ha hh

theorem amplitude_hasDerivAt (s : ℝ) :
    HasDerivAt (amplitude ε a h hε ha hh hb s)
      ((-Complex.I*(h:ℂ))⁻¹*formPairing ε a h hε ha hh hb 1 1 1 s) s := by
  rw [amplitude_eq_transition,← reference_pairing]
  exact transition_initial_hasDerivAt ε hε h hh hb 1 1 1 s _ _

theorem initial_derivative_ne_zero (s : ℝ) :
    (-Complex.I*(h:ℂ))⁻¹*formPairing ε a h hε ha hh hb 1 1 1 s ≠ 0 := by
  apply mul_ne_zero
  · exact inv_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (by exact_mod_cast hh))
  · exact formPairing_ne_zero ε a h hε ha hh hb s

theorem amplitude_eventually_ne_zero (s : ℝ) :
    ∀ᶠ t in 𝓝[≠] s, amplitude ε a h hε ha hh hb s t ≠ 0 :=
  (amplitude_hasDerivAt ε a h hε ha hh hb s).eventually_ne
    (initial_derivative_ne_zero ε a h hε ha hh hb s)

theorem evolution_eventually_outside_neutralClosure (s : ℝ) :
    ∀ᶠ t in 𝓝[≠] s, U s t ψ₀ ∉ closure (neutralStates ε h hε hh) := by
  filter_upwards [amplitude_eventually_ne_zero ε a h hε ha hh hb s] with t ht
  intro hm
  exact ht (state_neutralClosure_orthogonal ε a h hε ha hh (U s t ψ₀) hm)

theorem evolution_not_confined (s : ℝ) :
    ¬ ∀ t : ℝ, U s t ψ₀ ∈ closure (neutralStates ε h hε hh) := by
  intro hc
  obtain ⟨t,ht⟩ := (evolution_eventually_outside_neutralClosure ε a h hε ha hh hb s).exists
  exact ht (hc t)

#print axioms amplitude_eq_transition
#print axioms amplitude_initial
#print axioms amplitude_hasDerivAt
#print axioms initial_derivative_ne_zero
#print axioms amplitude_eventually_ne_zero
#print axioms evolution_eventually_outside_neutralClosure
#print axioms evolution_not_confined
end
end UnifiedTheory.Audit.KFCausalChargedPairEvolutionEscape

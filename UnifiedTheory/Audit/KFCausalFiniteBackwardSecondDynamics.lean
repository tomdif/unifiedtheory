/- Genuine nonautonomous second differentiation in the initial time for
the original finite sourced states.  The derivative of H(s) psi is an actual
constructed Hilbert vector.  The final-time H(t)^2 propagation problem is
different and is not asserted here. -/
import UnifiedTheory.Audit.KFCausalFiniteHamiltonianTimeDerivative
import UnifiedTheory.Audit.KFCausalClockFloorBackwardSchrodinger
import UnifiedTheory.Audit.KFCausalClockFloorFullDomainDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteBackwardSecondDynamics
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorAveragedEvolution (evolution)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteHamiltonianSquare (firstOutput secondOutput)
open KFCausalFiniteHamiltonianTimeDerivative (outputDerivative output_derivative)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum : ℝ)
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "F" => firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "G" => secondOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "F'" => outputDerivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "H" => hamiltonian ε hε h hh hb₀ mass2 quartic vacuum
local notation "U" => evolution ε hε h hh hb₀ mass2 quartic vacuum
local notation "d" => (Complex.I*((1/h:ℝ):ℂ))

private theorem backward_graph (s t : ℝ) (x y : Hilbert)
    (hxy : (x,y) ∈ (H s).graph) :
    HasDerivAt (fun r => U r t x) (d • U s t y) s := by
  obtain ⟨v,hx,hy⟩ := (H s).mem_graph_iff.mp hxy
  dsimp only at hx hy
  rw [← hx,← hy]
  simpa only [neg_mul,neg_neg] using
    KFCausalClockFloorBackwardSchrodinger.backward_derivative
      ε hε h hh hb₀ mass2 quartic vacuum s t v

theorem backward_first_derivative (s t : ℝ) :
    HasDerivAt (fun r => U r t ψ) (d • U s t (F s)) s :=
  backward_graph ε h hε hh hb mass2 quartic vacuum s t ψ (F s)
    (KFCausalFiniteHamiltonianSquare.first_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s)

theorem backward_output_derivative (s t : ℝ) :
    HasDerivAt (fun r => U r t (F r)) (d • U s t (G s)+U s t (F' s)) s := by
  have hz := KFCausalStrongIsometryDerivative.derivative_at_zero_vector
    (fun r => U r t)
    (KFCausalClockFloorAveragedEvolutionContinuity.evolution_initial_time_continuous
      ε hε h hh hb₀ mass2 quartic vacuum t)
    (fun r => F r-F s) (F' s) s
    ((output_derivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s).sub_const (F s))
    (sub_self (F s))
  have hf := backward_graph ε h hε hh hb mass2 quartic vacuum
    s t (F s) (G s)
    (KFCausalFiniteHamiltonianSquare.second_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s)
  have hsum := hz.add hf
  change HasDerivAt (fun r => U r t (F r-F s)+U r t (F s))
    (U s t (F' s)+d • U s t (G s)) s at hsum
  simp only [map_sub,sub_add_cancel] at hsum
  convert hsum using 1
  exact add_comm _ _

theorem backward_second_derivative (s t : ℝ) :
    HasDerivAt (fun r => deriv (fun v => U v t ψ) r)
      (((-((1/h)^2):ℝ):ℂ) • U s t (G s)+d • U s t (F' s)) s := by
  have he : deriv (fun v => U v t ψ) = fun r => d • U r t (F r) :=
    funext (fun r => (backward_first_derivative
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r t).deriv)
  rw [he]
  have hd : d*d = ((-((1/h)^2):ℝ):ℂ) := by
    rw [← pow_two,mul_pow]
    simp
  simpa only [smul_add,smul_smul,hd] using
    (backward_output_derivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s t).const_smul d

theorem backward_derivative_forward_domain (s t : ℝ) (hst : s ≤ t) :
    deriv (fun r => U r t ψ) s ∈ (H t).domain := by
  rw [(backward_first_derivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s t).deriv]
  exact (H t).domain.smul_mem _
    (KFCausalClockFloorFullDomainDynamics.forward_domain
      ε hε h hh hb₀ mass2 quartic vacuum s t hst
      ⟨F s,KFCausalFiniteHamiltonianSquare.output_domain
        n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩)

theorem mixed_time_derivative (s t : ℝ) (hst : s ≤ t) :
    ∃ hx : U s t (F s) ∈ (H t).domain,
      HasDerivAt (fun r => deriv (fun v => U v r ψ) s)
        ((((1/h)^2:ℝ):ℂ) • H t ⟨U s t (F s),hx⟩) t := by
  obtain ⟨hx,hder⟩ := KFCausalClockFloorFullDomainDynamics.forward_schrodinger
    ε hε h hh hb₀ mass2 quartic vacuum s t hst
    ⟨F s,KFCausalFiniteHamiltonianSquare.output_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩
  refine ⟨hx,?_⟩
  have he : (fun r => deriv (fun v => U v r ψ) s) = fun r => d • U s r (F s) :=
    funext (fun r => (backward_first_derivative
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s r).deriv)
  rw [he]
  have hd : d*(-Complex.I*((1/h:ℝ):ℂ)) = (((1/h)^2:ℝ):ℂ) := by
    calc
      d*(-Complex.I*((1/h:ℝ):ℂ)) = -(Complex.I^2)*(((1/h:ℝ):ℂ)^2) := by ring
      _ = (((1/h)^2:ℝ):ℂ) := by simp
  simpa only [smul_smul,hd] using hder.const_smul d

#print axioms backward_first_derivative
#print axioms backward_output_derivative
#print axioms backward_second_derivative
#print axioms backward_derivative_forward_domain
#print axioms mixed_time_derivative
end
end UnifiedTheory.Audit.KFCausalFiniteBackwardSecondDynamics

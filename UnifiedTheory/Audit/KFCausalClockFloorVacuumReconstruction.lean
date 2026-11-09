/- Reconstruction of the full vacuum clock Hamilton equations from the
globally defined scalar clock ODE. No positive-potential division is used,
so zero vacuum coupling is included. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
import UnifiedTheory.Audit.KFCausalScalarIntegratingFactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorReducedODE
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
open UnifiedTheory.Audit.KFCausalScalarIntegratingFactor

def candidate (ε J s : ℝ) : ℝ := J+2*chart ε s-clock ε s/2

theorem candidate_rate (ε J s : ℝ) (hε : 0 < ε) :
    candidate ε J s = clock ε s*rate ε J s := by
  have hc := (clock_positive ε s hε.le).ne'
  unfold candidate rate chart
  field_simp
  unfold clock
  ring

def growth (ε : ℝ) (s : ℝ → ℝ) (t : ℝ) : ℝ := 2-response ε (s t)/2

theorem growth_continuous (ε : ℝ) (hε : 0 < ε) (s : ℝ → ℝ) (hs : Continuous s) :
    Continuous (growth ε s) := by
  exact continuous_const.sub (((Real.continuous_exp.comp hs).div
    ((Real.continuous_exp.comp hs).add continuous_const)
    (fun t => (clock_positive ε (s t) hε.le).ne')).div_const 2)

theorem candidate_derivative (ε J : ℝ) (hε : 0 < ε) (s : ℝ → ℝ) (t : ℝ)
    (hs : HasDerivAt s (rate ε J (s t)) t) :
    HasDerivAt (fun u => candidate ε J (s u)) (growth ε s t*candidate ε J (s t)) t := by
  have hd := ((((chart_derivative ε (s t)).comp t hs).const_mul 2).const_add J).sub
    (((hs.exp).add_const ε).div_const 2)
  convert hd using 1
  rw [candidate_rate ε J (s t) hε]
  unfold growth response
  have hc := (clock_positive ε (s t) hε.le).ne'
  field_simp
  unfold clock
  ring

def liftedLongitudinal (ε : ℝ) (s : ℝ → ℝ) (L₀ t : ℝ) : ℝ :=
  L₀+Real.log (clock ε (s t))-Real.log (clock ε (s 0))+primitive (growth ε s) t-2*t

theorem liftedLongitudinal_initial (ε : ℝ) (s : ℝ → ℝ) (L₀ : ℝ) :
    liftedLongitudinal ε s L₀ 0 = L₀ := by
  simp only [liftedLongitudinal,primitive,intervalIntegral.integral_same,add_zero,mul_zero,sub_zero]
  ring

theorem liftedLongitudinal_derivative (ε J : ℝ) (hε : 0 < ε) (s : ℝ → ℝ) (L₀ t : ℝ)
    (hs : ∀ u, HasDerivAt s (rate ε J (s u)) u) :
    HasDerivAt (liftedLongitudinal ε s L₀)
      (response ε (s t)*(-1/2+rate ε J (s t))) t := by
  have hc := (clock_positive ε (s t) hε.le).ne'
  have hg := growth_continuous ε hε s (continuous_iff_continuousAt.mpr (fun u => (hs u).continuousAt))
  have hd := ((((((hs t).exp).add_const ε).log hc).const_add L₀).sub_const
    (Real.log (clock ε (s 0)))).add (primitive_derivative (growth ε s) hg t)
  have hd' := hd.sub ((hasDerivAt_id t).const_mul 2)
  convert hd' using 1
  unfold growth response clock
  ring

theorem lifted_amplitude (ε κ : ℝ) (hε : 0 < ε) (s : ℝ → ℝ) (L₀ t : ℝ) :
    amplitude ε κ t (s t) (liftedLongitudinal ε s L₀ t) =
      (κ*Real.exp L₀/clock ε (s 0))*Real.exp (primitive (growth ε s) t) := by
  have hc := clock_positive ε (s t) hε.le
  have hc0 := clock_positive ε (s 0) hε.le
  have he : 2*t+liftedLongitudinal ε s L₀ t =
      L₀+Real.log (clock ε (s t))-Real.log (clock ε (s 0))+primitive (growth ε s) t := by
    unfold liftedLongitudinal
    ring
  rw [amplitude,he,Real.exp_add,Real.exp_sub,Real.exp_add,Real.exp_log hc,Real.exp_log hc0]
  field_simp

theorem candidate_initial (ε κ s₀ L₀ : ℝ) :
    candidate ε (invariant ε κ 0 s₀ L₀) s₀ = κ*Real.exp L₀/clock ε s₀ := by
  unfold candidate invariant energy amplitude
  simp only [mul_zero,zero_add]
  ring

theorem reconstruct_equations (ε κ : ℝ) (hε : 0 < ε) (s : ℝ → ℝ) (L₀ : ℝ)
    (hs : ∀ t, HasDerivAt s (rate ε (invariant ε κ 0 (s 0) L₀) (s t)) t) (t : ℝ) :
    HasDerivAt s (amplitude ε κ t (s t) (liftedLongitudinal ε s L₀ t)/clock ε (s t)) t ∧
    HasDerivAt (liftedLongitudinal ε s L₀)
      (response ε (s t)*(-1/2+amplitude ε κ t (s t) (liftedLongitudinal ε s L₀ t)/clock ε (s t))) t := by
  let J := invariant ε κ 0 (s 0) L₀
  have hg := growth_continuous ε hε s (continuous_iff_continuousAt.mpr (fun u => (hs u).continuousAt))
  have he := solution_formula (fun u => candidate ε J (s u)) (growth ε s) hg
    (fun u => candidate_derivative ε J hε s u (hs u)) t
  rw [candidate_initial] at he
  have hA : amplitude ε κ t (s t) (liftedLongitudinal ε s L₀ t) = clock ε (s t)*rate ε J (s t) :=
    (lifted_amplitude ε κ hε s L₀ t).trans (he.symm.trans (candidate_rate ε J (s t) hε))
  rw [hA,mul_div_cancel_left₀ _ (clock_positive ε (s t) hε.le).ne']
  exact ⟨hs t,liftedLongitudinal_derivative ε J hε s L₀ t hs⟩

theorem exists_global_vacuum (ε κ s₀ L₀ : ℝ) (hε : 0 < ε) :
    ∃ s L : ℝ → ℝ, s 0 = s₀ ∧ L 0 = L₀ ∧
      (∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t) ∧
      (∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t) := by
  obtain ⟨s,hs0,hs⟩ := exists_global_clock ε (invariant ε κ 0 s₀ L₀) s₀ hε
  have hs' : ∀ t, HasDerivAt s (rate ε (invariant ε κ 0 (s 0) L₀) (s t)) t := by
    rw [hs0]
    exact hs
  exact ⟨s,liftedLongitudinal ε s L₀,hs0,liftedLongitudinal_initial ε s L₀,
    fun t => (reconstruct_equations ε κ hε s L₀ hs' t).1,
    fun t => (reconstruct_equations ε κ hε s L₀ hs' t).2⟩

theorem exists_global_canonical (ε κ s₀ p₀ : ℝ) (hε : 0 < ε) :
    ∃ s p : ℝ → ℝ, s 0 = s₀ ∧ p 0 = p₀ ∧
      (∀ t, HasDerivAt s (deriv (canonicalHamiltonian ε κ t (s t)) (p t)) t) ∧
      (∀ t, HasDerivAt p (-deriv (fun x => canonicalHamiltonian ε κ t x (p t)) (s t)) t) ∧
      ∀ t, ε < clock ε (s t) := by
  obtain ⟨s,L,hs0,hL0,hs,hL⟩ := exists_global_vacuum ε κ s₀ (p₀/clock ε s₀) hε
  refine ⟨s,fun t => clock ε (s t)*L t,hs0,?_,
    fun t => (canonical_equations ε κ hε s L t (hs t) (hL t)).1,
    fun t => (canonical_equations ε κ hε s L t (hs t) (hL t)).2,
    fun t => KFCausalClockFloorFlow.clock_above_floor ε (s t)⟩
  change clock ε (s 0)*L 0 = p₀
  rw [hs0,hL0,mul_div_cancel₀ _ (clock_positive ε s₀ hε.le).ne']

#print axioms candidate_rate
#print axioms growth_continuous
#print axioms candidate_derivative
#print axioms liftedLongitudinal_initial
#print axioms liftedLongitudinal_derivative
#print axioms lifted_amplitude
#print axioms candidate_initial
#print axioms reconstruct_equations
#print axioms exists_global_vacuum
#print axioms exists_global_canonical

end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumReconstruction

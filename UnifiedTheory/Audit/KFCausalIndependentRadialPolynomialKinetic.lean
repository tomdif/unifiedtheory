/- The bounded inverse half-clock changes only the clock profile of
the actual polynomial span. Two proved momentum steps therefore give
every original kinetic second graph on that span. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialMomentum
import UnifiedTheory.Audit.KFCausalClockFloorKineticSquare
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialKinetic
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalIndependentRadialPolynomialMomentum (state space state_charge_coe state_mem symmetric_invariant antisymmetric_invariant)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalNaturalSecondHamiltonianGraph (component)

def inverseClock (ε : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ :=
  (Real.sqrt (Real.exp s+ε):ℂ)⁻¹*g s

theorem inverseClock_continuous (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (hc : Continuous g) :
    Continuous (inverseClock ε g) := by
  have hq : Continuous (fun s : ℝ => (Real.sqrt (Real.exp s+ε):ℂ)) := by fun_prop
  exact (hq.inv₀ (fun s => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')).mul hc

theorem inverseClock_memLp (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) : MemLp (inverseClock ε g) 2 volume := by
  apply (hg.const_mul ((Real.sqrt ε)⁻¹:ℂ)).of_le
    (inverseClock_continuous ε hε g hc).aestronglyMeasurable
  filter_upwards [] with s
  simp only [inverseClock,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (KFCausalClockFloorClockHalf.inverseWeight_bound ε hε (s,0)) (norm_nonneg _)

variable (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : 0 < wL) (hR : 0 < wR)
  (hmatch : Real.pi^2/α=α*c^2) (b : ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
  (ε : ℝ) (hε : 0 < ε)

theorem inverse_state (P : Polynomial ℂ) (n : Fin 4 → ℕ) :
    inverseL ε hε (state α β wL wR c hα hβ hL hR hmatch b g hc hg P n)=
      state α β wL wR c hα hβ hL hR hmatch b (inverseClock ε g)
        (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) P n := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [KFCausalClockFloorAntisymmetricGraph.inverseL_charge_coe ε hε
    (state α β wL wR c hα hβ hL hR hmatch b g hc hg P n),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P n,
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b (inverseClock ε g)
      (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) P n] with x hi hf hd
  rw [hi,hf,hd]
  unfold KFCausalIndependentRadialCoordinateMoments.profile
    KFCausalIndependentRadialPacketProfiles.chargeProfile inverseClock KFCausalClockFloorFlow.clock
  ring

theorem inverse_space (f : Hilbert) (hf : f ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg) :
    inverseL ε hε f ∈ space α β wL wR c hα hβ hL hR hmatch b (inverseClock ε g)
      (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨P,n⟩,rfl⟩ := hf
      rw [inverse_state]
      exact state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | zero => simpa only [map_zero] using (Submodule.zero_mem
      (space α β wL wR c hα hβ hL hR hmatch b (inverseClock ε g)
        (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg)))
  | add f₁ f₂ _ _ hf₁ hf₂ => simpa only [map_add] using Submodule.add_mem _ hf₁ hf₂
  | smul z f _ hf => simpa only [map_smul] using Submodule.smul_mem _ z hf

theorem momentum_invariant (h : ℝ) (hh : h ≠ 0) (i : Fin 4) (f : Hilbert)
    (hf : f ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg) :
    ∃ d : Hilbert, d ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg ∧
      (f,d) ∈ (transverseMomentum h (modelDirections i)).graph := by
  fin_cases i
  · exact symmetric_invariant α β wL wR c hα hβ hL hR hmatch b g hc hg h hh 0 f hf
  · exact symmetric_invariant α β wL wR c hα hβ hL hR hmatch b g hc hg h hh 1 f hf
  · exact antisymmetric_invariant α β wL wR c hα hβ hL hR hmatch b g hc hg h hh 0 f hf
  · exact antisymmetric_invariant α β wL wR c hα hβ hL hR hmatch b g hc hg h hh 1 f hf

def kineticIndex (i : Fin 4) : Fin 8 := ![1,2,3,4] i

theorem kinetic_component (h : ℝ) (i : Fin 4) :
    component ε hε h (kineticIndex i)=KFCausalClockFloorKineticSquare.square ε h (modelDirections i) := by
  fin_cases i <;> rfl

theorem kinetic_graph_exists (h : ℝ) (hh : h ≠ 0) (i : Fin 4) (f : Hilbert)
    (hf : f ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg) :
    ∃ z : Hilbert, (f,z) ∈ (component ε hε h (kineticIndex i)).graph := by
  have hd := inverse_space α β wL wR c hα hβ hL hR hmatch b g hc hg ε hε f hf
  obtain ⟨u,hu,hfu⟩ := momentum_invariant α β wL wR c hα hβ hL hR hmatch b (inverseClock ε g)
    (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) h hh i _ hd
  obtain ⟨v,hv,huv⟩ := momentum_invariant α β wL wR c hα hβ hL hR hmatch b (inverseClock ε g)
    (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) h hh i u hu
  refine ⟨inverseL ε hε v,?_⟩
  rw [kinetic_component]
  exact (KFCausalClockFloorKineticSquare.square_graph ε hε h (modelDirections i) f _).mpr ⟨u,v,hfu,huv,rfl⟩

#print axioms inverseClock_continuous
#print axioms inverseClock_memLp
#print axioms inverse_state
#print axioms inverse_space
#print axioms momentum_invariant
#print axioms kinetic_component
#print axioms kinetic_graph_exists
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialKinetic

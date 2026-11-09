/- The domain constructed from the Laplace resolvent is exactly the full
right-derivative domain of the actual OS semigroup, not merely a chosen core. -/
import UnifiedTheory.Clay.YangMills.OSLaplaceGenerator
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSGeneratorDomain
noncomputable section
open ContinuumControl PeriodicLattice4 OSPositiveTimeKernel OSScalarDynamics
open OSLaplaceResolvent OSLaplaceHamiltonian OSLaplaceGenerator

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane} (D : Evolution W plane hp)

/-- A right derivative pairs against every operator-domain vector by
symmetry of the actual time evolution. -/
theorem derivative_pairing (v w : State (hp := hp))
    (hd : HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal v) w (Set.Ici 0) 0)
    (x : (hamiltonian D).domain) :
    inner ℂ (-w) (x : State (hp := hp)) = inner ℂ v (hamiltonian D x) := by
  have h₁ := hd.inner ℂ (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (x : State (hp := hp)))
  have h₂ := (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) v).inner ℂ (right_derivative D x)
  have h₁' : HasDerivWithinAt
      (fun t : ℝ => inner ℂ v (D.operator t.toNNReal (x : State (hp := hp))))
      (inner ℂ w (x : State (hp := hp))) (Set.Ici 0) 0 := by
    simpa only [D.symmetric, Real.toNNReal_zero, D.zero, inner_zero_right, zero_add] using h₁
  have h₂' : HasDerivWithinAt
      (fun t : ℝ => inner ℂ v (D.operator t.toNNReal (x : State (hp := hp))))
      (inner ℂ v (-hamiltonian D x)) (Set.Ici 0) 0 := by
    simpa only [Real.toNNReal_zero, D.zero, inner_zero_left, add_zero] using h₂
  have he := (h₁'.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (h₂'.derivWithin (uniqueDiffWithinAt_Ici 0))
  rw [inner_neg_left, he, inner_neg_right, neg_neg]

/-- Exact graph characterization: the Hamiltonian is the negative generator
on the maximal domain where the actual evolution has a right derivative. -/
theorem derivative_iff_graph (v w : State (hp := hp)) :
    HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal v) w (Set.Ici 0) 0 ↔
      (v,-w) ∈ (hamiltonian D).graph := by
  constructor
  · intro hd
    have hpair := derivative_pairing D v w hd
    have hm := LinearPMap.mem_adjoint_domain_of_exists (T := hamiltonian D) v ⟨-w,hpair⟩
    have ha := LinearPMap.adjoint_apply_eq (dense_domain D) ⟨v,hm⟩ hpair
    have hg : (v,-w) ∈ (hamiltonian D).adjoint.graph :=
      (hamiltonian D).adjoint.mem_graph_iff.mpr ⟨⟨v,hm⟩,rfl,ha⟩
    rw [LinearPMap.isSelfAdjoint_def.mp (selfAdjoint D)] at hg
    exact hg
  · intro hg
    obtain ⟨x,hx,he⟩ := (hamiltonian D).mem_graph_iff.mp hg
    simpa only [hx,he,neg_neg] using right_derivative D x

theorem mem_domain_iff_right_derivative (v : State (hp := hp)) :
    v ∈ (hamiltonian D).domain ↔
      ∃ w : State (hp := hp),
        HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal v) w (Set.Ici 0) 0 := by
  constructor
  · intro hv
    exact ⟨-hamiltonian D ⟨v,hv⟩,right_derivative D ⟨v,hv⟩⟩
  · rintro ⟨w,hw⟩
    obtain ⟨x,hx,_⟩ := (hamiltonian D).mem_graph_iff.mp ((derivative_iff_graph D v w).mp hw)
    change (x : State (hp := hp)) = v at hx
    rw [← hx]
    exact x.property

end
end UnifiedTheory.Clay.YangMills.OSGeneratorDomain

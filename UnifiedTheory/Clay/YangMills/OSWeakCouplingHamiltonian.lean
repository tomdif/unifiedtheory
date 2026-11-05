/- Along actual beta-to-infinity Wilson trajectories the unscaled real-character
OS Hamiltonian is zero on the full Hilbert space. Its positive real numbers
all have bounded two-sided inverses, so the required finite excitation fails.
This is not an obstruction to centered and rescaled Yang--Mills limits. -/
import UnifiedTheory.Clay.YangMills.OSGeneratorDomain
import UnifiedTheory.Clay.YangMills.OSWeakCouplingCollapse
import UnifiedTheory.Clay.YangMills.SpectralGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSWeakCouplingHamiltonian
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open OSScalarDynamics OSLaplaceResolvent OSLaplaceHamiltonian OSGeneratorDomain BareDefectHierarchy
open scoped NNReal Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {d : Type*} [Fintype d] [DecidableEq d]
  (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
  (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
  (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop atTop) (W : Hierarchy)
  (hW : WeakConvergence (fun k => unitaryHierarchy (period k) (a k) plane ρ hρ (beta k)) W)
  (hp : Positive W plane) (D : Evolution W plane hp)

include hbeta hW in
theorem derivative_zero (v : State (hp := hp)) :
    HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal v) 0 (Set.Ici 0) 0 := by
  simpa only [OSWeakCouplingCollapse.evolution_identity period a plane ρ hρ beta hbeta W hW hp D]
    using (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) v)

include hbeta hW in
theorem zero_graph (v : State (hp := hp)) : (v,0) ∈ (hamiltonian D).graph := by
  simpa only [neg_zero] using (derivative_iff_graph D v 0).mp
    (derivative_zero period a plane ρ hρ beta hbeta W hW hp D v)

include hbeta hW in
theorem domain_top : (hamiltonian D).domain = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨x,hx,_⟩ := (hamiltonian D).mem_graph_iff.mp
    (zero_graph period a plane ρ hρ beta hbeta W hW hp D v)
  change (x : State (hp := hp)) = v at hx
  rw [← hx]
  exact x.property

include hbeta hW in
theorem zero_action (x : (hamiltonian D).domain) : hamiltonian D x = 0 := by
  obtain ⟨y,hy,he⟩ := (hamiltonian D).mem_graph_iff.mp
    (zero_graph period a plane ρ hρ beta hbeta W hW hp D (x : State (hp := hp)))
  have hh : y = x := Subtype.ext hy
  simpa only [hh] using he

/-- The inverse is explicitly -1/lam times identity, with both laws in the
actual unbounded-operator spectral interface. -/
def nonzeroResolvent (lam : ℝ) (hlam : lam ≠ 0) :
    SpectralGap.ResolventWitness (hamiltonian D) lam where
  inverse := (-(lam : ℂ)⁻¹) • ContinuousLinearMap.id ℂ (State (hp := hp))
  right_inverse y := by
    have hc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    have he : y + (lam : ℂ) • ((-(lam : ℂ)⁻¹) • y) = 0 := by
      simp [smul_smul, mul_inv_cancel₀ hc]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, he]
    exact zero_graph period a plane ρ hρ beta hbeta W hW hp D _
  left_inverse x := by
    have hc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    change (-(lam : ℂ)⁻¹) • (hamiltonian D x - (lam : ℂ) • (x : State (hp := hp))) = x
    rw [zero_action period a plane ρ hρ beta hbeta W hW hp D x]
    simp only [zero_sub, smul_neg, neg_smul, neg_neg, smul_smul, neg_mul,
      inv_mul_cancel₀ hc, one_smul]

include hbeta hW in
/-- The bare collapsed candidate fails the finite positive excitation target,
even though an empty vacuum-orthogonal sector would make gap-only tests vacuous. -/
theorem not_finiteExcitation : ¬ SpectralGap.FiniteExcitation (hamiltonian D) := by
  rintro ⟨lam,hlam,hnot⟩
  exact hnot ⟨nonzeroResolvent period a plane ρ hρ beta hbeta W hW hp D lam (ne_of_gt hlam)⟩

include hbeta hW in
theorem not_spectralRequirements (Ω : State (hp := hp)) (Δ : ℝ) :
    ¬ SpectralGap.SpectralRequirements (hamiltonian D) Ω Δ := by
  intro h
  exact not_finiteExcitation period a plane ρ hρ beta hbeta W hW hp D h.finite_excitation

end
end UnifiedTheory.Clay.YangMills.OSWeakCouplingHamiltonian

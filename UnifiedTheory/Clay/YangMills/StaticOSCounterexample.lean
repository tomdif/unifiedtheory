/- A positive fixed reflected fluctuation and all-order Schwartz bounds do
not force positive energy or vacuum uniqueness. The explicit static random-
sign hierarchy has a nonzero orthogonal state but its constructed OS generator
is zero everywhere. This is not claimed to arise from a Wilson trajectory. -/
import UnifiedTheory.Clay.YangMills.StaticSchwartzHierarchy
import UnifiedTheory.Clay.YangMills.OSGeneratorDomain
import UnifiedTheory.Clay.YangMills.OSHamiltonianVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.StaticOSCounterexample
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel OSScalarDynamics
open KernelHilbertCompletion OSFactorizedCollapse StaticSchwartzHierarchy
open OSLaplaceResolvent OSLaplaceHamiltonian OSGeneratorDomain
open scoped NNReal Topology

variable (plane : Plane)

theorem canonical_shift (t : ℝ≥0) (i : Label) :
    canonical (positiveKernel hierarchy plane (positive plane)) (shift t i) =
      canonical (positiveKernel hierarchy plane (positive plane)) i := by
  apply (StaticSchwartzHierarchy.realization plane).injective
  rw [StaticSchwartzHierarchy.realization_canonical,
    StaticSchwartzHierarchy.realization_canonical, StaticSchwartzHierarchy.amplitude_shift]

variable (D : Evolution hierarchy plane (positive plane))

/-- Every evolution implementing the actual canonical time shifts is identity. -/
theorem evolution_identity (t : ℝ≥0)
    (v : Hilbert (positiveKernel hierarchy plane (positive plane))) : D.operator t v = v := by
  classical
  refine (denseRange_embed (positiveKernel hierarchy plane (positive plane))).induction_on v
    (isClosed_eq (D.operator t).continuous continuous_id) ?_
  intro x
  induction x using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add i c x hi hc ih =>
      have he : embed (positiveKernel hierarchy plane (positive plane)) (Finsupp.single i c) =
          c • canonical (positiveKernel hierarchy plane (positive plane)) i := by
        change embed _ (Finsupp.single i c) = c • embed _ (Finsupp.single i 1)
        rw [← map_smul]
        congr 1
        change (Finsupp.single i c : Label →₀ ℂ) = c • Finsupp.single i 1
        simp
      simp only [map_add, he, map_smul, D.canonical_action, canonical_shift, ih]

theorem zero_graph (v : Hilbert (positiveKernel hierarchy plane (positive plane))) :
    (v,0) ∈ (hamiltonian D).graph := by
  have hd : HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal v) 0 (Set.Ici 0) 0 := by
    simpa only [evolution_identity plane D] using
      hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) v
  simpa only [neg_zero] using (derivative_iff_graph D v 0).mp hd

theorem domain_top : (hamiltonian D).domain = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨x,hx,_⟩ := (hamiltonian D).mem_graph_iff.mp (zero_graph plane D v)
  change (x : Hilbert (positiveKernel hierarchy plane (positive plane))) = v at hx
  rw [← hx]
  exact x.property

theorem zero_action (x : (hamiltonian D).domain) : hamiltonian D x = 0 := by
  obtain ⟨y,hy,he⟩ := (hamiltonian D).mem_graph_iff.mp
    (zero_graph plane D (x : Hilbert (positiveKernel hierarchy plane (positive plane))))
  have hh : y = x := Subtype.ext hy
  simpa only [hh] using he

def nonzeroResolvent (lam : ℝ) (hlam : lam ≠ 0) :
    SpectralGap.ResolventWitness (hamiltonian D) lam where
  inverse := (-(lam : ℂ)⁻¹) • ContinuousLinearMap.id ℂ
    (Hilbert (positiveKernel hierarchy plane (positive plane)))
  right_inverse y := by
    have hc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    have he : y + (lam : ℂ) • ((-(lam : ℂ)⁻¹) • y) = 0 := by
      simp [smul_smul, mul_inv_cancel₀ hc]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, he]
    exact zero_graph plane D _
  left_inverse x := by
    have hc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    change (-(lam : ℂ)⁻¹) • (hamiltonian D x - (lam : ℂ) •
      (x : Hilbert (positiveKernel hierarchy plane (positive plane)))) = x
    rw [zero_action plane D x]
    simp only [zero_sub, smul_neg, neg_smul, neg_neg, smul_smul, neg_mul,
      inv_mul_cancel₀ hc, one_smul]

theorem not_finiteExcitation : ¬ SpectralGap.FiniteExcitation (hamiltonian D) := by
  rintro ⟨lam,hlam,hnot⟩
  exact hnot ⟨nonzeroResolvent plane D lam (ne_of_gt hlam)⟩

/-- The zero-energy sector genuinely contains a normalized non-vacuum state. -/
theorem nonvacuum_zero_mode :
    ∃ v : Hilbert (positiveKernel hierarchy plane (positive plane)),
      ‖v‖ = 1 ∧ inner ℂ (OSVacuumSector.vacuum hierarchy plane (positive plane)) v = 0 ∧
      (v,0) ∈ (hamiltonian D).graph :=
  ⟨witness plane, witness_norm plane, witness_orthogonal plane, zero_graph plane D _⟩

theorem witness_time_pairing (t : ℝ≥0) :
    inner ℂ (witness plane) (D.operator t (witness plane)) = 1 := by
  rw [evolution_identity, inner_self_eq_norm_sq_to_K, witness_norm]
  norm_num

/-- A time-clustering estimate is an additional input: positivity and the
all-order bound in this example do not supply it. -/
theorem witness_not_time_clustered :
    ¬ Tendsto (fun t : ℝ≥0 => inner ℂ (witness plane) (D.operator t (witness plane)))
      atTop (𝓝 0) := by
  intro ht
  have hc : Tendsto (fun t : ℝ≥0 => inner ℂ (witness plane) (D.operator t (witness plane)))
      atTop (𝓝 1) := by simpa only [witness_time_pairing] using tendsto_const_nhds
  have h := tendsto_nhds_unique hc ht
  norm_num at h

/-- This is the dynamics produced by the proved tempered OS reconstruction. -/
def actualEvolution : Evolution hierarchy plane (positive plane) :=
  OSTemperedDynamics.evolution hierarchy plane (positive plane) stationary

theorem actual_counterexample :
    (∀ f : CorrelationTest 0, hierarchy.correlation 0 f = ∫ x, f x) ∧
    Bounded hierarchy 1 ∧ Stationary hierarchy ∧
    (∀ (m : ℕ) (v : LocalFields.Spacetime) (f : CorrelationTest m),
      hierarchy.correlation m
        (SchwartzTranslations.translationCLM (CellSpacetimeTranslation.displacement m v) f) =
        hierarchy.correlation m f) ∧
    FullPositiveTimeReflection.Positive hierarchy plane ∧
    KernelHilbertCompletion.connectedVariance (positiveKernel hierarchy plane (positive plane))
      vacuumLabel witnessLabel = 1 ∧
    (∃ v : Hilbert (positiveKernel hierarchy plane (positive plane)),
      ‖v‖ = 1 ∧ inner ℂ (OSVacuumSector.vacuum hierarchy plane (positive plane)) v = 0 ∧
      (v,0) ∈ (hamiltonian (actualEvolution plane)).graph) ∧
    ¬ SpectralGap.FiniteExcitation (hamiltonian (actualEvolution plane)) :=
  ⟨normalized,bounded,stationary,spacetime_translation,full_positive plane,connected_floor plane,
    nonvacuum_zero_mode plane (actualEvolution plane),
    not_finiteExcitation plane (actualEvolution plane)⟩

end
end UnifiedTheory.Clay.YangMills.StaticOSCounterexample

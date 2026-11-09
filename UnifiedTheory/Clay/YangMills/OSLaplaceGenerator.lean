/- The operator defined from the actual OS Laplace resolvent is tied back to
time evolution: domain invariance, commutation, and its right derivative law. -/
import UnifiedTheory.Clay.YangMills.OSLaplaceHamiltonian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSLaplaceGenerator
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open OSScalarDynamics OSLaplaceResolvent OSLaplaceHamiltonian
open scoped NNReal Topology

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane} (D : Evolution W plane hp)

theorem resolvent_commutes (s : ℝ≥0) (x : State (hp := hp)) :
    D.operator s (resolvent D x) = resolvent D (D.operator s x) := by
  rw [resolvent_apply, resolvent_apply]
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, D.operator s (integrand D x t) :=
      (((D.operator s).restrictScalars ℝ).integral_comp_comm (integrand_integrable D x)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        simp only [integrand, ContinuousLinearMap.map_smul_of_tower, D.add, add_comm])

theorem evolution_mem_domain (s : ℝ≥0) (x : (hamiltonian D).domain) :
    D.operator s (x : State (hp := hp)) ∈ (hamiltonian D).domain := by
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,rfl⟩ := hx
  exact ⟨D.operator s y, (resolvent_commutes D s y).symm⟩

def evolveDomain (s : ℝ≥0) (x : (hamiltonian D).domain) : (hamiltonian D).domain :=
  ⟨D.operator s x,evolution_mem_domain D s x⟩

theorem hamiltonian_commutes (s : ℝ≥0) (x : (hamiltonian D).domain) :
    hamiltonian D (evolveDomain D s x) = D.operator s (hamiltonian D x) := by
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,rfl⟩ := hx
  change hamiltonian D (evolveDomain D s (rangePoint D y)) =
    D.operator s (hamiltonian D (rangePoint D y))
  have he : evolveDomain D s (rangePoint D y) = rangePoint D (D.operator s y) := by
    apply Subtype.ext
    exact resolvent_commutes D s y
  rw [he, apply_range, apply_range, map_sub, resolvent_commutes]

theorem integral_shift (s : ℝ) (x : State (hp := hp)) :
    (∫ t : ℝ in Set.Ioi 0, integrand D x (t+s)) =
      ∫ t : ℝ in Set.Ioi s, integrand D x t := by
  have h := (measurePreserving_add_right volume s).setIntegral_preimage_emb
    (Homeomorph.addRight s).measurableEmbedding (integrand D x) (Set.Ioi s)
  have he : (fun t : ℝ => t+s) ⁻¹' Set.Ioi s = Set.Ioi 0 := by
    ext t
    simp
  rw [he] at h
  exact h

theorem integrand_shift (s : ℝ≥0) (x : State (hp := hp)) (t : ℝ) (ht : 0 ≤ t) :
    D.operator s (integrand D x t) = Real.exp (s : ℝ) • integrand D x (t+s) := by
  have he : Real.exp (s : ℝ) * Real.exp (-(t+s)) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [integrand, ContinuousLinearMap.map_smul_of_tower, D.add,
    Real.toNNReal_add ht s.coe_nonneg, Real.toNNReal_coe, smul_smul, he, add_comm]

/-- Exact relation between the Laplace resolvent and a finite forward shift. -/
theorem evolution_resolvent (s : ℝ≥0) (x : State (hp := hp)) :
    D.operator s (resolvent D x) = Real.exp (s : ℝ) •
      (resolvent D x - ∫ t : ℝ in 0..(s : ℝ), integrand D x t) := by
  have hi : IntegrableOn (integrand D x) (Set.Ioi (s : ℝ)) volume :=
    (show IntegrableOn (integrand D x) (Set.Ioi 0) volume from
      integrand_integrable D x).mono_set (Set.Ioi_subset_Ioi s.coe_nonneg)
  have ht := intervalIntegral.integral_interval_add_Ioi (integrand_integrable D x) hi
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, D.operator s (integrand D x t) :=
      (((D.operator s).restrictScalars ℝ).integral_comp_comm (integrand_integrable D x)).symm
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (s : ℝ) • integrand D x (t+s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integrand_shift D s x t ht.le
    _ = Real.exp (s : ℝ) • ∫ t : ℝ in Set.Ioi (s : ℝ), integrand D x t := by
      rw [integral_smul, integral_shift]
    _ = _ := by
      congr 1
      change (∫ t : ℝ in Set.Ioi (s : ℝ), integrand D x t) =
        (∫ t : ℝ in Set.Ioi 0, integrand D x t) - ∫ t : ℝ in 0..(s : ℝ), integrand D x t
      exact eq_sub_of_add_eq' ht

theorem right_derivative_range (x : State (hp := hp)) :
    HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal (resolvent D x))
      (resolvent D x-x) (Set.Ici 0) 0 := by
  have hc := integrand_continuous D x
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0 : ℝ) 0) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt
  have he := (Real.hasDerivAt_exp (0 : ℝ)).smul ((hasDerivAt_const 0 (resolvent D x)).sub hi)
  have hd : HasDerivAt (fun t : ℝ => Real.exp t •
      (resolvent D x - ∫ r : ℝ in 0..t, integrand D x r)) (resolvent D x-x) 0 := by
    simpa [Pi.smul_apply, Pi.sub_apply, integrand, D.zero, sub_eq_add_neg, add_comm] using he
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    simpa only [Real.coe_toNNReal t ht] using evolution_resolvent D t.toNNReal x
  · simp only [Real.toNNReal_zero, D.zero, Real.exp_zero, intervalIntegral.integral_same,
      sub_zero, one_smul]

/-- On its exact dense range domain, the constructed self-adjoint operator
is the negative right derivative of the actual OS evolution at zero. -/
theorem right_derivative (x : (hamiltonian D).domain) :
    HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal (x : State (hp := hp)))
      (-hamiltonian D x) (Set.Ici 0) 0 := by
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,rfl⟩ := hx
  change HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal (resolvent D y))
    (-hamiltonian D (rangePoint D y)) (Set.Ici 0) 0
  rw [apply_range, neg_sub]
  exact right_derivative_range D y

end
end UnifiedTheory.Clay.YangMills.OSLaplaceGenerator

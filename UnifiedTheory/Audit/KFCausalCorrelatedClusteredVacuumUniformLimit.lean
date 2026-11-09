/- A degree- and family-size-uniform lower response bound survives
cluster confluence in the source-free neutral-vacuum, zero-frequency
subclass. This is one-sided and does not cover arbitrary neutral profiles. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralVacuumResponse
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputResponseLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumUniformLimit
noncomputable section
open Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalCorrelatedClusteredPotentialGraphLimit (limitingOutput limiting_energy_identity)

def family {m : ℕ} (d : Fin m → ℕ) (z : Fin m → ℂ) : Family m :=
  ⟨d,fun _ => 0,fun _ => 1,z⟩

theorem exists_uniform_finite_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3) (δ : ℝ), 0 < δ →
      -((C+2)/ε)*finiteEnergy (family d z) ε h a (fun _ => 0) hε hh (original_strip ε h hε hb) ha δ ≤
        finiteResponse (family d z) ε h a (fun _ => 0) hε hh (original_strip ε h hε hb) ha δ := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalNeutralVacuumResponse.exists_uniform_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb δ hδ
  rw [finiteEnergy,finiteResponse,dif_pos hδ,dif_pos hδ]
  exact hbound (count (family d z)) ε h (lift (family d z) a) (widths (family d z) δ)
    (coefficients (family d z) δ) hε (fun j => ha (index (family d z) j).1) hh
    (widths_admissible (family d z) δ hδ.le) (original_strip ε h hε hb) hb

theorem exists_uniform_limit_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ), 0 < ε → h ≠ 0 → (∀ i, 0 < a i) → |h| ≤ Real.pi*ε/3 →
      -((C+2)/ε)*limitingEnergy (family d z) ε h a (fun _ => 0) ≤
        limitingResponse (family d z) ε h a (fun _ => 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_finite_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb
  apply le_of_tendsto_of_tendsto
    ((potentialEnergy_tendsto (family d z) ε h a (fun _ => 0) hε hh (original_strip ε h hε hb) ha).const_mul (-((C+2)/ε)))
    (potentialResponse_tendsto (family d z) ε h a (fun _ => 0) hε hh (original_strip ε h hε hb) ha)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hbound m d z ε h a hε hh ha hb δ hδ

theorem exists_uniform_physical_limit_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3),
      let V := limitingOutput (family d z) ε h a (fun _ => 0) hε hh (original_strip ε h hε hb) ha;
      -((C+2)/ε)*(‖V 0‖^2+‖V 1‖^2/2+‖V 2‖^2/4) ≤
        limitingResponse (family d z) ε h a (fun _ => 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_limit_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb
  dsimp only
  rw [← limiting_energy_identity (family d z) ε h a (fun _ => 0) hε hh (original_strip ε h hε hb) ha]
  exact hbound m d z ε h a hε hh ha hb

#print axioms exists_uniform_finite_response
#print axioms exists_uniform_limit_response
#print axioms exists_uniform_physical_limit_response
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumUniformLimit

/- A universal full strong-Hamiltonian response lower bound survives
cluster confluence for the source-free neutral vacuum at zero clock
frequency and unit couplings. Charged degrees, coefficients, clock widths
and time are unrestricted within the original strip. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongResponseLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumUniformLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredUniformStrongResponse
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredVacuumUniformLimit (family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredPhysicalCauchy (finiteOutput)
open KFCausalCorrelatedClusteredMomentumPotentialProfiles (finiteMomentumOutput)
open KFCausalCorrelatedClusteredStrongResponseLimit (fullEnergy fullResponse energy_tendsto response_tendsto)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit (inputHamiltonian momentumHamiltonian)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalPhysicalEnergyFactors (energyWeight)

theorem exists_uniform_finite_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3) (t δ : ℝ), 0 < δ →
      let f := family d z;
      let hb' := original_strip ε h hε hb;
      let U := finiteOutput f ε h a (fun _ => 0) hε hh hb' ha δ;
      let V := finiteMomentumOutput f ε h a (fun _ => 0) hε hh hb' ha δ;
      -((C+2)/ε)*(∑ j, ‖energyWeight 1 1 1 t j‖^2*‖U j‖^2) ≤
        ∑ j, ‖energyWeight 1 1 1 t j‖^2*((-2/h)*(inner ℂ (U j) (V j)).im) := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalSuperpositionEnergy.exists_uniform_full_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb t δ hδ
  dsimp only
  let f := family d z
  have ho (j : Fin 8) := KFCausalReciprocalNeutralVacuumResponse.output_reciprocal
    (count f) ε h (lift f a) (widths f δ) (coefficients f δ) hε (fun k => ha (index f k).1)
    hh (widths_admissible f δ hδ.le) (original_strip ε h hε hb) j
  have hm (j : Fin 8) := KFCausalReciprocalNeutralVacuumResponse.momentumOutput_reciprocal
    (count f) ε h (lift f a) (widths f δ) (coefficients f δ) hε (fun k => ha (index f k).1)
    hh (widths_admissible f δ hδ.le) (original_strip ε h hε hb) j
  have hi := hbound (count f) ε h (lift f a) (widths f δ) (coefficients f δ)
    hε (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) hb t
  simp only [finiteOutput,finiteMomentumOutput,dif_pos hδ]
  change -((C+2)/ε)*(∑ j, ‖energyWeight 1 1 1 t j‖^2*
    ‖KFCausalReciprocalNeutralSuperposition.output (count f) ε h (lift f a) (widths f δ)
      (fun _ => 0) (coefficients f δ) (fun _ => 0) (fun _ => 1) hε
      (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) (original_strip ε h hε hb) j‖^2) ≤ _
  simp only [ho]
  change -((C+2)/ε)*(∑ j, ‖energyWeight 1 1 1 t j‖^2*
    ‖KFCausalReciprocalSuperpositionFactors.output (count f) ε h (lift f a) (widths f δ)
      (coefficients f δ) hε (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le)
      (original_strip ε h hε hb) j‖^2) ≤
    ∑ j, ‖energyWeight 1 1 1 t j‖^2*((-2/h)*(inner ℂ
      (KFCausalReciprocalNeutralSuperposition.output (count f) ε h (lift f a) (widths f δ)
        (fun _ => 0) (coefficients f δ) (fun _ => 0) (fun _ => 1) hε
        (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) (original_strip ε h hε hb) j)
      (KFCausalReciprocalNeutralSuperposition.momentumOutput (count f) ε h (lift f a) (widths f δ)
        (fun _ => 0) (coefficients f δ) (fun _ => 0) (fun _ => 1) hε
        (fun k => ha (index f k).1) hh (widths_admissible f δ hδ.le) (original_strip ε h hε hb) j)).im)
  simpa only [ho,hm] using hi

theorem exists_uniform_full_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      -((C+2)/ε)*fullEnergy (family d z) ε h a (fun _ => 0) hε hh ha hb 1 1 1 t ≤
        fullResponse (family d z) ε h a (fun _ => 0) hε hh ha hb 1 1 1 t := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_finite_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb t
  apply le_of_tendsto_of_tendsto
    ((energy_tendsto (family d z) ε h a (fun _ => 0) hε hh ha hb 1 1 1 t).const_mul (-((C+2)/ε)))
    (response_tendsto (family d z) ε h a (fun _ => 0) hε hh ha hb 1 1 1 t)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hbound m d z ε h a hε hh ha hb t δ hδ

theorem exists_uniform_strong_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      let f := family d z;
      let ψ := KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a (fun _ => 0) hε hh ha;
      let b := KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a (fun _ => 0) hε hh ha;
      let Hψ := inputHamiltonian f ε h a (fun _ => 0) hε hh ha hb 1 1 1 t;
      -((C+2)/ε)*(inner ℂ Hψ ψ).re ≤ (-2/h)*(inner ℂ Hψ b).im := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_full_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb t
  have hi := hbound m d z ε h a hε hh ha hb t
  rwa [KFCausalCorrelatedClusteredStrongResponseLimit.energy_identity,
    KFCausalCorrelatedClusteredStrongResponseLimit.response_identity] at hi

theorem exists_uniform_hamiltonian_momentum_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      let f := family d z;
      let ψ := KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a (fun _ => 0) hε hh ha;
      let Hψ := inputHamiltonian f ε h a (fun _ => 0) hε hh ha hb 1 1 1 t;
      let Hb := momentumHamiltonian f ε h a (fun _ => 0) hε hh ha hb 1 1 1 t;
      -((C+2)/ε)*(inner ℂ Hψ ψ).re ≤ (-2/h)*(inner ℂ ψ Hb).im := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_full_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb t
  have hi := hbound m d z ε h a hε hh ha hb t
  rwa [KFCausalCorrelatedClusteredStrongResponseLimit.energy_identity,
    KFCausalCorrelatedClusteredStrongResponseLimit.hamiltonian_momentum_response_identity] at hi

#print axioms exists_uniform_finite_response
#print axioms exists_uniform_full_response
#print axioms exists_uniform_strong_response
#print axioms exists_uniform_hamiltonian_momentum_response
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredUniformStrongResponse

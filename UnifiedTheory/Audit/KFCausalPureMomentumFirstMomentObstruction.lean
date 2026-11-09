/- Finite Hamiltonian-form energy does not ensure a finite absolute
first moment of actual pure-clock momentum, even in the normalized
zero-charge sector. The closed graph theorem is applied to the actual
square-root absolute Fourier multiplier, using the unbounded packet
expectation derived from the actual momentum graph. -/
import UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
import UnifiedTheory.Audit.KFCausalProjectedMomentumExpectation
import UnifiedTheory.Audit.KFCausalPureMomentumDomainObstruction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPureMomentumFirstMomentObstruction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
  (zeroProjection zeroProjection_fixes zeroProjection_mem zeroSector)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (input inputLift momentumOutput)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (projectedEnergy)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected (structured input_fixed projected_input_embedding)
open UnifiedTheory.Audit.KFCausalProjectedMomentumExpectation (bounded_energy_unbounded_expectation)
open UnifiedTheory.Audit.KFCausalPureMomentumDomainObstruction
  (closed_operator_pullback_bound projected_form_norm)
open UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
  (momentumHalf momentumHalf_closed momentumHalf_domain momentum_expectation_bound spectralCoordinates)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hp : 0 < h)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hh" => hp.ne'
local notation "hstrip" => KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hstrip hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hstrip hh mass2 quartic vacuum t
local notation "energy" => energyOperator ε hε h hstrip hh mass2 quartic vacuum t
local notation "P" => KFCausalZeroChargeStructuredResponse.project ε h hε hh hb mass2 quartic vacuum t
local notation "Q" => momentumHalf ε hε h
local notation "S" p:arg => structured a h p ha
local notation "f" p:arg => input ε h hε hh (S p)
local notation "Bf" p:arg => momentumOutput ε h hε hh (S p)
local notation "u" p:arg => P (inputLift ε h hε hh hb (S p) mass2 quartic vacuum t)
local notation "E" p:arg => projectedEnergy ε h hε hh hb (S p) mass2 quartic vacuum t

include ha in
theorem exists_zero_charge_energy_state_outside_first_moment :
    ∃ ψ : Hilbert, ψ ∈ (energy).domain ∧ ψ ∈ zeroSector h hh ∧ ψ ∉ (Q).domain := by
  by_contra hn
  push_neg at hn
  let J : Full →L[ℂ] Hilbert := (zeroProjection h hh).comp embed
  have hd (v : Full) : J v ∈ (Q).domain := by
    apply hn
    · exact zeroProjection_mem_energy_domain ε hε h hstrip hh mass2 quartic vacuum t _
        ((energy_domain ε hε h hstrip hh mass2 quartic vacuum t _).mpr ⟨v,rfl⟩)
    · exact zeroProjection_mem h hh (embed v)
  obtain ⟨K,hK,hbound⟩ := closed_operator_pullback_bound J (Q) (momentumHalf_closed ε hε h) hd
  obtain ⟨n,_,_,hgraph,henergy,hm⟩ := bounded_energy_unbounded_expectation ε a h hε ha hh hb hp
    mass2 quartic vacuum t (K^2*(2+E 0))
  have hj : J (u (-(n:ℝ))) = f (-(n:ℝ)) := by
    change zeroProjection h hh (embed (u (-(n:ℝ)))) = _
    exact (congrArg (zeroProjection h hh)
      (projected_input_embedding ε a h hε ha hh hb (-(n:ℝ)) mass2 quartic vacuum t)).trans
      (zeroProjection_fixes h hh _ (input_fixed ε a h hε ha hh _))
  have hf : f (-(n:ℝ)) ∈ (Q).domain :=
    Eq.mp (congrArg (fun x : Hilbert => x ∈ (Q).domain) hj) (hd (u (-(n:ℝ))))
  let y : Hilbert := (Q) ⟨f (-(n:ℝ)),hf⟩
  have hqy : (J (u (-(n:ℝ))),y) ∈ (Q).graph :=
    Eq.mpr (congrArg (fun x : Hilbert => (x,y) ∈ (Q).graph) hj)
      ((Q).mem_graph ⟨f (-(n:ℝ)),hf⟩)
  have hy := hbound _ _ hqy
  have hsq : ‖y‖^2 ≤ K^2*(2+E 0) := by
    calc
      _ ≤ (K*‖u (-(n:ℝ))‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      _ = K^2*(2+E (-(n:ℝ))) :=
        (mul_pow K ‖u (-(n:ℝ))‖ 2).trans
          (congrArg (fun r : ℝ => K^2*r)
            (projected_form_norm ε a h hε ha hp hb mass2 quartic vacuum t (-(n:ℝ))))
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (le_refl (2:ℝ)) henergy) (sq_nonneg K)
  have he := momentum_expectation_bound ε hε h hh _ _ hgraph hf
  exact (not_lt_of_ge (he.trans hsq)) hm

include ha in
theorem exists_normalized_zero_charge_energy_state_outside_first_moment :
    ∃ ψ : Hilbert, ‖ψ‖ = 1 ∧ ψ ∈ (energy).domain ∧ ψ ∈ zeroSector h hh ∧ ψ ∉ (Q).domain := by
  obtain ⟨ψ,hf,hz,hnot⟩ := exists_zero_charge_energy_state_outside_first_moment
    ε a h hε ha hp hb mass2 quartic vacuum t
  have hne : ψ ≠ 0 := by
    intro he
    apply hnot
    exact Eq.mpr (congrArg (fun x : Hilbert => x ∈ (Q).domain) he) (Q).domain.zero_mem
  have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  let g : Hilbert := (‖ψ‖⁻¹:ℝ) • ψ
  have hback : (‖ψ‖:ℝ) • g = ψ := by
    dsimp only [g]
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  refine ⟨g,?_,((energy).domain.restrictScalars ℝ).smul_mem _ hf,
    ((zeroSector h hh).restrictScalars ℝ).smul_mem _ hz,?_⟩
  · simp only [g,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn]
  · intro hg
    apply hnot
    exact Eq.mp (congrArg (fun x : Hilbert => x ∈ (Q).domain) hback)
      (((Q).domain.restrictScalars ℝ).smul_mem _ hg)

include ha in
theorem exists_normalized_infinite_absolute_moment :
    ∃ ψ : Hilbert, ‖ψ‖ = 1 ∧ ψ ∈ (energy).domain ∧ ψ ∈ zeroSector h hh ∧
      ¬ Integrable (fun k : KFCausalEuclideanConfiguration.Space =>
        |KFCausalClockFloorFourierMultiplier.symbol h k| *‖(spectralCoordinates ε hε ψ) k‖^2) := by
  obtain ⟨ψ,hn,he,hz,hnot⟩ := exists_normalized_zero_charge_energy_state_outside_first_moment
    ε a h hε ha hp hb mass2 quartic vacuum t
  exact ⟨ψ,hn,he,hz,fun hi => hnot ((momentumHalf_domain ε hε h ψ).mpr hi)⟩

#print axioms exists_zero_charge_energy_state_outside_first_moment
#print axioms exists_normalized_zero_charge_energy_state_outside_first_moment
#print axioms exists_normalized_infinite_absolute_moment
end
end UnifiedTheory.Audit.KFCausalPureMomentumFirstMomentObstruction

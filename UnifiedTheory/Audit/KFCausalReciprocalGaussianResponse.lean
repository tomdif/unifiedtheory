/- Response decomposition for actual reciprocal states and momenta.
Clock and kinetic contributions obey the established operator inequalities. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianHamiltonian
import UnifiedTheory.Audit.KFCausalPolynomialClockComposition
import UnifiedTheory.Audit.KFCausalChargedPairHamiltonianResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianResponse
noncomputable section
open KFCausalReciprocalGaussianMomentum
open KFCausalReciprocalGaussianHamiltonian
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight energyWeight_norm_square)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalReciprocalGaussianDomain
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

private theorem physical_sum (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (r : Fin 8 → ℝ) :
    (∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*r i) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*((r 3+r 4)/2+mass2/2*r 5+quartic/4*r 6+vacuum*r 7) := by
  simp_rw [energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "f" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)
local notation "Bf" => momentum ε a h w hε ha hh hw
local notation "u" => output ε a h w hε ha hh hw hb
local notation "v" => momentumOutput ε a h w hε ha hh hw hb

def factorRate (j : Fin 8) : ℝ := (-2/h)*(inner ℂ (u j) (v j)).im
def factorEnergy (j : Fin 8) : ℝ := ‖u j‖^2
local notation "E" => factorEnergy ε a h w hε ha hh hw hb
local notation "R" => factorRate ε a h w hε ha hh hw hb

theorem clock_output_domain : u 0 ∈ (pureMomentum ε hε h).domain := by
  let t := Real.log w/2
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hw) (by norm_num)
  have hg := KFCausalPolynomialClockComposition.sourced_composition_graph ε a
    (groundWidth h) (baseWidth h t) h hε ha (groundWidth_positive h hh)
    (baseWidth_positive h hh t) (baseWidth_bound h hh t ht) hh hb 1 0 0
  have hx := (pureMomentum ε hε h).graph.smul_mem (Real.exp (-t/2):ℂ)
    (pure_graph_transport ε hε h hh (-t) _ _ hg)
  have hd := LinearPMap.mem_domain_of_mem_graph hx
  simpa [output,KFCausalReciprocalSqueezeEnergy.factorScale,KFCausalReciprocalSqueezeEnergy.degree,
    KFCausalClockFloorSourcedCommonDomain.factorOutput,t] using hd

theorem clock_response : R 0 = -KFCausalClockFloorPureClockKineticResponse.response ε hε (u 0) :=
  KFCausalClockFloorPureClockClockResponse.weak_response ε hε h hh f (u 0) Bf (v 0) _
    (output_graph ε a h w hε ha hh hw hb 0)
    (momentum_graph ε a h w hε ha hh hw)
    (momentumOutput_graph ε a h w hε ha hh hw hb 0)
    ((pureMomentum ε hε h).mem_graph ⟨u 0,clock_output_domain ε a h w hε ha hh hw hb⟩)

theorem clock_energy_bounds : -(1/(4*ε))*E 0 ≤ R 0 ∧ R 0 ≤ 0 := by
  rw [clock_response]
  exact KFCausalClockFloorPureClockClockResponse.response_bounds ε hε f (u 0)

theorem kinetic_response (i : Fin 4) : R (kineticIndex i) =
    KFCausalClockFloorPureClockKineticResponse.response ε hε (u (kineticIndex i)) := by
  apply KFCausalClockFloorPureClockKineticResponse.weak_response ε hε h hh (modelDirections i)
    f _ Bf _
  · have hg := output_graph ε a h w hε ha hh hw hb (kineticIndex i)
    fin_cases i <;> exact hg
  · exact momentum_graph ε a h w hε ha hh hw
  · have hg := momentumOutput_graph ε a h w hε ha hh hw hb (kineticIndex i)
    fin_cases i <;> exact hg

theorem kinetic_bounds (i : Fin 4) : 0 ≤ R (kineticIndex i) ∧
    R (kineticIndex i) ≤ (1/(4*ε))*E (kineticIndex i) := by
  rw [kinetic_response]
  exact KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε (u (kineticIndex i))

theorem physical_energy (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullEnergy ε a h w hε ha hh hw hb mass2 quartic vacuum t =
      (E 0+E 1+E 2)/2+Real.exp (2*t)*((E 3+E 4)/2+mass2/2*E 5+quartic/4*E 6+vacuum*E 7) := by
  rw [energy_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv E

theorem physical_response (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    fullResponse ε a h w hε ha hh hw hb mass2 quartic vacuum t =
      (R 0+R 1+R 2)/2+Real.exp (2*t)*((R 3+R 4)/2+mass2/2*R 5+quartic/4*R 6+vacuum*R 7) := by
  rw [response_decomposition]
  exact physical_sum mass2 quartic vacuum t hm hq hv R

def clockKineticEnergy (t : ℝ) : ℝ :=
  (E 0+E 1+E 2)/2+Real.exp (2*t)*(E 3+E 4)/2
def clockKineticResponse (t : ℝ) : ℝ :=
  (R 0+R 1+R 2)/2+Real.exp (2*t)*(R 3+R 4)/2
def potentialEnergy : ℝ := E 7+E 5/2+E 6/4
def potentialResponse : ℝ := R 7+R 5/2+R 6/4

theorem clockKinetic_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy ε a h w hε ha hh hw hb t ≤
      clockKineticResponse ε a h w hε ha hh hw hb t := by
  have h0 := (clock_energy_bounds ε a h w hε ha hh hw hb).1
  have h1 := (kinetic_bounds ε a h w hε ha hh hw hb 0).1
  have h2 := (kinetic_bounds ε a h w hε ha hh hw hb 1).1
  have h3 := (kinetic_bounds ε a h w hε ha hh hw hb 2).1
  have h4 := (kinetic_bounds ε a h w hε ha hh hw hb 3).1
  change 0 ≤ R 1 at h1
  change 0 ≤ R 2 at h2
  change 0 ≤ R 3 at h3
  change 0 ≤ R 4 at h4
  have hc : 0 ≤ 1/(4*ε) := by positivity
  have he : E 0/2 ≤ clockKineticEnergy ε a h w hε ha hh hw hb t := by
    have hs : 0 ≤ (E 1+E 2)/2 := by unfold factorEnergy; positivity
    have hg : 0 ≤ Real.exp (2*t)*(E 3+E 4)/2 := by unfold factorEnergy; positivity
    unfold clockKineticEnergy
    linarith
  have hr : -(1/(4*ε))*(E 0/2) ≤ clockKineticResponse ε a h w hε ha hh hw hb t := by
    have hg := mul_nonneg (Real.exp_pos (2*t)).le (add_nonneg h3 h4)
    unfold clockKineticResponse
    linarith
  exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hc)).trans hr

theorem unit_full_energy (t : ℝ) :
    fullEnergy ε a h w hε ha hh hw hb 1 1 1 t =
      clockKineticEnergy ε a h w hε ha hh hw hb t+
        Real.exp (2*t)*potentialEnergy ε a h w hε ha hh hw hb := by
  rw [physical_energy ε a h w hε ha hh hw hb 1 1 1 t (by norm_num) (by norm_num) (by norm_num)]
  unfold clockKineticEnergy potentialEnergy
  ring

theorem unit_full_response (t : ℝ) :
    fullResponse ε a h w hε ha hh hw hb 1 1 1 t =
      clockKineticResponse ε a h w hε ha hh hw hb t+
        Real.exp (2*t)*potentialResponse ε a h w hε ha hh hw hb := by
  rw [physical_response ε a h w hε ha hh hw hb 1 1 1 t (by norm_num) (by norm_num) (by norm_num)]
  unfold clockKineticResponse potentialResponse
  ring

theorem fullResponse_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy ε a h w hε ha hh hw hb t+
      Real.exp (2*t)*potentialResponse ε a h w hε ha hh hw hb ≤
        fullResponse ε a h w hε ha hh hw hb 1 1 1 t := by
  rw [unit_full_response]
  exact add_le_add (clockKinetic_lower ε a h w hε ha hh hw hb t) le_rfl

#print axioms clock_output_domain
#print axioms clock_response
#print axioms clock_energy_bounds
#print axioms kinetic_response
#print axioms kinetic_bounds
#print axioms physical_energy
#print axioms physical_response
#print axioms clockKinetic_lower
#print axioms unit_full_energy
#print axioms unit_full_response
#print axioms fullResponse_lower
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianResponse

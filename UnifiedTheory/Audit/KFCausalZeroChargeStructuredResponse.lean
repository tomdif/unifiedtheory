/- Actual fixed-time responses after projection to the physical zero-charge
sector. Projection averages output vectors before their pairing. The energy
and signed response split exactly into zero-charge and complementary parts;
energy contraction alone supplies no sign for either signed response. -/
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection
import UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
import UnifiedTheory.Audit.KFCausalAveragedProjectionPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 50000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
  (zeroProjection zeroProjection_idempotent zeroSector standingCharge)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group action_full_period)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean (mean mean_const)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState input momentumOutput inputLift momentumLift momentum_graph)

private theorem inner_split {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (a b pa pb : K) (h1 : inner ℂ pa b = inner ℂ pa pb)
    (h2 : inner ℂ a pb = inner ℂ pa pb) :
    inner ℂ a b = inner ℂ pa pb+inner ℂ (a-pa) (b-pb) := by
  simp only [inner_sub_left,inner_sub_right,h1,h2]
  abel

private theorem lp_pairing_split {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (a b : Lp K 2 angleMeasure) :
    inner ℂ a b =
      inner ℂ (Lp.const 2 angleMeasure (mean angleMeasure a)) (Lp.const 2 angleMeasure (mean angleMeasure b))+
      inner ℂ (a-Lp.const 2 angleMeasure (mean angleMeasure a))
        (b-Lp.const 2 angleMeasure (mean angleMeasure b)) := by
  let C : K →L[ℂ] Lp K 2 angleMeasure := Lp.constL 2 angleMeasure ℂ
  have h0 : inner ℂ (C (mean angleMeasure a)) (C (mean angleMeasure b)) =
      inner ℂ (mean angleMeasure a) (mean angleMeasure b) :=
    (C.adjoint_inner_right _ _).symm.trans
      (congrArg (inner ℂ (mean angleMeasure a)) (mean_const angleMeasure _))
  exact inner_split a b _ _ ((C.adjoint_inner_right _ _).symm.trans h0.symm)
    ((C.adjoint_inner_left _ _).symm.trans h0.symm)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "D" => KFCausalClockFloorFormHamiltonian.formData ε hε h hp mass2 quartic vacuum t
local notation "Target" => KFCausalFiniteJointGraph.Output (Fin 8) Hilbert
local notation "Base" => KFCausalClosedGraphForm.FormSpace D
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "A" => KFCausalClosedGraphForm.energyOutput D
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
def output : Full →L[ℂ] Lp Target 2 angleMeasure :=
  energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "out" => output ε h hε hh hb mass2 quartic vacuum t
def project (u : Full) : Full := projectedForm ε hε h hp hh mass2 quartic vacuum t u
local notation "P" => project ε h hε hh hb mass2 quartic vacuum t

theorem projected_idempotent (u : Full) : P (P u) = P u := by
  apply embedding_injective ε hε h hp hh mass2 quartic vacuum t
  simp only [project,projected_embedding,zeroProjection_idempotent]

theorem projected_output (u : Full) :
    out (P u) = Lp.const 2 angleMeasure (mean angleMeasure (out u)) := by
  have ht := KFCausalAveragedProjectionPairing.project_output_eq_const_mean
    (H := Hilbert) (E := Base) (K := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert)
    (group h hh) (2*Real.pi) (by positivity) (action_full_period h hh) J A
  exact ht u

theorem projected_pairing (u v : Full) :
    inner ℂ (out (P u)) (out (P v)) =
      inner ℂ (mean angleMeasure (out u)) (mean angleMeasure (out v)) := by
  have hc (x y : Target) : inner ℂ (Lp.const 2 angleMeasure x) (Lp.const 2 angleMeasure y) = inner ℂ x y := by
    calc
      _ = inner ℂ x (mean angleMeasure (Lp.const 2 angleMeasure y)) :=
        ((Lp.constL 2 angleMeasure ℂ : Target →L[ℂ] Lp Target 2 angleMeasure).adjoint_inner_right _ _).symm
      _ = _ := congrArg (inner ℂ x) (mean_const angleMeasure y)
  exact (congrArg₂ (inner ℂ)
    (projected_output ε h hε hh hb mass2 quartic vacuum t u)
    (projected_output ε h hε hh hb mass2 quartic vacuum t v)).trans (hc _ _)

theorem pairing_split (u v : Full) :
    inner ℂ (out u) (out v) = inner ℂ (out (P u)) (out (P v))+
      inner ℂ (out (u-P u)) (out (v-P v)) := by
  have hu := projected_output ε h hε hh hb mass2 quartic vacuum t u
  have hv := projected_output ε h hε hh hb mass2 quartic vacuum t v
  have su := (out).map_sub u (P u)
  have sv := (out).map_sub v (P v)
  have hdu : out (u-P u) = out u-Lp.const 2 angleMeasure (mean angleMeasure (out u)) :=
    su.trans (congrArg (fun z => out u-z) hu)
  have hdv : out (v-P v) = out v-Lp.const 2 angleMeasure (mean angleMeasure (out v)) :=
    sv.trans (congrArg (fun z => out v-z) hv)
  exact (lp_pairing_split (out u) (out v)).trans
    (congrArg₂ (fun x y : ℂ => x+y) (congrArg₂ (inner ℂ) hu hv)
      (congrArg₂ (inner ℂ) hdu hdv)).symm

theorem energy_split (u : Full) : ‖out u‖^2 = ‖out (P u)‖^2+‖out (u-P u)‖^2 := by
  have he := congrArg Complex.re (pairing_split ε h hε hh hb mass2 quartic vacuum t u u)
  have hr (x : Lp Target 2 angleMeasure) : (inner ℂ x x).re = ‖x‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Complex.add_re,hr] using he

theorem response_split (u v : Full) :
    (-2/h)*(inner ℂ (out u) (out v)).im =
      (-2/h)*(inner ℂ (out (P u)) (out (P v))).im+
      (-2/h)*(inner ℂ (out (u-P u)) (out (v-P v))).im := by
  exact (congrArg (fun z : ℂ => (-2/h)*z.im)
    (pairing_split ε h hε hh hb mass2 quartic vacuum t u v)).trans (mul_add _ _ _)

variable (S : StructuredState)
local notation "u" => inputLift ε h hε hh hb S mass2 quartic vacuum t
local notation "v" => momentumLift ε h hε hh hb S mass2 quartic vacuum t

theorem actual_projected_graph : (embed (P u),embed (P v)) ∈ (pureMomentum ε hε h).graph :=
  KFCausalPureClockZeroProjection.projected_graph ε hε h hh _ _ (momentum_graph ε h hε hh S)

theorem actual_zero_charge :
    (embed (P u),0) ∈ (standingCharge h hh).graph ∧
      (embed (P v),0) ∈ (standingCharge h hh).graph :=
  ⟨projected_charge_zero ε hε h hp hh mass2 quartic vacuum t u,
    projected_charge_zero ε hε h hp hh mass2 quartic vacuum t v⟩

theorem actual_projected_domains :
    zeroProjection h hh (input ε h hε hh S) ∈
      (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain ∧
    zeroProjection h hh (momentumOutput ε h hε hh S) ∈
      (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain :=
  ⟨(energy_domain ε hε h hp hh mass2 quartic vacuum t _).mpr ⟨P u,rfl⟩,
    (energy_domain ε hε h hp hh mass2 quartic vacuum t _).mpr ⟨P v,rfl⟩⟩

theorem actual_projected_response :
    (-2/h)*(inner ℂ (out (P u)) (out (P v))).im =
      (-2/h)*(inner ℂ (mean angleMeasure (out u)) (mean angleMeasure (out v))).im := by
  exact congrArg (fun z : ℂ => (-2/h)*z.im)
    (projected_pairing ε h hε hh hb mass2 quartic vacuum t u v)

#print axioms projected_idempotent
#print axioms projected_output
#print axioms projected_pairing
#print axioms pairing_split
#print axioms energy_split
#print axioms response_split
#print axioms actual_projected_graph
#print axioms actual_zero_charge
#print axioms actual_projected_domains
#print axioms actual_projected_response
end
end UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse

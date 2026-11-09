/- Constraint preservation for the actual unbounded averaged evolution.
Closedness transfers zero charge through the constructed strong limits;
proved zero-sector energy-domain density extends this to every zero-sector
L2 state. Reversibility then gives commutation with the orthogonal projection. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionContinuity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDynamicsProjection
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakNormConservation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedDynamicsProjection (dynamics_zero_sector)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)

local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "P" => zeroProjection hbar hh
local notation "Z" => zeroSector hbar hh
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε hbar hh hbound mass2 quartic vacuum 0

theorem weak_trajectory_zero_sector (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) (hw : J w ∈ Z) :
    J (V.formState t) ∈ Z := by
  have hl := cutoff_subsequence_strong_convergence ε hε hbar hh hbound mass2 quartic vacuum s w V t
  exact (zeroSector_closed hbar hh).mem_of_tendsto hl (Eventually.of_forall fun n =>
    dynamics_zero_sector ε hε hbar hh hbound mass2 quartic vacuum
      (cutoff (V.subsequence n)) (cutoff_pos (V.subsequence n)) s t (J w) hw)

theorem formFlow_zero_sector (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (hw : J w ∈ Z) :
    J (formFlow ε hε hbar hh hbound mass2 quartic vacuum s t w) ∈ Z :=
  weak_trajectory_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t w
    (weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) hw

theorem evolution_form_zero_sector (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (hw : J w ∈ Z) :
    U s t (J w) ∈ Z := by
  have he := evolution_embedding ε hε hbar hh hbound mass2 quartic vacuum s t w
  exact (congrArg (fun f : Hilbert => f ∈ Z) he).mpr
    (formFlow_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t w hw)

theorem evolution_zero_sector (s t : ℝ) (f : Hilbert) (hf : f ∈ Z) : U s t f ∈ Z := by
  let S : Submodule ℂ Hilbert := (Z).comap (U s t).toLinearEquiv.toLinearMap
  have hS : IsClosed (S : Set Hilbert) := (zeroSector_closed hbar hh).preimage (U s t).continuous
  have hle : Z ⊓ (D).operator.domain ≤ S := by
    intro g hg
    let w := KFCausalClosedGraphForm.graphVector D ⟨g,hg.2⟩
    have hj : J w = g := KFCausalClosedGraphForm.graphVector_embedding D ⟨g,hg.2⟩
    have hw : J w ∈ Z := (congrArg (fun x : Hilbert => x ∈ Z) hj).mpr hg.1
    have hu := evolution_form_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t w hw
    exact (congrArg (fun x : Hilbert => U s t x ∈ Z) hj).mp hu
  have hd : (Z ⊓ (D).operator.domain).topologicalClosure = Z :=
    KFCausalClockFloorAveragedDensity.zero_energy_domain_closure ε hbar hε hh hbound mass2 quartic vacuum 0
  have hc := Submodule.topologicalClosure_minimal (Z ⊓ (D).operator.domain) hle hS
  exact (hd.symm.le.trans hc) hf

theorem evolution_zeroProjection (s t : ℝ) (f : Hilbert) : U s t (P f) = P (U s t f) := by
  let A : Hilbert →L[ℂ] Hilbert := U s t
  let B : Hilbert →L[ℂ] Hilbert := U t s
  have hp : star P = P := zeroProjection_selfAdjoint hbar hh
  have hB : star B = A := evolution_adjoint ε hε hbar hh hbound mass2 quartic vacuum t s
  have hforward : P*(A*P) = A*P := by
    apply ContinuousLinearMap.ext
    intro g
    exact zeroProjection_fixes hbar hh _
      (evolution_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t (P g) (zeroProjection_mem hbar hh g))
  have hback : P*B*P = B*P := by
    apply ContinuousLinearMap.ext
    intro g
    exact zeroProjection_fixes hbar hh _
      (evolution_zero_sector ε hε hbar hh hbound mass2 quartic vacuum t s (P g) (zeroProjection_mem hbar hh g))
  have hs := congrArg star hback
  simp only [star_mul,hp,hB,mul_assoc] at hs
  have hc : P*A = A*P := hs.symm.trans hforward
  exact (congrArg (fun T : Hilbert →L[ℂ] Hilbert => T f) hc).symm

theorem evolution_charge_zero (s t : ℝ) (f : Hilbert) (hf : f ∈ Z) :
    (U s t f,0) ∈ (standingCharge hbar hh).graph :=
  (standingCharge_zero_iff hbar hh _).mpr
    (evolution_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t f hf)

def zeroEvolution (s t : ℝ) : Z ≃ₗᵢ[ℂ] Z where
  toLinearEquiv := {
    toFun f := ⟨U s t (f:Hilbert),evolution_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t f f.property⟩
    invFun f := ⟨U t s (f:Hilbert),evolution_zero_sector ε hε hbar hh hbound mass2 quartic vacuum t s f f.property⟩
    map_add' f g := Subtype.ext ((U s t).map_add (f:Hilbert) (g:Hilbert))
    map_smul' c f := Subtype.ext ((U s t).map_smul c (f:Hilbert))
    left_inv f := Subtype.ext (congrArg (fun T : Hilbert →L[ℂ] Hilbert => T (f:Hilbert))
      (evolution_reverse ε hε hbar hh hbound mass2 quartic vacuum s t))
    right_inv f := Subtype.ext (congrArg (fun T : Hilbert →L[ℂ] Hilbert => T (f:Hilbert))
      (evolution_reverse ε hε hbar hh hbound mass2 quartic vacuum t s)) }
  norm_map' f := evolution_norm ε hε hbar hh hbound mass2 quartic vacuum s t (f:Hilbert)

theorem zeroEvolution_apply (s t : ℝ) (f : Z) :
    (zeroEvolution ε hε hbar hh hbound mass2 quartic vacuum s t f : Hilbert) = U s t (f:Hilbert) := rfl

#print axioms weak_trajectory_zero_sector
#print axioms formFlow_zero_sector
#print axioms evolution_form_zero_sector
#print axioms evolution_zero_sector
#print axioms evolution_zeroProjection
#print axioms evolution_charge_zero
#print axioms zeroEvolution
#print axioms zeroEvolution_apply

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection

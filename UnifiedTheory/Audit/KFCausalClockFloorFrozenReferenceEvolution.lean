/- Frozen full-Hamiltonian evolution on the common reference form.
The reference-space norm need not be conserved: the exact conserved
energy is the full form at the frozen physical time. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenFormEvolution
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
import UnifiedTheory.Audit.KFCausalFormCrossDerivative

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenReferenceEvolution
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k r η : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "W" => FormSpace ε hε h hne hb m g k r
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "Jr" => embedding ε hε h hne hb m g k r
local notation "Br" => energyOutput ε hε h hne hb m g k r
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "Q" => referenceFormOperator ε hε h hne hb m g k r
local notation "L" => formTransfer ε hε h hne hb m g k 0 r
local notation "M" => formTransfer ε hε h hne hb m g k r 0
local notation "F" => KFCausalClockFloorFrozenFormEvolution.evolution ε hε h hne hb m g k r η
local notation "U" => KFCausalClockFloorFrozenEvolution.evolution ε hε h hne hb m g k r η

def evolution (t : ℝ) : V →L[ℂ] V := (M).comp ((F t : W →L[ℂ] W).comp L)
local notation "E" => evolution ε hε h hne hb m g k r η

theorem transfer_evolution (t : ℝ) (v : V) : L (E t v)=F t (L v) :=
  transfer_inverse ε hε h hne hb m g k r 0 (F t (L v))

theorem evolution_embedding (t : ℝ) (v : V) : J (E t v)=U t (J v) := by
  change J (M (F t (L v)))=_
  exact (transfer_embedding ε hε h hne hb m g k r 0 (F t (L v))).trans
    ((KFCausalClockFloorFrozenFormEvolution.evolution_embedding ε hε h hne hb m g k r η t (L v)).trans
      (congrArg (U t) (transfer_embedding ε hε h hne hb m g k 0 r v)))

theorem evolution_initial (v : V) : E 0 v=v := by
  apply embedding_injective ε hε h hne hb m g k 0
  exact (evolution_embedding ε hε h hne hb m g k r η 0 v).trans
    (KFCausalClockFloorFrozenEvolution.evolution_initial ε hε h hne hb m g k r η (J v))

theorem evolution_compose (s t : ℝ) (v : V) : E (s+t) v=E t (E s v) := by
  apply embedding_injective ε hε h hne hb m g k 0
  exact (evolution_embedding ε hε h hne hb m g k r η (s+t) v).trans
    ((KFCausalClockFloorFrozenEvolution.evolution_compose ε hε h hne hb m g k r η s t (J v)).trans
      ((congrArg (U t) (evolution_embedding ε hε h hne hb m g k r η s v).symm).trans
        (evolution_embedding ε hε h hne hb m g k r η t (E s v)).symm))

theorem evolution_continuous (v : V) : Continuous (fun t => E t v) :=
  (M).continuous.comp (KFCausalClockFloorFrozenFormEvolution.evolution_continuous ε hε h hne hb m g k r η (L v))

theorem physical_norm (t : ℝ) (v : V) : ‖J (E t v)‖=‖J v‖ := by
  rw [evolution_embedding,(U t).norm_map]

theorem energy_preserved (t : ℝ) (v : V) :
    timeEnergy ε hε h hne hb m g k r (E t v)=timeEnergy ε hε h hne hb m g k r v := by
  have hn := KFCausalClockFloorFrozenFormEvolution.energy_preserved ε hε h hne hb m g k r η t (L v)
  have ht := transfer_evolution ε hε h hne hb m g k r η t v
  exact (timeEnergy_actual ε hε h hne hb m g k r (E t v)).symm.trans
    ((congrArg (fun x : W => ‖Br x‖^2) ht).trans
      ((congrArg (fun a : ℝ => a^2) hn).trans (timeEnergy_actual ε hε h hne hb m g k r v)))

theorem weak_schrodinger (v z : V) (t : ℝ) :
    HasDerivAt (fun u => inner ℂ (U u (J v)) (J z))
      ((Complex.I*(η:ℂ))*inner ℂ (E t v) (Q z)) t := by
  have hd := KFCausalClockFloorFrozenFormEvolution.weak_schrodinger ε hε h hne hb m g k r η (L v) (L z) t
  change HasDerivAt (fun u => inner ℂ (U u (Jr (L v))) (Jr (L z)))
    ((Complex.I*(η:ℂ))*inner ℂ (Br (F t (L v))) (Br (L z))) t at hd
  have hp : inner ℂ (Br (F t (L v))) (Br (L z))=inner ℂ (E t v) (Q z) :=
    (congrArg (fun x : W => inner ℂ (Br x) (Br (L z)))
      (transfer_evolution ε hε h hne hb m g k r η t v).symm).trans
        (referenceForm_represents_closed_form ε hε h hne hb m g k r (E t v) z).symm
  have hf : (fun u => inner ℂ (U u (Jr (L v))) (Jr (L z)))=
      (fun u => inner ℂ (U u (J v)) (J z)) := by
    funext u
    exact congrArg₂ (fun x y : Hilbert => inner ℂ (U u x) y)
      (transfer_embedding ε hε h hne hb m g k 0 r v)
      (transfer_embedding ε hε h hne hb m g k 0 r z)
  exact (congrArg₂ (fun f d => HasDerivAt f d t) hf
    (congrArg (fun a : ℂ => (Complex.I*(η:ℂ))*a) hp)).mp hd

theorem mass_derivative (v : V) (t : ℝ) :
    HasDerivAt (fun a => KFCausalBoundedFormCurve.gram J (E a v))
      ((-Complex.I*(η:ℂ)) • Q (E t v)) t := by
  apply KFCausalFormCrossDerivative.mass_derivative J Q
    (KFCausalShiftedForm.formOperator_inner_symm A B r) η (fun a => E a v)
    (evolution_continuous ε hε h hne hb m g k r η v) _ t
  intro a z
  have hf : (fun b => inner ℂ (J (E b v)) (J z))=(fun b => inner ℂ (U b (J v)) (J z)) := by
    funext b
    exact congrArg (fun x : Hilbert => inner ℂ x (J z))
      (evolution_embedding ε hε h hne hb m g k r η b v)
  exact (congrArg (fun f => HasDerivAt f ((Complex.I*(η:ℂ))*inner ℂ (E a v) (Q z)) a) hf).mpr
    (weak_schrodinger ε hε h hne hb m g k r η v z a)

#print axioms transfer_evolution
#print axioms evolution_embedding
#print axioms evolution_initial
#print axioms evolution_compose
#print axioms evolution_continuous
#print axioms physical_norm
#print axioms energy_preserved
#print axioms weak_schrodinger
#print axioms mass_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenReferenceEvolution

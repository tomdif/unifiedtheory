/- Direct application of the completed-form perturbation theorem to the
actual eight-factor interacting Hamiltonian. The coupling uses the mean of
an actual energy-output component. All original interacting form terms are
retained. This is a configuration-space Hamiltonian theorem, not a proof of
the full bosonic Pauli--Fierz or local relativistic field construction. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
import UnifiedTheory.Audit.KFCausalLinearFieldFormPerturbation

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingComponentPerturbation
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem form_pairing_rewrite {X K : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (D : KFCausalClosedGraphForm.Data X K)
    (u v : KFCausalClosedGraphForm.FormSpace D) (z w : ℂ) :
    (inner ℂ u v - inner ℂ (KFCausalClosedGraphForm.embedding D u)
      (KFCausalClosedGraphForm.embedding D v) + z = w) ↔
    (inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
      (KFCausalClosedGraphForm.energyOutput D v) + z = w) := by
  rw [KFCausalClosedGraphForm.form_inner_identity D u v, add_sub_cancel_left]

abbrev EnergySpace := Lp (Output (Fin 8) Hilbert) 2 angleMeasure

def componentMean (i : Fin 8) : EnergySpace →L[ℂ] Hilbert :=
  (PiLp.proj 2 (fun _ : Fin 8 => Hilbert) i).comp
    (KFCausalProbabilityL2Mean.mean angleMeasure)

theorem componentMean_contracts (i : Fin 8) (v : EnergySpace) :
    ‖componentMean i v‖ ≤ ‖v‖ :=
  (PiLp.norm_apply_le _ _).trans (KFCausalProbabilityL2Mean.mean_norm_le angleMeasure v)

theorem componentMean_integral (i : Fin 8) (v : EnergySpace) :
    componentMean i v = (∫ θ, v θ ∂angleMeasure) i := by
  change (KFCausalProbabilityL2Mean.mean angleMeasure v) i = _
  rw [KFCausalProbabilityL2Mean.mean_integral]

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hb : |hbar| ≤ 2*Real.pi*ε/3) (m q κ t : ℝ)
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε hbar hh hb m q κ t
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "E" => KFCausalClosedGraphForm.energyOutput D
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε hbar hh hb m q κ t

abbrev FormSpace := KFCausalClosedGraphForm.FormSpace D

def component (i : Fin 8) : FormSpace ε hε hbar hh hb m q κ t →L[ℂ] Hilbert :=
  (componentMean i).comp E

theorem component_bound (i : Fin 8) (u : FormSpace ε hε hbar hh hb m q κ t) :
    ‖component ε hε hbar hh hb m q κ t i u‖^2 ≤ ‖u‖^2 - ‖J u‖^2 := by
  have hc := componentMean_contracts i (E u)
  have he := KFCausalClosedGraphForm.form_norm_identity D u
  change ‖componentMean i (E u)‖^2 ≤ _
  nlinarith [norm_nonneg (componentMean i (E u)), norm_nonneg (E u)]

def hamiltonian (i : Fin 8) (g : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  KFCausalLinearFieldFormPerturbation.hamiltonian J
    (component ε hε hbar hh hb m q κ t i) g
    (component_bound ε hε hbar hh hb m q κ t i)
    (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)

theorem hamiltonian_selfAdjoint (i : Fin 8) (g : ℝ) :
    IsSelfAdjoint (hamiltonian ε hε hbar hh hb m q κ t i g) :=
  KFCausalLinearFieldFormPerturbation.hamiltonian_selfAdjoint _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
theorem variational_graph (i : Fin 8) (g : ℝ)
    (u : FormSpace ε hε hbar hh hb m q κ t) (y : Hilbert) :
    (J u,y) ∈ (hamiltonian ε hε hbar hh hb m q κ t i g).graph ↔
      ∀ v : FormSpace ε hε hbar hh hb m q κ t,
        inner ℂ (E u) (E v) + (g : ℂ)*
          (inner ℂ (J u) (component ε hε hbar hh hb m q κ t i v) +
            inner ℂ (component ε hε hbar hh hb m q κ t i u) (J v)) = inner ℂ y (J v) := by
  refine (KFCausalLinearFieldFormPerturbation.variational_graph J
    (component ε hε hbar hh hb m q κ t i) g
    (component_bound ε hε hbar hh hb m q κ t i)
    (KFCausalClosedGraphForm.embedding_injective D)
    (KFCausalClosedGraphForm.embedding_dense D) u y).trans ?_
  apply forall_congr'
  intro v
  exact form_pairing_rewrite D u v _ _

theorem lower_bound (i : Fin 8) (g : ℝ)
    (u : FormSpace ε hε hbar hh hb m q κ t) (y : Hilbert)
    (hg : (J u,y) ∈ (hamiltonian ε hε hbar hh hb m q κ t i g).graph) :
    -(2*g^2)*‖J u‖^2 ≤ (inner ℂ y (J u)).re :=
  KFCausalLinearFieldFormPerturbation.lower_bound _ _ _ _ _ _
    (KFCausalClosedGraphForm.embedding_contraction D) u y hg

private theorem selfadjoint_eq_of_le (A B : Hilbert →ₗ.[ℂ] Hilbert)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hle : A ≤ B) : A = B := by
  have hBB : B.IsFormalAdjoint B := by
    have hF := LinearPMap.adjoint_isFormalAdjoint hB.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hB] at hF
  have hAB : A.IsFormalAdjoint B := by
    intro f g
    have he : A f = B ⟨f,hle.1 f.property⟩ := hle.2 rfl
    rw [he]
    exact hBB ⟨f,hle.1 f.property⟩ g
  have hrev := hAB.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hrev
  exact le_antisymm hle hrev

theorem zero_coupling_recovers_full_operator (i : Fin 8) :
    hamiltonian ε hε hbar hh hb m q κ t i 0 = H := by
  symm
  apply selfadjoint_eq_of_le _ _
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε hbar hh hb m q κ t)
    (hamiltonian_selfAdjoint ε hε hbar hh hb m q κ t i 0)
  apply LinearPMap.le_graph_iff.mp
  rintro ⟨x,y⟩ hxy
  obtain ⟨f,hf,hy⟩ := (H).mem_graph_iff.mp hxy
  let u := KFCausalClosedGraphForm.formLift D f
  have hu : J u = x := (KFCausalClosedGraphForm.embedding_formLift D f).trans hf
  rw [← hu]
  apply (variational_graph ε hε hbar hh hb m q κ t i 0 u y).mpr
  intro v
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  exact (KFCausalClosedGraphForm.hamiltonian_represents_form D f v).trans
    (congrArg (fun w : Hilbert => inner ℂ w (J v)) hy)

end
end UnifiedTheory.Audit.KFCausalInteractingComponentPerturbation

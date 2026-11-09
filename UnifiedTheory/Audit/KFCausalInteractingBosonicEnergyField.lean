/- Full Bose energy forms, annihilation estimates, and a linear field
perturbation constructed from the actual interacting one-particle H(t). -/
import UnifiedTheory.Audit.KFCausalBosonicEnergyFieldHamiltonian
import UnifiedTheory.Audit.KFCausalInteractingBosonicHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalInteractingBosonicEnergyField
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalBosonicFullEnergyForm

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ) (hk : 0 < k) (t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hpos.ne' hw m g k t
local notation "hD" => KFCausalInteractingParticleEnergyGap.original_lower ε hε h hpos hb m g k hk t
local notation "V" => FormSpace (fullFormData D)
local notation "J" => embedding (fullFormData D)
local notation "Q" => energyOutput (fullFormData D)

theorem form_hamiltonian_identification : hamiltonian (fullFormData D) = fullHamiltonian D :=
  hamiltonian_identification D

theorem form_domain (x : BosonFock D) :
    (∃ u : V, J u = x) ↔ ∃ (hx : ∀ n, x n ∈ (sector D n).form.operator.domain),
      Summable (fun n => ‖(sector D n).form.operator ⟨x n, hx n⟩‖ ^ 2) :=
  form_domain_iff D x

include hk in
theorem form_number_bound (u : V) :
    (∑' n : ℕ, ((n : ℝ) * (ε / 2)) * ‖J u n‖ ^ 2) ≤ ‖Q u‖ ^ 2 :=
  number_energy_lower D (ε / 2) (by positivity) hD u

include hk in
theorem form_vacuum_gap (u : V) (hu : J u 0 = 0) :
    (ε / 2) * ‖J u‖ ^ 2 ≤ ‖Q u‖ ^ 2 :=
  vacuum_form_gap D (ε / 2) (by positivity) hD u hu

def annihilation (f : Hilbert) : V →L[ℂ] BosonFock D :=
  KFCausalBosonicAnnihilationEnergy.annihilationForm D f (ε / 2) (by positivity) hD

theorem annihilation_energy (f : Hilbert) (u : V) :
    ‖annihilation ε hε h hpos hb m g k hk t f u‖ ^ 2 ≤
      (‖f‖ ^ 2 / (ε / 2)) * ‖Q u‖ ^ 2 :=
  KFCausalBosonicAnnihilationEnergy.energy_bound D f (ε / 2) (by positivity) hD u

def fieldHamiltonian (f : Hilbert) (α : ℝ) : BosonFock D →ₗ.[ℂ] BosonFock D :=
  KFCausalBosonicEnergyFieldHamiltonian.hamiltonian D f (ε / 2) (by positivity) hD α

theorem field_selfAdjoint (f : Hilbert) (α : ℝ) :
    IsSelfAdjoint (fieldHamiltonian ε hε h hpos hb m g k hk t f α) :=
  KFCausalBosonicEnergyFieldHamiltonian.selfAdjoint D f (ε / 2) (by positivity) hD α

theorem field_variational_graph (f : Hilbert) (α : ℝ) (u : V) (y : BosonFock D) :
    (J u, y) ∈ (fieldHamiltonian ε hε h hpos hb m g k hk t f α).graph ↔
      ∀ v : V, inner ℂ (Q u) (Q v) + (α : ℂ) *
        (inner ℂ (J u) (annihilation ε hε h hpos hb m g k hk t f v) +
         inner ℂ (annihilation ε hε h hpos hb m g k hk t f u) (J v)) = inner ℂ y (J v) :=
  KFCausalBosonicEnergyFieldHamiltonian.variational_graph D f (ε / 2) (by positivity) hD α u y

theorem field_lower_bound (f : Hilbert) (α : ℝ)
    (x : (fieldHamiltonian ε hε h hpos hb m g k hk t f α).domain) :
    -(2 * α ^ 2 * (‖f‖ ^ 2 / (ε / 2))) * ‖(x : BosonFock D)‖ ^ 2 ≤
      (inner ℂ (fieldHamiltonian ε hε h hpos hb m g k hk t f α x) (x : BosonFock D)).re :=
  KFCausalBosonicEnergyFieldHamiltonian.operator_lower_bound D f (ε / 2) (by positivity) hD α x

theorem field_zero_coupling (f : Hilbert) :
    fieldHamiltonian ε hε h hpos hb m g k hk t f 0 = fullHamiltonian D :=
  KFCausalBosonicEnergyFieldHamiltonian.zero_coupling D f (ε / 2) (by positivity) hD

end
end UnifiedTheory.Audit.KFCausalInteractingBosonicEnergyField

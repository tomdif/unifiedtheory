/- A self-adjoint linear field perturbation of the actual completed Bose
energy Hamiltonian. Its full variational domain is constructed for every real
coupling. No matter interaction, ground-state existence or coupled gap is asserted. -/
import UnifiedTheory.Audit.KFCausalBosonicAnnihilationEnergy
import UnifiedTheory.Audit.KFCausalLinearFieldFormPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicEnergyFieldHamiltonian
noncomputable section
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalBosonicFullEnergyForm
open KFCausalBosonicAnnihilationEnergy KFCausalTensorSumEnergyFloor

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ) (g : ℝ)

local notation "V" => FormSpace (fullFormData D)
local notation "J" => embedding (fullFormData D)
local notation "A" => annihilationForm D f δ hδ hD
local notation "Q" => energyOutput (fullFormData D)

def fieldForm : V →L[ℂ] V := KFCausalLinearFieldFormPerturbation.perturbation J A g

theorem field_pairing (u v : V) : inner ℂ (fieldForm D f δ hδ hD g u) v =
    (g : ℂ) * (inner ℂ (J u) (A v) + inner ℂ (A u) (J v)) :=
  KFCausalLinearFieldFormPerturbation.perturbation_pairing J A g u v

theorem field_symmetric : (fieldForm D f δ hδ hD g).toLinearMap.IsSymmetric :=
  KFCausalLinearFieldFormPerturbation.perturbation_symmetric J A g

theorem field_diagonal (u : V) :
    (inner ℂ (fieldForm D f δ hδ hD g u) u).re = 2 * g * (inner ℂ (A u) (J u)).re :=
  KFCausalLinearFieldFormPerturbation.perturbation_diagonal J A g u

theorem relative_bound (u : V) :
    |(inner ℂ (fieldForm D f δ hδ hD g u) u).re| ≤
      (1/2 : ℝ) * (‖u‖ ^ 2 - ‖J u‖ ^ 2) + (2 * g ^ 2 * (‖f‖ ^ 2 / δ)) * ‖J u‖ ^ 2 := by
  rw [field_diagonal, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hi : |(inner ℂ (A u) (J u)).re| ≤ ‖A u‖ * ‖J u‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hn := energy_norm_bound D f δ hδ hD u
  have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg (J u))
  have hb := mul_le_mul_of_nonneg_left (hi.trans hm)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg g))
  have hc : 0 ≤ ‖f‖ ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
  have hy := two_mul_le_add_mul_sq (a := ‖Q u‖)
    (b := |g| * Real.sqrt (‖f‖ ^ 2 / δ) * ‖J u‖) (by norm_num : (0 : ℝ) < 1/2)
  rw [mul_pow, mul_pow, Real.sq_sqrt hc, sq_abs] at hy
  have hq := form_norm_identity (fullFormData D) u
  nlinarith

def hamiltonian : BosonFock D →ₗ.[ℂ] BosonFock D :=
  KFCausalRelativeFormPerturbation.hamiltonian J (fieldForm D f δ hδ hD g)
    (2 * g ^ 2 * (‖f‖ ^ 2 / δ)) (1/2) (by norm_num) (by norm_num)
    (relative_bound D f δ hδ hD g) (embedding_injective (fullFormData D))
    (embedding_dense (fullFormData D)) (field_symmetric D f δ hδ hD g)

theorem selfAdjoint : IsSelfAdjoint (hamiltonian D f δ hδ hD g) :=
  KFCausalRelativeFormPerturbation.hamiltonian_selfAdjoint _ _ _ _ _ _ _ _ _ _

theorem variational_graph (u : V) (y : BosonFock D) :
    (J u, y) ∈ (hamiltonian D f δ hδ hD g).graph ↔
      ∀ v : V, inner ℂ (Q u) (Q v) +
        (g : ℂ) * (inner ℂ (J u) (A v) + inner ℂ (A u) (J v)) = inner ℂ y (J v) := by
  rw [hamiltonian, KFCausalRelativeFormPerturbation.variational_graph]
  simp only [field_pairing]
  have he (v : V) : inner ℂ u v - inner ℂ (J u) (J v) = inner ℂ (Q u) (Q v) := by
    rw [form_inner_identity, add_sub_cancel_left]
  simp only [he]

theorem domain_in_form_range (x : (hamiltonian D f δ hδ hD g).domain) :
    ∃ u : V, J u = (x : BosonFock D) := by
  obtain ⟨y, hy⟩ := x.property
  exact ⟨Ring.inverse (KFCausalRelativeFormPerturbation.shiftedForm J
    (fieldForm D f δ hδ hD g) (2 * g ^ 2 * (‖f‖ ^ 2 / δ))) ((embedding (fullFormData D)).adjoint y), hy⟩

theorem full_graph (x y : BosonFock D) :
    (x, y) ∈ (hamiltonian D f δ hδ hD g).graph ↔
      ∃ u : V, J u = x ∧ ∀ v : V, inner ℂ (Q u) (Q v) +
        (g : ℂ) * (inner ℂ (J u) (A v) + inner ℂ (A u) (J v)) = inner ℂ y (J v) := by
  constructor
  · intro hg
    obtain ⟨z, hz, hzy⟩ := (hamiltonian D f δ hδ hD g).mem_graph_iff.mp hg
    obtain ⟨u, hu⟩ := domain_in_form_range D f δ hδ hD g z
    have hx : J u = x := hu.trans hz
    exact ⟨u, hx, (variational_graph D f δ hδ hD g u y).mp (hx.symm ▸ hg)⟩
  · rintro ⟨u, rfl, hu⟩
    exact (variational_graph D f δ hδ hD g u y).mpr hu

theorem lower_bound (u : V) (y : BosonFock D)
    (hg : (J u, y) ∈ (hamiltonian D f δ hδ hD g).graph) :
    -(2 * g ^ 2 * (‖f‖ ^ 2 / δ)) * ‖J u‖ ^ 2 ≤ (inner ℂ y (J u)).re :=
  KFCausalRelativeFormPerturbation.form_lower_bound _ _ _ _ _ _ _ _ _ _
    (embedding_contraction (fullFormData D)) u y hg

theorem operator_lower_bound (x : (hamiltonian D f δ hδ hD g).domain) :
    -(2 * g ^ 2 * (‖f‖ ^ 2 / δ)) * ‖(x : BosonFock D)‖ ^ 2 ≤
      (inner ℂ (hamiltonian D f δ hδ hD g x) (x : BosonFock D)).re := by
  obtain ⟨u, hu⟩ := domain_in_form_range D f δ hδ hD g x
  have hg := (hamiltonian D f δ hδ hD g).mem_graph x
  rw [← hu] at hg ⊢
  exact lower_bound D f δ hδ hD g u _ hg

theorem zero_coupling : hamiltonian D f δ hδ hD 0 = fullHamiltonian D := by
  rw [← hamiltonian_identification D]
  apply LinearPMap.eq_of_eq_graph
  ext p
  rcases p with ⟨x, y⟩
  rw [full_graph]
  constructor
  · rintro ⟨u, rfl, hp⟩
    have hq : ∀ v : V, inner ℂ (Q u) (Q v) = inner ℂ y (J v) := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hp
    obtain ⟨hx, hy⟩ := (hamiltonian_domain_characterization (fullFormData D) u y).mpr hq
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨J u, hx⟩, rfl, hy⟩
  · intro hg
    obtain ⟨z, hz, hzy⟩ := (KFCausalClosedGraphForm.hamiltonian (fullFormData D)).mem_graph_iff.mp hg
    refine ⟨formLift (fullFormData D) z, (embedding_formLift _ z).trans hz, ?_⟩
    intro v
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [hamiltonian_represents_form]
    exact congrArg (fun w => inner ℂ w (J v)) hzy

end
end UnifiedTheory.Audit.KFCausalBosonicEnergyFieldHamiltonian

/- Real spectral-gap requirements for an unbounded Hamiltonian.
A gap requires bounded two-sided resolvents throughout the open interval;
absence of eigenvectors alone does not fill this requirement. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SpectralGap
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ResolventWitness (A : H →ₗ.[ℂ] H) (lam : ℝ) where
  inverse : H →L[ℂ] H
  right_inverse : ∀ y, (inverse y, y + (lam : ℂ) • inverse y) ∈ A.graph
  left_inverse : ∀ x : A.domain, inverse (A x - (lam : ℂ) • (x : H)) = x

def InRealResolvent (A : H →ₗ.[ℂ] H) (lam : ℝ) : Prop := Nonempty (ResolventWitness A lam)

def IntervalGap (A : H →ₗ.[ℂ] H) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ lam : ℝ, 0 < lam → lam < Δ → InRealResolvent A lam

def FiniteExcitation (A : H →ₗ.[ℂ] H) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ¬ InRealResolvent A lam

def VacuumFormGap (A : H →ₗ.[ℂ] H) (Ω : H) (Δ : ℝ) : Prop :=
  ∀ x : A.domain, inner ℂ Ω (x : H) = 0 →
    Δ * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (A x) (x : H)).re

structure SpectralRequirements (A : H →ₗ.[ℂ] H) (Ω : H) (Δ : ℝ) : Prop where
  self_adjoint : IsSelfAdjoint A
  vacuum_norm : ‖Ω‖ = 1
  vacuum_stationary : (Ω, 0) ∈ A.graph
  positive_energy : ∀ x : A.domain, 0 ≤ (inner ℂ (A x) (x : H)).re
  unique_zero_energy : ∀ x : H, (x, 0) ∈ A.graph → ∃ c : ℂ, x = c • Ω
  spectral_gap : IntervalGap A Δ
  finite_excitation : FiniteExcitation A

theorem resolvent_excludes_eigenvector (A : H →ₗ.[ℂ] H) (lam : ℝ)
    (R : ResolventWitness A lam) (x : A.domain) (hx : A x = (lam : ℂ) • (x : H)) :
    (x : H) = 0 := by
  have he := R.left_inverse x
  rw [hx, sub_self, map_zero] at he
  exact he.symm

theorem vacuum_not_in_resolvent (A : H →ₗ.[ℂ] H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hg : (Ω, 0) ∈ A.graph) : ¬ InRealResolvent A 0 := by
  rintro ⟨R⟩
  obtain ⟨u, hu, hv⟩ := A.mem_graph_iff.mp hg
  have hz : (u : H) = 0 := resolvent_excludes_eigenvector A 0 R u (by simpa using hv)
  have he : Ω = 0 := hu.symm.trans hz
  simpa [he] using hΩ

theorem gap_excludes_eigenvector (A : H →ₗ.[ℂ] H) (Δ lam : ℝ)
    (hgap : IntervalGap A Δ) (hlam : 0 < lam) (hlamΔ : lam < Δ)
    (x : A.domain) (hx : A x = (lam : ℂ) • (x : H)) : (x : H) = 0 := by
  obtain ⟨R⟩ := hgap.2 lam hlam hlamΔ
  exact resolvent_excludes_eigenvector A lam R x hx

end
end UnifiedTheory.Clay.YangMills.SpectralGap

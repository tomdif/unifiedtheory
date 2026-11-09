/- Explicit S3 matter operators and their number-changing mode coupling.
The constant matter vector is deliberately unnormalized; the averaging
projector is the orthogonal projector for the counting inner product.
This is a symmetric coupling on the occupation core, not the self-adjoint
Pauli--Fierz Hamiltonian or its ground-state theorem. -/
import UnifiedTheory.Audit.KFCausalBosonicCCR
import UnifiedTheory.Audit.KFCausalDynamicalGauge
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalPauliFierzMatterCore
noncomputable section
open scoped BigOperators
open KFCausalBosonicOccupationSpace KFCausalBosonicCCR

abbrev Group := Equiv.Perm (Fin 3)
abbrev Matter := Group → ℂ

def sign (r : Group) : ℂ := ((Equiv.Perm.sign r : ℤ) : ℂ)

@[simp] theorem sign_one : sign 1 = 1 := by simp [sign]
@[simp] theorem sign_conj (r : Group) : starRingEnd ℂ (sign r) = sign r := by
  simp [sign]

theorem sign_square (r : Group) : sign r * sign r = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign r) with he | he <;> simp [sign, he]

theorem sign_sum : ∑ r : Group, sign r = 0 := by
  let τ : Group := Equiv.swap 0 1
  have hm (r : Group) : sign (τ*r) = -sign r := by
    simp [sign, τ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)]
  have he := Equiv.sum_comp (Equiv.mulLeft τ) sign
  change (∑ r : Group, sign (τ*r)) = ∑ r : Group, sign r at he
  simp only [hm, Finset.sum_neg_distrib] at he
  linear_combination (-1/2 : ℂ) * he

def uniform : Matter := fun _ => 1
def B : Matter →ₗ[ℂ] Matter where
  toFun ψ r := sign r * ψ r
  map_add' _ _ := by ext r; simp [mul_add]
  map_smul' _ _ := by ext r; simp [mul_left_comm]

def mean : Matter →ₗ[ℂ] Matter where
  toFun ψ _ := (Fintype.card Group : ℂ)⁻¹ * ∑ r, ψ r
  map_add' _ _ := by ext r; simp [Finset.sum_add_distrib, mul_add]
  map_smul' _ _ := by ext r; simp [Finset.mul_sum, mul_left_comm]

def matterEnergy (Δ : ℝ) : Matter →ₗ[ℂ] Matter := (Δ : ℂ) • (LinearMap.id - mean)
def matterPairing (ψ φ : Matter) : ℂ := ∑ r, starRingEnd ℂ (ψ r) * φ r

theorem B_involution (ψ : Matter) : B (B ψ) = ψ := by
  ext r
  change sign r * (sign r * ψ r) = ψ r
  rw [← mul_assoc, sign_square, one_mul]

theorem B_symmetric (ψ φ : Matter) : matterPairing (B ψ) φ = matterPairing ψ (B φ) := by
  simp only [matterPairing, B, LinearMap.coe_mk, AddHom.coe_mk, map_mul, sign_conj]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem mean_idempotent (ψ : Matter) : mean (mean ψ) = mean ψ := by
  have hn : (Fintype.card Group : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext r
  simp [mean, hn]

theorem mean_symmetric (ψ φ : Matter) : matterPairing (mean ψ) φ = matterPairing ψ (mean φ) := by
  simp only [matterPairing, mean, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_inv₀,
    map_natCast, map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem mean_uniform : mean uniform = uniform := by
  have hn : (Fintype.card Group : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext r
  simp [mean, uniform, hn]

theorem mean_sign : mean (B uniform) = 0 := by
  ext r
  simp [mean, B, uniform, sign_sum]

theorem uniform_sign_orthogonal : matterPairing uniform (B uniform) = 0 := by
  simp [matterPairing, uniform, B, sign_sum]

theorem matter_commutator (Δ : ℝ) :
    matterEnergy Δ (B uniform) - B (matterEnergy Δ uniform) = (Δ : ℂ) • B uniform := by
  simp [matterEnergy, mean_sign, mean_uniform]

theorem matter_commutator_nonzero (Δ : ℝ) (hΔ : Δ ≠ 0) :
    matterEnergy Δ (B uniform) - B (matterEnergy Δ uniform) ≠ 0 := by
  rw [matter_commutator]
  intro he
  have h1 := congrFun he 1
  simp [B, uniform, hΔ] at h1

variable {ι : Type*}
abbrev CoupledCore (ι : Type*) := Group → Core ι
def coupledPairing (u v : CoupledCore ι) : ℂ := ∑ r, inner ℂ (embed (u r)) (embed (v r))

def coupling (i : ι) : CoupledCore ι →ₗ[ℂ] CoupledCore ι where
  toFun u r := sign r • field i (u r)
  map_add' _ _ := by ext r; simp [smul_add]
  map_smul' _ _ := by ext r; simp [smul_smul, mul_comm]

theorem coupling_symmetric (i : ι) (u v : CoupledCore ι) :
    coupledPairing (coupling i u) v = coupledPairing u (coupling i v) := by
  unfold coupledPairing
  apply Finset.sum_congr rfl
  intro r _
  change inner ℂ (embed (sign r • field i (u r))) (embed (v r)) =
    inner ℂ (embed (u r)) (embed (sign r • field i (v r)))
  rw [map_smul, map_smul, inner_smul_left, inner_smul_right, sign_conj, field_symmetric]

def uncoupledVacuum : CoupledCore ι := fun _ => vacuumCore

theorem coupling_vacuum_nonzero (i : ι) : coupling i uncoupledVacuum ≠ 0 := by
  intro he
  have h1 := congrFun he 1
  change sign 1 • field i vacuumCore = 0 at h1
  rw [sign_one, one_smul] at h1
  apply field_vacuum_nonzero i
  rw [h1, map_zero]

/-- The relative-coordinate lift is gauge invariant, including after the
bosonic mode coupling. This concerns the existing finite S3 gauge action. -/
theorem coupling_gauge_invariant (i : ι) (u : CoupledCore ι)
    {V E : Type*} (s t : E → V) (e : E)
    (a : V → Group) (c : KFCausalDynamicalGauge.Config V E Group) :
    coupling i u (KFCausalDynamicalGauge.relative s t
      (KFCausalDynamicalGauge.gauge s t a c) e) =
    coupling i u (KFCausalDynamicalGauge.relative s t c e) := by
  rw [KFCausalDynamicalGauge.relative_gauge]

end
end UnifiedTheory.Audit.KFCausalPauliFierzMatterCore

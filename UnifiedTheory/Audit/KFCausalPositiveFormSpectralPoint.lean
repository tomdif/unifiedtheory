/- A finite positive spectral point follows from the bounded positive inverse
of a nontrivial strictly positive closed-form Hamiltonian. No eigenvectors
or preassigned spectral law are assumed. -/
import UnifiedTheory.Audit.KFCausalPositiveFormResolvent
import UnifiedTheory.Audit.KFCausalCoerciveFormHamiltonian
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPositiveFormSpectralPoint
noncomputable section
open KFCausalClosedGraphForm KFCausalTensorSumEnergyFloor KFCausalPositiveFormResolvent
open UnifiedTheory.Clay.YangMills.SpectralGap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem inverse_positive (D : Data H K) (delta : ℝ) (hdelta : 0 < delta)
    (hD : LowerBound D delta) : 0 ≤ resolvent D 0 := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  constructor
  · exact KFCausalCoerciveFormHamiltonian.resolvent_symmetric (embedding D)
      (shiftedForm D 0) (shiftedUnit D delta 0 (le_refl _) hdelta hD) (shifted_symmetric D 0)
  · intro y
    obtain ⟨x, hx, hy⟩ := (hamiltonian D).mem_graph_iff.mp
      (right_graph D delta 0 (le_refl _) hdelta hD y)
    dsimp only at hx hy
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at hy
    change 0 ≤ (inner ℂ (resolvent D 0 y) y).re
    rw [← hx, ← hy]
    change 0 ≤ RCLike.re (inner ℂ (x : H) (hamiltonian D x))
    rw [inner_re_symm]
    exact hamiltonian_positive D x

theorem inverse_ne_zero [Nontrivial H] (D : Data H K) (delta : ℝ) (hdelta : 0 < delta)
    (hD : LowerBound D delta) : resolvent D 0 ≠ 0 := by
  have hi : Function.Injective (resolvent D 0) :=
    KFCausalCoerciveFormHamiltonian.resolvent_injective (embedding D)
      (embedding_injective D) (embedding_dense D) (shiftedForm D 0)
      (shiftedUnit D delta 0 (le_refl _) hdelta hD)
  intro hz
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  apply hx
  apply hi
  simp [hz]

variable {A : H →ₗ.[ℂ] H}

theorem resolvent_product_unit (R : ResolventWitness A 0) (lam : ℝ)
    (S : ResolventWitness A lam) : IsUnit (1 - (lam : ℂ) • R.inverse) := by
  have hRS (y : H) : R.inverse y + (lam : ℂ) • R.inverse (S.inverse y) = S.inverse y := by
    obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp (S.right_inverse y)
    dsimp only at hx hy
    have he := R.left_inverse x
    simp only [Complex.ofReal_zero, zero_smul, sub_zero] at he
    rw [hx, hy, map_add, map_smul] at he
    exact he
  have hSR (y : H) : S.inverse y - (lam : ℂ) • S.inverse (R.inverse y) = R.inverse y := by
    obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp (R.right_inverse y)
    dsimp only at hx hy
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at hy
    have he := S.left_inverse x
    rw [hx, hy, map_sub, map_smul] at he
    exact he
  have hr : (1 - (lam : ℂ) • R.inverse) * (1 + (lam : ℂ) • S.inverse) = 1 := by
    ext y
    change y + (lam : ℂ) • S.inverse y - (lam : ℂ) • R.inverse (y + (lam : ℂ) • S.inverse y) = y
    rw [map_add, map_smul, hRS]
    module
  have hl : (1 + (lam : ℂ) • S.inverse) * (1 - (lam : ℂ) • R.inverse) = 1 := by
    ext y
    change y - (lam : ℂ) • R.inverse y + (lam : ℂ) • S.inverse (y - (lam : ℂ) • R.inverse y) = y
    rw [map_sub, map_smul, hSR]
    module
  exact ⟨⟨_, _, hr, hl⟩, rfl⟩

theorem inverse_spectral_point (R : ResolventWitness A 0) (r : ℝ) (hr : 0 < r)
    (hs : r ∈ spectrum ℝ R.inverse) : ¬ InRealResolvent A r⁻¹ := by
  rintro ⟨S⟩
  have hu := resolvent_product_unit R r⁻¹ S
  have hc : IsUnit (algebraMap ℝ (H →L[ℂ] H) r) :=
    (isUnit_iff_ne_zero.mpr hr.ne').map (algebraMap ℝ (H →L[ℂ] H))
  have hp := hc.mul hu
  have he : algebraMap ℝ (H →L[ℂ] H) r * (1 - (r⁻¹ : ℝ) • R.inverse) =
      algebraMap ℝ (H →L[ℂ] H) r - R.inverse := by
    simp [Algebra.algebraMap_eq_smul_one, mul_sub, smul_sub, smul_smul, hr.ne']
  have hec : (r⁻¹ : ℝ) • R.inverse = ((r⁻¹ : ℝ) : ℂ) • R.inverse := by
    ext y
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
  rw [← hec, he] at hp
  exact (spectrum.mem_iff.mp hs) hp

theorem finite_excitation [Nontrivial H] (D : Data H K) (delta : ℝ)
    (hdelta : 0 < delta) (hD : LowerBound D delta) : FiniteExcitation (hamiltonian D) := by
  let R := KFCausalPositiveFormResolvent.witness D delta 0 (le_refl _) hdelta hD
  have hp : 0 < ‖R.inverse‖ := norm_pos_iff.mpr (inverse_ne_zero D delta hdelta hD)
  refine ⟨‖R.inverse‖⁻¹, inv_pos.mpr hp, inverse_spectral_point R _ hp ?_⟩
  exact CStarAlgebra.norm_mem_spectrum_of_nonneg (inverse_positive D delta hdelta hD)

end
end UnifiedTheory.Audit.KFCausalPositiveFormSpectralPoint

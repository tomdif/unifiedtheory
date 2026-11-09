/- The open positive gap for the actual auxiliary Bose direct-sum Hamiltonian.
The inverse is assembled from coercively constructed sector inverses. -/
import UnifiedTheory.Audit.KFCausalPositiveFormResolvent
import UnifiedTheory.Audit.KFCausalBoundedDirectSumMap
import UnifiedTheory.Audit.KFCausalBosonicClayGapInterface

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicIntervalResolvent
noncomputable section
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalTensorSumEnergyFloor
open UnifiedTheory.Clay.YangMills.SpectralGap

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def sectorInverse (D : Data H K) (lam : ℝ) :
    ∀ n, (sector D n).State →L[ℂ] (sector D n).State
  | 0 => (-(lam : ℂ)⁻¹) • (1 : ℂ →L[ℂ] ℂ)
  | n + 1 => KFCausalPositiveFormResolvent.resolvent (sector D (n + 1)).form lam

theorem positive_sector_lower (D : Data H K) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hD : LowerBound D delta) (n : ℕ) : LowerBound (sector D (n + 1)).form delta := by
  intro x
  have hb := KFCausalBosonicEnergyGap.sector_lower D delta hD (n + 1) x
  have hc : delta ≤ ((n + 1 : ℕ) : ℝ) * delta := by
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans hb

theorem sector_right (D : Data H K) (delta lam : ℝ) (hlam : 0 < lam)
    (hld : lam < delta) (hD : LowerBound D delta) (n : ℕ) (y : (sector D n).State) :
    (sectorInverse D lam n y, y + (lam : ℂ) • sectorInverse D lam n y) ∈
      (sectorHamiltonian D n).graph := by
  cases n with
  | zero =>
    change ℂ at y
    change (-(lam : ℂ)⁻¹ * y, y + (lam : ℂ) * (-(lam : ℂ)⁻¹ * y)) ∈ _
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    have hz : (y : ℂ) + (lam : ℂ) * (-(lam : ℂ)⁻¹ * y) = 0 := by
      simp [mul_assoc, hl]
    rw [hz]
    exact vacuum_graph D _
  | succ n =>
    exact KFCausalPositiveFormResolvent.right_graph _ delta lam hlam.le hld
      (positive_sector_lower D delta (by linarith) hD n) y

theorem sector_left (D : Data H K) (delta lam : ℝ) (hlam : 0 < lam)
    (hld : lam < delta) (hD : LowerBound D delta) (n : ℕ)
    (x : (sectorHamiltonian D n).domain) :
    sectorInverse D lam n (sectorHamiltonian D n x - (lam : ℂ) • (x : (sector D n).State)) = x := by
  cases n with
  | zero =>
    obtain ⟨u, hu, hv⟩ := (sectorHamiltonian D 0).mem_graph_iff.mp (vacuum_graph D (show ℂ from (x : (sector D 0).State)))
    dsimp only at hu hv
    have hux : u = x := Subtype.ext hu
    subst u
    rw [hv]
    change -(lam : ℂ)⁻¹ * (0 - (lam : ℂ) * (show ℂ from (x : (sector D 0).State))) = (show ℂ from (x : (sector D 0).State))
    have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    simp [mul_assoc, hl]
  | succ n =>
    exact KFCausalPositiveFormResolvent.left_inverse _ delta lam hlam.le hld
      (positive_sector_lower D delta (by linarith) hD n) x

def inverseBound (delta lam : ℝ) : ℝ := max lam⁻¹ (delta - lam)⁻¹

theorem inverseBound_nonneg (delta lam : ℝ) (hlam : 0 < lam) :
    0 ≤ inverseBound delta lam := (inv_nonneg.mpr hlam.le).trans (le_max_left _ _)

theorem sector_bound (D : Data H K) (delta lam : ℝ) (hlam : 0 < lam)
    (hld : lam < delta) (hD : LowerBound D delta) (n : ℕ) (y : (sector D n).State) :
    ‖sectorInverse D lam n y‖ ≤ inverseBound delta lam * ‖y‖ := by
  cases n with
  | zero =>
    change ℂ at y
    change ‖-(lam : ℂ)⁻¹ * (y : ℂ)‖ ≤ _
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  | succ n =>
    exact (KFCausalPositiveFormResolvent.resolvent_norm_bound _ delta lam hlam.le hld
      (positive_sector_lower D delta (by linarith) hD n) y).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

def fullInverse (D : Data H K) (delta lam : ℝ) (hlam : 0 < lam)
    (hld : lam < delta) (hD : LowerBound D delta) : BosonFock D →L[ℂ] BosonFock D :=
  KFCausalBoundedDirectSumMap.continuousMap (sectorInverse D lam) (inverseBound delta lam)
    (inverseBound_nonneg delta lam hlam) (sector_bound D delta lam hlam hld hD)

@[simp] theorem fullInverse_apply (D : Data H K) (delta lam : ℝ) (hlam : 0 < lam)
    (hld : lam < delta) (hD : LowerBound D delta) (y : BosonFock D) (n : ℕ) :
    fullInverse D delta lam hlam hld hD y n = sectorInverse D lam n (y n) := rfl

def witness (D : Data H K) (delta lam : ℝ) (hlam : 0 < lam)
    (hld : lam < delta) (hD : LowerBound D delta) : ResolventWitness (fullHamiltonian D) lam where
  inverse := fullInverse D delta lam hlam hld hD
  right_inverse y := by
    rw [full_graph]
    intro n
    exact sector_right D delta lam hlam hld hD n (y n)
  left_inverse x := by
    apply lp.ext
    funext n
    obtain ⟨u, hu, hv⟩ := (sectorHamiltonian D n).mem_graph_iff.mp
      ((full_graph D x (fullHamiltonian D x)).mp ((fullHamiltonian D).mem_graph x) n)
    dsimp only at hu hv
    change sectorInverse D lam n (fullHamiltonian D x n - (lam : ℂ) • (x : BosonFock D) n) = _
    rw [← hu, ← hv]
    exact sector_left D delta lam hlam hld hD n u

theorem interval_gap (D : Data H K) (delta : ℝ) (hdelta : 0 < delta)
    (hD : LowerBound D delta) : IntervalGap (fullHamiltonian D) delta :=
  ⟨hdelta, fun lam hlam hld => ⟨witness D delta lam hlam hld hD⟩⟩

theorem spectral_requirements_of_finite_excitation (D : Data H K) (delta : ℝ)
    (hdelta : 0 < delta) (hD : LowerBound D delta)
    (hfinite : FiniteExcitation (fullHamiltonian D)) :
    SpectralRequirements (fullHamiltonian D) (vacuum D) delta :=
  KFCausalBosonicClayGapInterface.auxiliary_spectral_requirements_of_inputs D delta hD
    (interval_gap D delta hdelta hD) hfinite

end
end UnifiedTheory.Audit.KFCausalBosonicIntervalResolvent

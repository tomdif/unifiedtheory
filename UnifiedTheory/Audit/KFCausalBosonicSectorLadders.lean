/- Symmetrized tensor creation and its Hilbert adjoint on every completed
Bose sector. Norm estimates do not assume an energy eigenbasis. -/
import UnifiedTheory.Audit.KFCausalBosonicFock
import UnifiedTheory.Audit.KFCausalBosonicSectorOneParticle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicSectorLadders
noncomputable section
open KFCausalClosedGraphForm KFCausalBosonicSectorProjection KFCausalBosonicFock
open KFCausalTensorParticleSectors (nonemptySector)

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem average_norm_le (D : Data H K) (n : ℕ) (x : (nonemptySector D n).State) :
    ‖average D n x‖ ≤ ‖x‖ := by
  rw [average_apply, norm_smul, norm_inv]
  have hc : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    ‖(Fintype.card (Equiv.Perm (Fin (n + 1))) : ℂ)‖⁻¹ *
        ‖∑ σ : Equiv.Perm (Fin (n + 1)), KFCausalParticlePermutations.action D n σ x‖ ≤
      ‖(Fintype.card (Equiv.Perm (Fin (n + 1))) : ℂ)‖⁻¹ *
        ∑ σ : Equiv.Perm (Fin (n + 1)), ‖KFCausalParticlePermutations.action D n σ x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (norm_nonneg _))
    _ = ‖x‖ := by simp [mul_assoc, hc]

theorem projection_norm_le (D : Data H K) (n : ℕ) (x : (nonemptySector D n).State) :
    ‖projection D n x‖ ≤ ‖x‖ := average_norm_le D n x

def append (D : Data H K) (f : H) : (n : ℕ) →
    (sector D n).State →L[ℂ] (sector D (n + 1)).State
  | 0 => (projection D 0).comp ((ContinuousLinearMap.id ℂ ℂ).smulRight f)
  | n + 1 => (projection D (n + 1)).comp
      ((KFCausalCompletedTensor.left (nonemptySector D n).State H f).comp (invariant D n).subtypeL)

theorem append_bound (D : Data H K) (f : H) (n : ℕ) (x : (sector D n).State) :
    ‖append D f n x‖ ≤ ‖f‖ * ‖x‖ := by
  cases n with
  | zero =>
    change ‖projection D 0 ((show ℂ from x) • f)‖ ≤ ‖f‖ * ‖(show ℂ from x)‖
    apply (projection_norm_le D 0 _).trans_eq
    rw [norm_smul]
    exact mul_comm _ _
  | succ n =>
    change ‖projection D (n + 1) (KFCausalCompletedTensor.pure _ H x.val f)‖ ≤ ‖f‖ * ‖x‖
    apply (projection_norm_le D (n + 1) _).trans_eq
    dsimp only [sector, KFCausalTensorParticleSectors.fromForm, nonemptySector,
      KFCausalTensorParticleSectors.product] at x ⊢
    rw [KFCausalCompletedTensor.pure,
      (KFCausalCompletedTensor.includeTensor (nonemptySector D n).State H).norm_map,
      TensorProduct.norm_tmul]
    exact mul_comm _ _

def creator (D : Data H K) (f : H) (n : ℕ) :
    (sector D n).State →L[ℂ] (sector D (n + 1)).State :=
  (Real.sqrt (n + 1) : ℂ) • append D f n

theorem creator_bound (D : Data H K) (f : H) (n : ℕ) (x : (sector D n).State) :
    ‖creator D f n x‖ ≤ (Real.sqrt (n + 1) * ‖f‖) * ‖x‖ := by
  rw [creator, ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left (append_bound D f n x) (Real.sqrt_nonneg _)

theorem creator_norm_le (D : Data H K) (f : H) (n : ℕ) :
    ‖creator D f n‖ ≤ Real.sqrt (n + 1) * ‖f‖ :=
  (creator D f n).opNorm_le_bound (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (creator_bound D f n)

def annihilator (D : Data H K) (f : H) (n : ℕ) :
    (sector D (n + 1)).State →L[ℂ] (sector D n).State := (creator D f n).adjoint

theorem adjoint_pairing (D : Data H K) (f : H) (n : ℕ)
    (x : (sector D n).State) (y : (sector D (n + 1)).State) :
    inner ℂ (annihilator D f n y) x = inner ℂ y (creator D f n x) :=
  (creator D f n).adjoint_inner_left x y

theorem annihilator_bound (D : Data H K) (f : H) (n : ℕ)
    (x : (sector D (n + 1)).State) :
    ‖annihilator D f n x‖ ≤ (Real.sqrt (n + 1) * ‖f‖) * ‖x‖ := by
  apply (annihilator D f n).le_opNorm x |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  simpa only [annihilator, LinearIsometryEquiv.norm_map] using creator_norm_le D f n

theorem annihilator_square_bound (D : Data H K) (f : H) (n : ℕ)
    (x : (sector D (n + 1)).State) :
    ‖annihilator D f n x‖ ^ 2 ≤ ‖f‖ ^ 2 * ((n : ℝ) + 1) * ‖x‖ ^ 2 := by
  have he := pow_le_pow_left₀ (norm_nonneg (annihilator D f n x))
    (annihilator_bound D f n x) 2
  have hs : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  calc
    _ ≤ ((Real.sqrt (n + 1) * ‖f‖) * ‖x‖) ^ 2 := he
    _ = _ := by rw [mul_pow, mul_pow, hs]; ring

theorem creator_vacuum (D : Data H K) (f : H) :
    creator D f 0 (1 : ℂ) = projection D 0 f := by
  simp only [creator, ContinuousLinearMap.smul_apply, Nat.cast_zero, zero_add,
    Real.sqrt_one, Complex.ofReal_one, one_smul]
  change projection D 0 ((1 : ℂ) • f) = projection D 0 f
  rw [one_smul]

end
end UnifiedTheory.Audit.KFCausalBosonicSectorLadders

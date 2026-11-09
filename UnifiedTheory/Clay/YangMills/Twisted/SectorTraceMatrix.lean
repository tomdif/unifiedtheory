/- Sector traces of a positive semidefinite transfer matrix: the matrix form of
`TwistedFluxRecursion.sectorTrace_double`.

For a real PSD matrix `A`, `tr(A^(2t)) ≤ (tr A^t)²` (spectral theorem). For a symmetric involution `Ω`
commuting with `A` (the center element), the sector projections `P = (1-Ω)/2`, `Q = (1+Ω)/2` give sector
traces `Z_e(t) = tr(P A^t)`, `Z_0(t) = tr(Q A^t)` that satisfy the same doubling inequality for `t ≥ 1`,
because `(P A P)^t = P A^t` and `P A P` is PSD. Then `Z_0 + Z_e = tr A^t` (untwisted) and
`Z_0 - Z_e = tr(Ω A^t)` (twisted), and the flux ratio obeys `y(2t) ≤ K(t) y(t)²`.

Finite-dimensional only. Identifying `A` with the lattice transfer operator is not formalized here. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.SectorTraceMatrix

open Matrix Unitary
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_pow_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (t : ℕ) :
    (A ^ t).trace = ∑ i, hA.eigenvalues i ^ t := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow, conjStarAlgAut_apply, trace_mul_cycle,
    coe_star_mul_self, one_mul, diagonal_pow, trace_diagonal]
  simp

omit [DecidableEq n] in
theorem sum_sq_le_sq_sum (f : n → ℝ) (h0 : ∀ i, 0 ≤ f i) :
    ∑ i, f i ^ 2 ≤ (∑ i, f i) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)) (h0 i)

theorem trace_pow_double {A : Matrix n n ℝ} (hA : A.PosSemidef) (t : ℕ) :
    (A ^ (2 * t)).trace ≤ ((A ^ t).trace) ^ 2 ∧ 0 ≤ (A ^ t).trace := by
  have h0 : ∀ i, 0 ≤ hA.1.eigenvalues i ^ t := fun i => pow_nonneg (hA.eigenvalues_nonneg i) t
  rw [trace_pow_eq_sum hA.1, trace_pow_eq_sum hA.1]
  refine ⟨?_, Finset.sum_nonneg fun i _ => h0 i⟩
  have := sum_sq_le_sq_sum _ h0
  simpa [← pow_mul, mul_comm] using this

/-! ### Generic symmetric projection commuting with `A` -/

omit [DecidableEq n] in
theorem proj_conj_posSemidef {A P : Matrix n n ℝ} (hA : A.PosSemidef) (hPT : Pᵀ = P) :
    (P * A * P).PosSemidef := by
  have := hA.conjTranspose_mul_mul_same P
  rwa [conjTranspose_eq_transpose_of_trivial, hPT] at this

theorem proj_conj_pow {A P : Matrix n n ℝ} (hPP : P * P = P) (hPA : P * A = A * P) :
    ∀ t : ℕ, 1 ≤ t → (P * A * P) ^ t = P * A ^ t := by
  have hPAP : P * A * P = P * A := by rw [mul_assoc, ← hPA, ← mul_assoc, hPP]
  have hc : Commute P A := hPA
  intro t ht
  induction t with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hPAP]
    · rw [pow_succ, ih hk, hPAP, ← mul_assoc, mul_assoc P, ((hc.pow_right k).eq).symm,
        ← mul_assoc, hPP, mul_assoc, ← pow_succ]

theorem proj_trace_double {A P : Matrix n n ℝ} (hA : A.PosSemidef) (hPP : P * P = P)
    (hPT : Pᵀ = P) (hPA : P * A = A * P) (t : ℕ) (ht : 1 ≤ t) :
    (P * A ^ (2 * t)).trace ≤ ((P * A ^ t).trace) ^ 2 ∧ 0 ≤ (P * A ^ t).trace := by
  have h := trace_pow_double (proj_conj_posSemidef hA hPT) t
  rwa [proj_conj_pow hPP hPA t ht, proj_conj_pow hPP hPA (2 * t) (by omega)] at h

/-! ### The flux sectors of a center element `Ω` -/

/-- Twisted (odd) sector projection `(1 - Ω)/2`. -/
noncomputable def projE (Ω : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (1 - Ω)
/-- Untwisted (even) sector projection `(1 + Ω)/2`. -/
noncomputable def projO (Ω : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (1 + Ω)

theorem projE_idem {Ω : Matrix n n ℝ} (h2 : Ω * Ω = 1) : projE Ω * projE Ω = projE Ω := by
  unfold projE
  rw [smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, h2]
  simp only [one_mul, mul_one]
  rw [show (1 - Ω - (Ω - 1) : Matrix n n ℝ) = (2 : ℝ) • (1 - Ω) by module, smul_smul]
  norm_num

theorem projO_idem {Ω : Matrix n n ℝ} (h2 : Ω * Ω = 1) : projO Ω * projO Ω = projO Ω := by
  unfold projO
  rw [smul_mul_smul_comm, add_mul, mul_add, mul_add, h2]
  simp only [one_mul, mul_one]
  rw [show (1 + Ω + (Ω + 1) : Matrix n n ℝ) = (2 : ℝ) • (1 + Ω) by module, smul_smul]
  norm_num

omit [Fintype n] in
theorem projE_transpose {Ω : Matrix n n ℝ} (hT : Ωᵀ = Ω) : (projE Ω)ᵀ = projE Ω := by
  simp [projE, transpose_sub, hT]

omit [Fintype n] in
theorem projO_transpose {Ω : Matrix n n ℝ} (hT : Ωᵀ = Ω) : (projO Ω)ᵀ = projO Ω := by
  simp [projO, transpose_add, hT]

theorem projE_comm {Ω A : Matrix n n ℝ} (hc : Ω * A = A * Ω) :
    projE Ω * A = A * projE Ω := by
  simp [projE, sub_mul, mul_sub, hc]

theorem projO_comm {Ω A : Matrix n n ℝ} (hc : Ω * A = A * Ω) :
    projO Ω * A = A * projO Ω := by
  simp [projO, add_mul, mul_add, hc]

theorem projE_posSemidef {Ω A : Matrix n n ℝ} (hA : A.PosSemidef) (hT : Ωᵀ = Ω) :
    (projE Ω * A * projE Ω).PosSemidef := proj_conj_posSemidef hA (projE_transpose hT)

theorem projO_posSemidef {Ω A : Matrix n n ℝ} (hA : A.PosSemidef) (hT : Ωᵀ = Ω) :
    (projO Ω * A * projO Ω).PosSemidef := proj_conj_posSemidef hA (projO_transpose hT)

theorem projE_conj_pow {Ω A : Matrix n n ℝ} (h2 : Ω * Ω = 1) (hc : Ω * A = A * Ω)
    (t : ℕ) (ht : 1 ≤ t) : (projE Ω * A * projE Ω) ^ t = projE Ω * A ^ t :=
  proj_conj_pow (projE_idem h2) (projE_comm hc) t ht

theorem projO_conj_pow {Ω A : Matrix n n ℝ} (h2 : Ω * Ω = 1) (hc : Ω * A = A * Ω)
    (t : ℕ) (ht : 1 ≤ t) : (projO Ω * A * projO Ω) ^ t = projO Ω * A ^ t :=
  proj_conj_pow (projO_idem h2) (projO_comm hc) t ht

/-- Twisted sector trace `Z_e(t) = tr(P A^t)`. -/
noncomputable def Ze (Ω A : Matrix n n ℝ) (t : ℕ) : ℝ := (projE Ω * A ^ t).trace
/-- Untwisted sector trace `Z_0(t) = tr(Q A^t)`. -/
noncomputable def Z0 (Ω A : Matrix n n ℝ) (t : ℕ) : ℝ := (projO Ω * A ^ t).trace

theorem Ze_double {Ω A : Matrix n n ℝ} (hA : A.PosSemidef) (h2 : Ω * Ω = 1) (hT : Ωᵀ = Ω)
    (hc : Ω * A = A * Ω) (t : ℕ) (ht : 1 ≤ t) :
    Ze Ω A (2 * t) ≤ Ze Ω A t ^ 2 ∧ 0 ≤ Ze Ω A t :=
  proj_trace_double hA (projE_idem h2) (projE_transpose hT) (projE_comm hc) t ht

theorem Z0_double {Ω A : Matrix n n ℝ} (hA : A.PosSemidef) (h2 : Ω * Ω = 1) (hT : Ωᵀ = Ω)
    (hc : Ω * A = A * Ω) (t : ℕ) (ht : 1 ≤ t) :
    Z0 Ω A (2 * t) ≤ Z0 Ω A t ^ 2 ∧ 0 ≤ Z0 Ω A t :=
  proj_trace_double hA (projO_idem h2) (projO_transpose hT) (projO_comm hc) t ht

/-! ### Untwisted / twisted traces and the flux-ratio step -/

theorem Z0_add_Ze (Ω A : Matrix n n ℝ) (t : ℕ) : Z0 Ω A t + Ze Ω A t = (A ^ t).trace := by
  rw [Z0, Ze, ← trace_add, ← add_mul]
  congr 2
  simp only [projO, projE, ← smul_add]
  rw [show (1 + Ω + (1 - Ω) : Matrix n n ℝ) = (2 : ℝ) • 1 by module, smul_smul]
  norm_num

theorem Z0_sub_Ze (Ω A : Matrix n n ℝ) (t : ℕ) : Z0 Ω A t - Ze Ω A t = (Ω * A ^ t).trace := by
  rw [Z0, Ze, ← trace_sub, ← sub_mul]
  congr 2
  simp only [projO, projE, ← smul_sub]
  rw [show (1 + Ω - (1 - Ω) : Matrix n n ℝ) = (2 : ℝ) • Ω by module, smul_smul]
  norm_num

theorem flux_ratio_step {Ω A : Matrix n n ℝ} (hA : A.PosSemidef) (h2 : Ω * Ω = 1)
    (hT : Ωᵀ = Ω) (hc : Ω * A = A * Ω) (t : ℕ) (ht : 1 ≤ t)
    (h0t : 0 < Z0 Ω A t) (h02t : 0 < Z0 Ω A (2 * t)) :
    Ze Ω A (2 * t) / Z0 Ω A (2 * t) ≤
      (Z0 Ω A t ^ 2 / Z0 Ω A (2 * t)) * (Ze Ω A t / Z0 Ω A t) ^ 2 := by
  have hA' := (Ze_double hA h2 hT hc t ht).1
  have : (Z0 Ω A t ^ 2 / Z0 Ω A (2 * t)) * (Ze Ω A t / Z0 Ω A t) ^ 2 =
      Ze Ω A t ^ 2 / Z0 Ω A (2 * t) := by field_simp
  rw [this]; exact div_le_div_of_nonneg_right hA' h02t.le

end UnifiedTheory.Clay.YangMills.Twisted.SectorTraceMatrix

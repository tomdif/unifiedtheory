/- Physical energy from the actual normalized transfer eigenvalue and from
contraction over several time steps. The contraction estimate is an explicit
input; finite-cutoff positivity alone does not establish a uniform mass. -/
import UnifiedTheory.Clay.YangMills.TransferEnergySurvival
import UnifiedTheory.Clay.YangMills.TransferSpectralScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.TransferPhysicalRatio
noncomputable section
open TransferEnergySurvival
open Filter
open scoped Topology

/-- Exact physical gap criterion. Zero transfer eigenvalues are excluded. -/
theorem energy_lower_iff (a r m : ℝ) (ha : 0 < a) (hr : 0 < r) :
    m ≤ -Real.log r / a ↔ r ≤ Real.exp (-a * m) := by
  rw [le_div_iff₀ ha, ← Real.log_le_iff_le_exp hr]
  constructor <;> intro h <;> nlinarith

/-- A one-step loss must be compared with the temporal lattice spacing. -/
theorem deficit_energy_lower (a r ε : ℝ) (ha : 0 < a) (hr : 0 < r)
    (hdeficit : r ≤ 1 - ε) : ε / a ≤ -Real.log r / a := by
  apply div_le_div_of_nonneg_right _ ha.le
  have h := Real.log_le_sub_one_of_pos hr
  linarith

/-- A fixed contraction after N steps gives a physical energy floor when
the total physical time N*a is bounded above by tau. -/
theorem block_energy_lower (a r q tau : ℝ) (N : ℕ) (ha : 0 < a)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hN : 0 < N)
    (htime : (N : ℝ) * a ≤ tau) (hblock : r ^ N ≤ q) :
    -Real.log q / tau ≤ -Real.log r / a := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have htau : 0 < tau := (mul_pos hNr ha).trans_le htime
  have hlog := Real.log_le_log (pow_pos hr N) hblock
  rw [Real.log_pow] at hlog
  have hqlog : Real.log q < 0 := Real.log_neg hq hq1
  have hrlog : Real.log r < 0 := by nlinarith
  apply (div_le_div_iff₀ htau ha).mpr
  have h1 := mul_le_mul_of_nonneg_right hlog ha.le
  have h2 := mul_le_mul_of_nonneg_left htime (neg_nonneg.mpr hrlog.le)
  nlinarith

/-- Even the exact logarithmic energy bound obtained from global kernel
minorization tends to zero with spatial volume at fixed positive coupling.
This is a limitation of that estimate, not a statement that the true gap closes. -/
theorem global_kernel_bound_vanishes (a beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun V : ℝ => -Real.log (1 - Real.exp (-(24 * beta * V))) / a)
      atTop (𝓝 0) := by
  have hb : Tendsto (fun V : ℝ => 24 * beta * V) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hb
  have hl := (tendsto_const_nhds.sub he).log (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simpa only [sub_zero, Real.log_one, neg_zero, zero_div] using hl.neg.div_const a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Normalizing by the top eigenvalue produces exactly the eigenvalue ratio. -/
theorem normalized_eigenvector (T : H →L[ℂ] H) (lam rho : ℝ)
    (v : H) (heig : T v = rho • v) :
    ((lam⁻¹ : ℂ) • T) v = (rho / lam) • v := by
  simp only [ContinuousLinearMap.smul_apply, heig,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  exact mul_comm _ _

theorem iterate_eigenvector (A : H →L[ℂ] H) (r : ℝ) (v : H)
    (heig : A v = r • v) (N : ℕ) : iterate A N v = r ^ N • v := by
  induction N with
  | zero => simp [iterate_zero]
  | succ N ih =>
    rw [iterate_succ, ih, map_real_smul A A.continuous, heig, smul_smul, pow_succ]

/-- A verified block contraction on the vacuum-orthogonal sector bounds
every nonnegative eigenvalue in that sector, without assuming a spectral measure. -/
theorem eigenvalue_pow_le (A : H →L[ℂ] H) (Omega v : H) (r q : ℝ) (N : ℕ)
    (hr : 0 ≤ r) (hv : v ≠ 0) (horth : inner ℂ Omega v = 0)
    (heig : A v = r • v)
    (hblock : ∀ w, inner ℂ Omega w = 0 → ‖iterate A N w‖ ≤ q * ‖w‖) :
    r ^ N ≤ q := by
  have h := hblock v horth
  rw [iterate_eigenvector A r v heig N, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr N)] at h
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp h

/-- An estimate over uniformly bounded physical time is sufficient for a
cutoff-independent lower bound. Establishing hblock for Wilson remains separate. -/
theorem physical_gap_of_block_contraction (A : H →L[ℂ] H) (Omega v : H)
    (a r q tau : ℝ) (N : ℕ) (ha : 0 < a) (hr : 0 < r)
    (hq : 0 < q) (hq1 : q < 1) (hN : 0 < N)
    (hv : v ≠ 0) (horth : inner ℂ Omega v = 0) (heig : A v = r • v)
    (htime : (N : ℝ) * a ≤ tau)
    (hblock : ∀ w, inner ℂ Omega w = 0 → ‖iterate A N w‖ ≤ q * ‖w‖) :
    -Real.log q / tau ≤ -Real.log r / a :=
  block_energy_lower a r q tau N ha hr hq hq1 hN htime
    (eigenvalue_pow_le A Omega v r q N hr.le hv horth heig hblock)

/-- Self-adjoint transfer dynamics preserve the complement of a fixed vacuum. -/
theorem iterate_orthogonal (A : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (Omega : H) (hfix : A Omega = Omega) (v : H) (hv : inner ℂ Omega v = 0)
    (N : ℕ) : inner ℂ Omega (iterate A N v) = 0 := by
  induction N with
  | zero => exact hv
  | succ N ih => rw [iterate_succ, ← hs, hfix, ih]

/-- Repeated block contraction controls every orthogonal vector, rather
than just a chosen eigenvector or observable. -/
theorem iterate_blocks_norm (A : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (Omega : H) (hfix : A Omega = Omega) (q : ℝ) (hq : 0 ≤ q) (N : ℕ)
    (hblock : ∀ w, inner ℂ Omega w = 0 → ‖iterate A N w‖ ≤ q * ‖w‖)
    (v : H) (hv : inner ℂ Omega v = 0) (k : ℕ) :
    ‖iterate A (k * N) v‖ ≤ q ^ k * ‖v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_comm, iterate_add]
    exact (hblock _ (iterate_orthogonal A hs Omega hfix v hv _)).trans (by
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left ih hq)

/-- Block contraction controls connected matrix elements on the full
orthogonal sector at all block times. -/
theorem block_pairing_bound (A : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (Omega : H) (hfix : A Omega = Omega) (q : ℝ) (hq : 0 ≤ q) (N : ℕ)
    (hblock : ∀ w, inner ℂ Omega w = 0 → ‖iterate A N w‖ ≤ q * ‖w‖)
    (u v : H) (hv : inner ℂ Omega v = 0) (k : ℕ) :
    ‖inner ℂ u (iterate A (k * N) v)‖ ≤ q ^ k * ‖u‖ * ‖v‖ := by
  exact (norm_inner_le_norm u _).trans (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left (iterate_blocks_norm A hs Omega hfix q hq N hblock v hv k)
        (norm_nonneg u))

end
end UnifiedTheory.Clay.YangMills.TransferPhysicalRatio

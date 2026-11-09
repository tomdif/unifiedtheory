/-
  Microscopic selection after the harmonic chain-collapse obstruction.

  Checked here: every finite probability vector has a scalar complex lift
  with both coherent sum one and the prescribed Born probabilities; a
  centered phase change has only an O(1/K) effect on each probability; and
  the exact ordering-fraction update identifies the relevant geometric drift.

  The causal insertion reference measure and the stochastic limit arguments
  are analytic constructions in MICROSCOPIC_SELECTION_PRINCIPLE.md. They are
  not asserted here as identified Lean causal-trajectory measures.
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornMicroscopicSelection

noncomputable section
open scoped BigOperators

/-- A binary coherent split whose first Born probability is q. Changing
the sign of the imaginary part gives its reflected chirality. -/
def binaryBornSplit (q : ℝ) : ℂ :=
  (q : ℂ) + (Real.sqrt (q * (1 - q)) : ℂ) * Complex.I

theorem binaryBornSplit_normSq {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Complex.normSq (binaryBornSplit q) = q := by
  rw [binaryBornSplit, Complex.normSq_add_mul_I,
    Real.sq_sqrt (mul_nonneg hq (sub_nonneg.mpr hq1))]
  ring

theorem binaryBornSplit_complement_normSq {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Complex.normSq (1 - binaryBornSplit q) = 1 - q := by
  rw [Complex.normSq_sub, binaryBornSplit_normSq hq hq1]
  simp [binaryBornSplit]
  ring

/-- Normalization does not select the Born distribution. Every finite
nonnegative probability vector has a simultaneous coherent/Born lift.
The Fin order is an auxiliary amplitude convention, not a physical law. -/
theorem exists_coherent_prescribed_born :
    ∀ (n : ℕ) (p : Fin (n + 1) → ℝ),
      (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      ∃ b : Fin (n + 1) → ℂ,
        (∑ i, b i) = 1 ∧ ∀ i, Complex.normSq (b i) = p i := by
  intro n
  induction n with
  | zero =>
      intro p _hpos hsum
      refine ⟨fun _ => 1, by simp, ?_⟩
      intro i
      have hi : i = 0 := by omega
      subst i
      simpa using hsum.symm
  | succ n ih =>
      intro p hpos hsum
      have hs : p 0 + ∑ i : Fin (n + 1), p i.succ = 1 := by
        simpa only [Fin.sum_univ_succ] using hsum
      have hq := hpos 0
      have ht : 0 ≤ ∑ i : Fin (n + 1), p i.succ :=
        Finset.sum_nonneg fun i _ => hpos i.succ
      have hq1 : p 0 ≤ 1 := by linarith
      by_cases heq : p 0 = 1
      · have hz : ∑ i : Fin (n + 1), p i.succ = 0 := by linarith
        have htail : ∀ i : Fin (n + 1), p i.succ = 0 := by
          intro i
          have hle := Finset.single_le_sum (fun j _ => hpos j.succ)
            (Finset.mem_univ i)
          rw [hz] at hle
          exact le_antisymm hle (hpos i.succ)
        refine ⟨Fin.cons 1 (fun _ => 0), ?_, ?_⟩
        · rw [Fin.sum_univ_succ]
          simp
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using heq.symm
          · simp [htail]
      · have hd : 0 < 1 - p 0 := by
          have : p 0 < 1 := lt_of_le_of_ne hq1 heq
          linarith
        let tail : Fin (n + 1) → ℝ := fun i => p i.succ / (1 - p 0)
        have htp : ∀ i, 0 ≤ tail i := fun i => div_nonneg (hpos _) hd.le
        have hts : ∑ i, tail i = 1 := by
          simp only [tail, ← Finset.sum_div]
          apply (div_eq_one_iff_eq (ne_of_gt hd)).2
          linarith
        obtain ⟨b, hb, hbp⟩ := ih tail htp hts
        let a := binaryBornSplit (p 0)
        refine ⟨Fin.cons a (fun i => (1 - a) * b i), ?_, ?_⟩
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum, hb, mul_one]
          ring
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact binaryBornSplit_normSq hq hq1
          · simp only [Fin.cons_succ, Complex.normSq_mul, hbp,
              binaryBornSplit_complement_normSq hq hq1, a, tail]
            field_simp

/-- Strictly positive probabilities give full support as well as both
normalizations; zero-free partitions are unnecessary in this construction. -/
theorem exists_biNormalized_fullSupport (n : ℕ) (p : Fin (n + 1) → ℝ)
    (hpos : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    ∃ b : Fin (n + 1) → ℂ,
      (∑ i, b i) = 1 ∧ (∑ i, Complex.normSq (b i)) = 1 ∧
      (∀ i, Complex.normSq (b i) = p i) ∧ (∀ i, b i ≠ 0) := by
  obtain ⟨b, hb, hbp⟩ := exists_coherent_prescribed_born n p
    (fun i => (hpos i).le) hsum
  refine ⟨b, hb, ?_, hbp, ?_⟩
  · simpa only [hbp] using hsum
  · intro i hi
    have := hbp i
    rw [hi, map_zero] at this
    linarith [hpos i]

/-- The phase-dependent part is only the interference with the uniform
center. The squared centered magnitude itself is unchanged. -/
theorem centered_phase_probability_difference (u : ℝ) (z c : ℂ)
    (hz : Complex.normSq z = 1) :
    Complex.normSq ((u : ℂ) + z * c) - Complex.normSq ((u : ℂ) + c) =
      2 * u * ((z - 1) * c).re := by
  simp only [Complex.normSq_add, Complex.normSq_mul, hz, one_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im]
  ring

/-- In a normalized centered shell, |c_i| ≤ 1. With u = 1/K,
no choice of centered phase can change an individual Born probability
by more than 4/K. -/
theorem centered_phase_probability_change_le (u : ℝ) (hu : 0 ≤ u)
    (z c : ℂ) (hz : ‖z‖ = 1) (hc : ‖c‖ ≤ 1) :
    |Complex.normSq ((u : ℂ) + z * c) -
      Complex.normSq ((u : ℂ) + c)| ≤ 4 * u := by
  have hzs : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]
    norm_num
  rw [centered_phase_probability_difference u z c hzs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * u)]
  have hnorm : ‖z - 1‖ ≤ 2 := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [hz]
  have hre : |((z - 1) * c).re| ≤ 2 := by
    calc
      _ ≤ ‖(z - 1) * c‖ := Complex.abs_re_le_norm _
      _ = ‖z - 1‖ * ‖c‖ := norm_mul _ _
      _ ≤ 2 * 1 := mul_le_mul hnorm hc (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  nlinarith

/-- R is the number of existing strict relations, omega is the number
created by the next maximal birth. The same identity holds in conditional
expectation by linearity. -/
theorem ordering_fraction_update (n R omega : ℝ) (hn : 1 < n) :
    (R + omega) / (n * (n + 1) / 2) - R / (n * (n - 1) / 2) =
      2 / (n + 1) * (omega / n - R / (n * (n - 1) / 2)) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  have hnp : n + 1 ≠ 0 := by linarith
  field_simp
  ring

private theorem sum_cut_sizes (n : ℕ) :
    (∑ j : Fin (n + 1), (j.val : ℝ)) = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
      ring

/-- A floor on the probabilities of causal-volume cuts supplies an
extensive lower bound on the mean number of ancestors. -/
theorem expected_ancestors_lower_of_cut_floor (n : ℕ)
    (p : Fin (n + 1) → ℝ) (eta : ℝ)
    (hfloor : ∀ j, eta / (n + 1) ≤ p j) :
    eta * n / 2 ≤ ∑ j, p j * j.val := by
  have hsum :
      ∑ j : Fin (n + 1), eta / (n + 1) * (j.val : ℝ) ≤
        ∑ j, p j * j.val := by
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hfloor j) (by positivity)
  rw [← Finset.mul_sum, sum_cut_sizes] at hsum
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  convert hsum using 1
  field_simp

/-- The same cut floor protects incomparable pairs, rather than just
the frequency of non-timid births. -/
theorem expected_missing_lower_of_cut_floor (n : ℕ)
    (p : Fin (n + 1) → ℝ) (eta : ℝ)
    (hfloor : ∀ j, eta / (n + 1) ≤ p j) :
    eta * n / 2 ≤ ∑ j, p j * ((n : ℝ) - j.val) := by
  have hsum :
      ∑ j : Fin (n + 1), eta / (n + 1) * ((n : ℝ) - j.val) ≤
        ∑ j, p j * ((n : ℝ) - j.val) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right (hfloor j)
    have hj : (j.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
    linarith
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_cut_sizes] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  convert hsum using 1
  field_simp
  ring

#print axioms exists_coherent_prescribed_born
#print axioms exists_biNormalized_fullSupport
#print axioms centered_phase_probability_change_le
#print axioms ordering_fraction_update
#print axioms expected_ancestors_lower_of_cut_floor
#print axioms expected_missing_lower_of_cut_floor

end
end UnifiedTheory.Audit.KFCausalBornMicroscopicSelection

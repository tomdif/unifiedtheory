/-
  Audit/KFOrientationHistoryRigidity.lean

  CLASSIFICATION OF BALANCED TWO-HISTORY DECOHERENCE KERNELS

  The path-quantum audit found two orientation projectors which agree on every
  real route-event measure and differ by an imaginary off-diagonal phase.  This
  file determines whether strong positivity and normalization force the phase.

  They do not.  Every admissible balanced two-history kernel belongs to one
  closed interval.  Its endpoints are exactly the two previously derived
  orientation projectors; equivalently, they are the only pure and
  deterministic-orientation members.  Reflection reverses the interval
  parameter.  Thus kinematics classifies the allowed ambiguity, while a
  refinement law or microscopic dynamics must select an endpoint.
-/

import Mathlib.Analysis.Matrix.PosDef
import UnifiedTheory.Audit.KFOrientationPathQuantum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationHistoryRigidity

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationPathQuantum

/-! ## 1. The balanced one-parameter family -/

/-- A balanced two-history kernel.  The diagonal route weights are `1/2`,
and `y` is the imaginary coherence in the `(0,1)` entry. -/
def balancedHistoryKernel (y : ℝ) : SquareMatrix 2 :=
  !![(1 / 2 : ℂ), Complex.I * (y : ℂ);
     -Complex.I * (y : ℂ), 1 / 2]

/-- Strong positivity, equal singleton weights, and normalized total event.
Hermiticity follows from positive semidefiniteness. -/
def IsAdmissibleBalancedKernel (rho : SquareMatrix 2) : Prop :=
  rho.PosSemidef
    ∧ rho 0 0 = 1 / 2
    ∧ rho 1 1 = 1 / 2
    ∧ pathHistoryMeasure rho Finset.univ = 1

theorem balancedHistoryKernel_negativeEndpoint :
    balancedHistoryKernel (-1 / 2) = positiveOrientationProjector := by
  rw [positiveOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedHistoryKernel, Fin.ext_iff] <;> ring

theorem balancedHistoryKernel_positiveEndpoint :
    balancedHistoryKernel (1 / 2) = negativeOrientationProjector := by
  rw [negativeOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedHistoryKernel, Fin.ext_iff] <;> ring

/-- Every balanced kernel is the affine mixture of the two orientation
projectors with weights `1/2-y` and `1/2+y`. -/
theorem balancedHistoryKernel_projector_mixture (y : ℝ) :
    balancedHistoryKernel y =
      (1 / 2 - y) • positiveOrientationProjector +
        (1 / 2 + y) • negativeOrientationProjector := by
  rw [positiveOrientationProjector_exact,
    negativeOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedHistoryKernel, Fin.ext_iff] <;> ring

theorem balancedHistoryKernel_isPathDensity
    {y : ℝ} (hy : |y| ≤ 1 / 2) :
    IsPathDensity (balancedHistoryKernel y) := by
  have hy' := (abs_le.mp hy)
  have hPlus : 0 ≤ (1 / 2 - y : ℝ) := by linarith
  have hMinus : 0 ≤ (1 / 2 + y : ℝ) := by linarith
  have hPos : (balancedHistoryKernel y).PosSemidef := by
    rw [balancedHistoryKernel_projector_mixture]
    exact (positiveOrientationProjector_isPathDensity.2.1.smul hPlus).add
      (negativeOrientationProjector_isPathDensity.2.1.smul hMinus)
  refine ⟨hPos.isHermitian, hPos, ?_⟩
  norm_num [Matrix.trace, balancedHistoryKernel, Fin.sum_univ_succ,
    Fin.ext_iff]

theorem balancedHistoryKernel_total_measure (y : ℝ) :
    pathHistoryMeasure (balancedHistoryKernel y) Finset.univ = 1 := by
  norm_num [pathHistoryMeasure, pathHistoryKernel,
    balancedHistoryKernel, Fin.sum_univ_succ, Fin.ext_iff]

/-- Every member of the admissible interval has the same complete real kernel
on the route-event algebra.  The parameter is invisible to all real `Z`-sector
event measures, not to curvature-basis measurements. -/
theorem balancedHistoryKernel_same_real_history_kernel
    (y z : ℝ) (p q : Fin 2) :
    (pathHistoryKernel (balancedHistoryKernel y) p q).re =
      (pathHistoryKernel (balancedHistoryKernel z) p q).re := by
  fin_cases p <;> fin_cases q <;>
    norm_num [pathHistoryKernel, balancedHistoryKernel, Fin.ext_iff]

theorem balancedHistoryKernel_same_history_measure
    (y z : ℝ) (event : Finset (Fin 2)) :
    pathHistoryMeasure (balancedHistoryKernel y) event =
      pathHistoryMeasure (balancedHistoryKernel z) event := by
  unfold pathHistoryMeasure
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact balancedHistoryKernel_same_real_history_kernel y z p q

/-- Route dephasing collapses the complete interval to the same maximally mixed
state, not only the two pure endpoints. -/
theorem pathDephase_balancedHistoryKernel (y : ℝ) :
    pathDephase (balancedHistoryKernel y) = (1 / 2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathDephase, balancedHistoryKernel, Fin.ext_iff]

theorem balancedHistoryKernel_admissible
    {y : ℝ} (hy : |y| ≤ 1 / 2) :
    IsAdmissibleBalancedKernel (balancedHistoryKernel y) := by
  exact ⟨(balancedHistoryKernel_isPathDensity hy).2.1,
    by norm_num [balancedHistoryKernel, Fin.ext_iff],
    by norm_num [balancedHistoryKernel, Fin.ext_iff],
    balancedHistoryKernel_total_measure y⟩

/-! ## 2. Classification from strong positivity -/

/-- A Hermitian balanced normalized kernel has purely imaginary coherence. -/
theorem balanced_normalization_forces_imaginary_coherence
    {rho : SquareMatrix 2}
    (hHerm : rho.IsHermitian)
    (h00 : rho 0 0 = 1 / 2)
    (h11 : rho 1 1 = 1 / 2)
    (hTotal : pathHistoryMeasure rho Finset.univ = 1) :
    (rho 0 1).re = 0 := by
  have hStar := hHerm.apply 0 1
  have hRe : (rho 1 0).re = (rho 0 1).re := by
    calc
      (rho 1 0).re = (star (rho 1 0)).re := by simp
      _ = (rho 0 1).re := congrArg Complex.re hStar
  norm_num [pathHistoryMeasure, pathHistoryKernel,
    Fin.sum_univ_succ, Fin.ext_iff, h00, h11] at hTotal
  linarith

/-- Every strongly positive balanced normalized two-history kernel is exactly
one member of the imaginary-coherence family, and positivity bounds the
parameter by `1/2`. -/
theorem admissibleBalancedKernel_classification
    {rho : SquareMatrix 2} (h : IsAdmissibleBalancedKernel rho) :
    ∃ y : ℝ, |y| ≤ 1 / 2 ∧ rho = balancedHistoryKernel y := by
  rcases h with ⟨hPos, h00, h11, hTotal⟩
  let y : ℝ := (rho 0 1).im
  have hRe : (rho 0 1).re = 0 :=
    balanced_normalization_forces_imaginary_coherence
      hPos.isHermitian h00 h11 hTotal
  have h01 : rho 0 1 = Complex.I * (y : ℂ) := by
    apply Complex.ext
    · simpa [y] using hRe
    · simp [y]
  have hStar := hPos.isHermitian.apply 1 0
  have h10 : rho 1 0 = -Complex.I * (y : ℂ) := by
    rw [← hStar]
    rw [h01]
    apply Complex.ext <;> simp [y]
  have hrho : rho = balancedHistoryKernel y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [balancedHistoryKernel, h00, h11, h01, h10]
  have hdet := hPos.det_nonneg
  rw [hrho, Matrix.det_fin_two] at hdet
  have hdetRe := (Complex.nonneg_iff.mp hdet).1
  norm_num [balancedHistoryKernel, Fin.ext_iff, Complex.I_sq] at hdetRe
  refine ⟨y, ?_, hrho⟩
  rw [abs_le]
  constructor <;> nlinarith

/-- Exact classification: admissibility is equivalent to membership in the
closed imaginary-coherence interval. -/
theorem admissibleBalancedKernel_iff
    (rho : SquareMatrix 2) :
    IsAdmissibleBalancedKernel rho ↔
      ∃ y : ℝ, |y| ≤ 1 / 2 ∧ rho = balancedHistoryKernel y := by
  constructor
  · exact admissibleBalancedKernel_classification
  · rintro ⟨y, hy, rfl⟩
    exact balancedHistoryKernel_admissible hy

theorem balancedHistoryKernel_injective :
    Function.Injective balancedHistoryKernel := by
  intro y z h
  have h01 := congrFun (congrFun h 0) 1
  have him := congrArg Complex.im h01
  norm_num [balancedHistoryKernel, Fin.ext_iff] at him
  exact him

/-- The parameter of an admissible balanced kernel is unique. -/
theorem admissibleBalancedKernel_unique_parameter
    {rho : SquareMatrix 2} (h : IsAdmissibleBalancedKernel rho) :
    ∃! y : ℝ, |y| ≤ 1 / 2 ∧ rho = balancedHistoryKernel y := by
  obtain ⟨y, hy, hrho⟩ := admissibleBalancedKernel_classification h
  refine ⟨y, ⟨hy, hrho⟩, ?_⟩
  intro z hz
  apply balancedHistoryKernel_injective
  rw [← hrho, ← hz.2]

/-- The balanced family respects arbitrary affine combinations. -/
theorem balancedHistoryKernel_affine (a b t : ℝ) :
    balancedHistoryKernel (t * a + (1 - t) * b) =
      t • balancedHistoryKernel a + (1 - t) • balancedHistoryKernel b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedHistoryKernel, Fin.ext_iff] <;> ring

/-- Scalar extremality in the closed admissible interval. -/
def IsConvexExtremeOrientationParameter (y : ℝ) : Prop :=
  |y| ≤ 1 / 2
    ∧ ∀ a b t : ℝ,
      |a| ≤ 1 / 2 → |b| ≤ 1 / 2 →
      0 < t → t < 1 →
      y = t * a + (1 - t) * b →
      a = y ∧ b = y

theorem convexExtremeOrientationParameter_iff (y : ℝ) :
    IsConvexExtremeOrientationParameter y ↔
      y = -1 / 2 ∨ y = 1 / 2 := by
  constructor
  · rintro ⟨hy, hExtreme⟩
    by_cases hNeg : y = -1 / 2
    · exact Or.inl hNeg
    by_cases hPos : y = 1 / 2
    · exact Or.inr hPos
    have hyBounds := abs_le.mp hy
    have hyLower : -(1 / 2 : ℝ) < y :=
      lt_of_le_of_ne hyBounds.1 (by
        intro hEq
        apply hNeg
        linarith)
    have hyUpper : y < 1 / 2 :=
      lt_of_le_of_ne hyBounds.2 hPos
    have hEnds := hExtreme (-1 / 2) (1 / 2) (1 / 2 - y)
      (by norm_num) (by norm_num) (by linarith) (by linarith) (by ring)
    exact (hNeg hEnds.1.symm).elim
  · rintro (rfl | rfl)
    · refine ⟨by norm_num, ?_⟩
      intro a b t ha hb ht0 ht1 hEq
      have haLower := (abs_le.mp ha).1
      have hbLower := (abs_le.mp hb).1
      have hta : 0 ≤ t * (a + 1 / 2) :=
        mul_nonneg (le_of_lt ht0) (by linarith)
      have htb : 0 ≤ (1 - t) * (b + 1 / 2) :=
        mul_nonneg (by linarith) (by linarith)
      have hsum : t * (a + 1 / 2) +
          (1 - t) * (b + 1 / 2) = 0 := by
        nlinarith [hEq]
      have hta0 : t * (a + 1 / 2) = 0 := by nlinarith
      have htb0 : (1 - t) * (b + 1 / 2) = 0 := by nlinarith
      constructor
      · rcases mul_eq_zero.mp hta0 with ht | ha0
        · exfalso; nlinarith
        · linarith
      · rcases mul_eq_zero.mp htb0 with ht | hb0
        · exfalso; nlinarith
        · linarith
    · refine ⟨by norm_num, ?_⟩
      intro a b t ha hb ht0 ht1 hEq
      have haUpper := (abs_le.mp ha).2
      have hbUpper := (abs_le.mp hb).2
      have hta : 0 ≤ t * (1 / 2 - a) :=
        mul_nonneg (le_of_lt ht0) (by linarith)
      have htb : 0 ≤ (1 - t) * (1 / 2 - b) :=
        mul_nonneg (by linarith) (by linarith)
      have hsum : t * (1 / 2 - a) +
          (1 - t) * (1 / 2 - b) = 0 := by
        nlinarith [hEq]
      have hta0 : t * (1 / 2 - a) = 0 := by nlinarith
      have htb0 : (1 - t) * (1 / 2 - b) = 0 := by nlinarith
      constructor
      · rcases mul_eq_zero.mp hta0 with ht | ha0
        · exfalso; nlinarith
        · linarith
      · rcases mul_eq_zero.mp htb0 with ht | hb0
        · exfalso; nlinarith
        · linarith

/-- Matrix-level convex extremality inside the classified balanced family. -/
def IsConvexExtremeBalancedKernel (y : ℝ) : Prop :=
  |y| ≤ 1 / 2
    ∧ ∀ a b t : ℝ,
      |a| ≤ 1 / 2 → |b| ≤ 1 / 2 →
      0 < t → t < 1 →
      balancedHistoryKernel y =
        t • balancedHistoryKernel a + (1 - t) • balancedHistoryKernel b →
      a = y ∧ b = y

theorem convexExtremeBalancedKernel_iff_parameter (y : ℝ) :
    IsConvexExtremeBalancedKernel y ↔
      IsConvexExtremeOrientationParameter y := by
  constructor
  · rintro ⟨hy, hMatrix⟩
    refine ⟨hy, ?_⟩
    intro a b t ha hb ht0 ht1 hParam
    apply hMatrix a b t ha hb ht0 ht1
    rw [hParam]
    exact balancedHistoryKernel_affine a b t
  · rintro ⟨hy, hParam⟩
    refine ⟨hy, ?_⟩
    intro a b t ha hb ht0 ht1 hMatrix
    apply hParam a b t ha hb ht0 ht1
    apply balancedHistoryKernel_injective
    exact hMatrix.trans (balancedHistoryKernel_affine a b t).symm

/-- The two curvature projectors are exactly the convex extreme points of the
complete strongly positive balanced-kernel family. -/
theorem convexExtremeBalancedKernel_iff (y : ℝ) :
    IsConvexExtremeBalancedKernel y ↔
      y = -1 / 2 ∨ y = 1 / 2 :=
  (convexExtremeBalancedKernel_iff_parameter y).trans
    (convexExtremeOrientationParameter_iff y)

/-! ## 3. Reflection and the endpoint sectors -/

/-- Reflection on the ordered history kernel.  For a Hermitian kernel this is
equivalently entrywise complex conjugation. -/
def pathHistoryReflection (rho : SquareMatrix 2) : SquareMatrix 2 :=
  rhoᵀ

theorem pathHistoryReflection_balancedHistoryKernel (y : ℝ) :
    pathHistoryReflection (balancedHistoryKernel y) =
      balancedHistoryKernel (-y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathHistoryReflection, balancedHistoryKernel,
      Matrix.transpose_apply, Fin.ext_iff]

theorem pathHistoryReflection_swaps_endpoints :
    pathHistoryReflection positiveOrientationProjector =
        negativeOrientationProjector
      ∧ pathHistoryReflection negativeOrientationProjector =
        positiveOrientationProjector := by
  constructor
  · rw [← balancedHistoryKernel_negativeEndpoint,
      pathHistoryReflection_balancedHistoryKernel]
    norm_num [balancedHistoryKernel_positiveEndpoint]
  · rw [← balancedHistoryKernel_positiveEndpoint,
      pathHistoryReflection_balancedHistoryKernel]
    rw [show -(1 / 2 : ℝ) = -1 / 2 by ring,
      balancedHistoryKernel_negativeEndpoint]

/-- The independently derived cubic chirality signs select the two endpoints
of the complete strongly positive balanced-kernel interval. -/
theorem relational_chirality_selects_extremal_history_kernels :
    chiralitySelectedProjector 1 1 1 2 2 2 2 1 1 =
        balancedHistoryKernel (-1 / 2)
      ∧ chiralitySelectedProjector 1 1 1 2 2 2 1 1 2 =
        balancedHistoryKernel (1 / 2) := by
  exact ⟨chiralitySelectedProjector_witness.trans
      balancedHistoryKernel_negativeEndpoint.symm,
    chiralitySelectedProjector_reflected_witness.trans
      balancedHistoryKernel_positiveEndpoint.symm⟩

/-- Selection by either member of the independently constructed reflected
cubic-chirality witness pair. -/
def IsChiralitySelectedHistoryKernel (rho : SquareMatrix 2) : Prop :=
  rho = chiralitySelectedProjector 1 1 1 2 2 2 2 1 1
    ∨ rho = chiralitySelectedProjector 1 1 1 2 2 2 1 1 2

theorem balancedHistoryKernel_chiralitySelected_iff (y : ℝ) :
    IsChiralitySelectedHistoryKernel (balancedHistoryKernel y) ↔
      y = -1 / 2 ∨ y = 1 / 2 := by
  constructor
  · rintro (h | h)
    · left
      apply balancedHistoryKernel_injective
      exact h.trans
        relational_chirality_selects_extremal_history_kernels.1
    · right
      apply balancedHistoryKernel_injective
      exact h.trans
        relational_chirality_selects_extremal_history_kernels.2
  · rintro (rfl | rfl)
    · exact Or.inl
        relational_chirality_selects_extremal_history_kernels.1.symm
    · exact Or.inr
        relational_chirality_selects_extremal_history_kernels.2.symm

/-! ## 4. Purity and deterministic orientation select only the endpoints -/

theorem balancedHistoryKernel_positive_bornWeight (y : ℝ) :
    bornWeight (balancedHistoryKernel y) positiveOrientationProjector =
      1 / 2 - y := by
  rw [positiveOrientationProjector_exact]
  norm_num [bornWeight, balancedHistoryKernel, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, Fin.ext_iff,
    Complex.I_sq]
  ring

theorem balancedHistoryKernel_negative_bornWeight (y : ℝ) :
    bornWeight (balancedHistoryKernel y) negativeOrientationProjector =
      1 / 2 + y := by
  rw [negativeOrientationProjector_exact]
  norm_num [bornWeight, balancedHistoryKernel, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, Fin.ext_iff,
    Complex.I_sq]
  ring

/-- The curvature-basis Born weight is a complete operational coordinate on
the interval.  Unlike route-event data, it distinguishes every value of `y`. -/
theorem balancedHistoryKernel_curvature_bornWeight_injective (y z : ℝ) :
    bornWeight (balancedHistoryKernel y) positiveOrientationProjector =
        bornWeight (balancedHistoryKernel z) positiveOrientationProjector
      ↔ y = z := by
  rw [balancedHistoryKernel_positive_bornWeight,
    balancedHistoryKernel_positive_bornWeight]
  constructor <;> intro h <;> linarith

theorem balancedHistoryKernel_deterministic_iff (y : ℝ) :
    (bornWeight (balancedHistoryKernel y) positiveOrientationProjector = 1
        ∨ bornWeight (balancedHistoryKernel y)
          negativeOrientationProjector = 1)
      ↔ y = -1 / 2 ∨ y = 1 / 2 := by
  rw [balancedHistoryKernel_positive_bornWeight,
    balancedHistoryKernel_negative_bornWeight]
  constructor <;> rintro (h | h)
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith

/-- Idempotence is the finite density-matrix purity condition.  In the full
admissible interval it holds exactly at the two maximally coherent endpoints. -/
theorem balancedHistoryKernel_pure_iff (y : ℝ) :
    balancedHistoryKernel y * balancedHistoryKernel y =
        balancedHistoryKernel y
      ↔ y = -1 / 2 ∨ y = 1 / 2 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h00re := congrArg Complex.re h00
    norm_num [balancedHistoryKernel, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff, Complex.I_sq] at h00re
    have hySq : y * y = (1 / 2 : ℝ) * (1 / 2) := by nlinarith
    rcases (mul_self_eq_mul_self_iff.mp hySq) with hy | hy
    · right; exact hy
    · left; linarith
  · rintro (rfl | rfl)
    · rw [balancedHistoryKernel_negativeEndpoint,
        positiveOrientationProjector_idempotent]
    · rw [balancedHistoryKernel_positiveEndpoint,
        negativeOrientationProjector_idempotent]

/-- Purity, deterministic curvature sign, and endpoint saturation are exactly
equivalent for every admissible balanced history kernel. -/
theorem balancedHistoryKernel_endpoint_equivalences
    {y : ℝ} (hy : |y| ≤ 1 / 2) :
    IsAdmissibleBalancedKernel (balancedHistoryKernel y)
      ∧ ((balancedHistoryKernel y * balancedHistoryKernel y =
            balancedHistoryKernel y)
          ↔ (bornWeight (balancedHistoryKernel y)
                positiveOrientationProjector = 1
            ∨ bornWeight (balancedHistoryKernel y)
                negativeOrientationProjector = 1))
      ∧ ((balancedHistoryKernel y * balancedHistoryKernel y =
            balancedHistoryKernel y)
          ↔ y = -1 / 2 ∨ y = 1 / 2) := by
  exact ⟨balancedHistoryKernel_admissible hy,
    balancedHistoryKernel_pure_iff y |>.trans
      (balancedHistoryKernel_deterministic_iff y).symm,
    balancedHistoryKernel_pure_iff y⟩

/-- Four independent endpoint criteria coincide: algebraic purity,
convex-geometric extremality, operationally deterministic curvature, and
selection by the reflected cubic-chirality witness pair. -/
theorem balancedHistoryKernel_four_way_endpoint_selection
    (y : ℝ) :
    ((balancedHistoryKernel y * balancedHistoryKernel y =
          balancedHistoryKernel y)
        ↔ IsConvexExtremeBalancedKernel y)
      ∧ ((balancedHistoryKernel y * balancedHistoryKernel y =
            balancedHistoryKernel y)
        ↔ (bornWeight (balancedHistoryKernel y)
              positiveOrientationProjector = 1
          ∨ bornWeight (balancedHistoryKernel y)
              negativeOrientationProjector = 1))
      ∧ ((balancedHistoryKernel y * balancedHistoryKernel y =
            balancedHistoryKernel y)
        ↔ IsChiralitySelectedHistoryKernel (balancedHistoryKernel y))
      ∧ ((balancedHistoryKernel y * balancedHistoryKernel y =
            balancedHistoryKernel y)
        ↔ y = -1 / 2 ∨ y = 1 / 2) := by
  exact ⟨(balancedHistoryKernel_pure_iff y).trans
      (convexExtremeBalancedKernel_iff y).symm,
    (balancedHistoryKernel_pure_iff y).trans
      (balancedHistoryKernel_deterministic_iff y).symm,
    (balancedHistoryKernel_pure_iff y).trans
      (balancedHistoryKernel_chiralitySelected_iff y).symm,
    balancedHistoryKernel_pure_iff y⟩

/-- The center of the admissible interval is a concrete counterexample to
kinematic phase uniqueness: it is strongly positive and normalized but is
neither orientation projector. -/
theorem strong_positivity_does_not_select_orientation :
    IsAdmissibleBalancedKernel (balancedHistoryKernel 0)
      ∧ balancedHistoryKernel 0 ≠ positiveOrientationProjector
      ∧ balancedHistoryKernel 0 ≠ negativeOrientationProjector := by
  refine ⟨balancedHistoryKernel_admissible (by norm_num), ?_, ?_⟩
  · intro h
    have : (0 : ℝ) = -1 / 2 := balancedHistoryKernel_injective
      (h.trans balancedHistoryKernel_negativeEndpoint.symm)
    norm_num at this
  · intro h
    have : (0 : ℝ) = 1 / 2 := balancedHistoryKernel_injective
      (h.trans balancedHistoryKernel_positiveEndpoint.symm)
    norm_num at this

/-- Kinematic underdetermination is route-operational: every parameter has the
same real `Z`-sector event measures and dephased state.  The following curvature
coordinate remains injective, so this is not full operational equivalence. -/
theorem balancedHistoryKernel_route_operational_indistinguishability
    (y z : ℝ) :
    (∀ event : Finset (Fin 2),
      pathHistoryMeasure (balancedHistoryKernel y) event =
        pathHistoryMeasure (balancedHistoryKernel z) event)
      ∧ pathDephase (balancedHistoryKernel y) =
          pathDephase (balancedHistoryKernel z)
      ∧ (bornWeight (balancedHistoryKernel y)
              positiveOrientationProjector =
            bornWeight (balancedHistoryKernel z)
              positiveOrientationProjector ↔ y = z) := by
  exact ⟨balancedHistoryKernel_same_history_measure y z,
    (pathDephase_balancedHistoryKernel y).trans
      (pathDephase_balancedHistoryKernel z).symm,
    balancedHistoryKernel_curvature_bornWeight_injective y z⟩

/-- Final rigidity boundary: the kinematic axioms determine a unique interval
parameter but do not select its value; adding purity or deterministic
orientation reduces the interval to the reflected endpoint pair. -/
theorem balanced_history_rigidity_boundary :
    (∀ rho : SquareMatrix 2,
      IsAdmissibleBalancedKernel rho →
        ∃! y : ℝ, |y| ≤ 1 / 2 ∧ rho = balancedHistoryKernel y)
      ∧ (∀ y : ℝ,
        balancedHistoryKernel y * balancedHistoryKernel y =
            balancedHistoryKernel y
          ↔ y = -1 / 2 ∨ y = 1 / 2)
      ∧ (∀ y : ℝ, IsConvexExtremeBalancedKernel y ↔
          y = -1 / 2 ∨ y = 1 / 2)
      ∧ pathHistoryReflection positiveOrientationProjector =
          negativeOrientationProjector
      ∧ chiralitySelectedProjector 1 1 1 2 2 2 2 1 1 =
          balancedHistoryKernel (-1 / 2)
      ∧ chiralitySelectedProjector 1 1 1 2 2 2 1 1 2 =
          balancedHistoryKernel (1 / 2)
      ∧ IsAdmissibleBalancedKernel (balancedHistoryKernel 0) := by
  exact ⟨fun rho h => admissibleBalancedKernel_unique_parameter h,
    balancedHistoryKernel_pure_iff,
    convexExtremeBalancedKernel_iff,
    pathHistoryReflection_swaps_endpoints.1,
    relational_chirality_selects_extremal_history_kernels.1,
    relational_chirality_selects_extremal_history_kernels.2,
    strong_positivity_does_not_select_orientation.1⟩

#print axioms admissibleBalancedKernel_iff
#print axioms admissibleBalancedKernel_unique_parameter
#print axioms convexExtremeBalancedKernel_iff
#print axioms relational_chirality_selects_extremal_history_kernels
#print axioms balancedHistoryKernel_endpoint_equivalences
#print axioms balancedHistoryKernel_four_way_endpoint_selection
#print axioms strong_positivity_does_not_select_orientation
#print axioms balancedHistoryKernel_route_operational_indistinguishability
#print axioms balanced_history_rigidity_boundary

end

end UnifiedTheory.Audit.KFOrientationHistoryRigidity

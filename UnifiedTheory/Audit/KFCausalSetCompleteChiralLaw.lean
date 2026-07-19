/-
  Audit/KFCausalSetCompleteChiralLaw.lean

  A ZERO-FREE INTERACTING CHIRAL GROWTH LAW

  The independently multiplicative quarter-turn character has an exact
  finite zero, so it cannot be normalized at every causal-set parent without
  a fallback.  This file replaces independent composition by a quadratic
  signature-local interaction that is invisible for zero or one ancestor:

      A(omega,m) = lambda^(omega (omega - 1)) (±i)^m.

  The new exponent counts ordered pairs of distinct ancestors.  At the
  elementary one-event parent it vanishes, so the already-derived chiral
  endpoint is unchanged.  At higher rank it prevents exact cancellation
  when lambda is transcendental.  Indeed, the real part of every finite
  parent partition is an integer polynomial in lambda whose constant
  coefficient is exactly one.  Choosing the canonical base-two Liouville
  number therefore gives a nonzero partition at every finite rank and hence
  a normalized, strongly positive projective growth law with no fallback.

  The exponent is twice `choose omega 2`, so the law only sees the effective
  unordered-pair coupling `g = lambda^2`; `lambda` and `-lambda` are exactly
  the same law, while `g` is identifiable at the two-ancestor signature.
  All-rank normalizability still does not select `g`: the sparse `g = 0` law
  is also zero-free and induces the same depth-two orientation endpoint.
  Full raw support excludes precisely this degenerate candidate, but does not
  restore uniqueness: `lambda + 1` is a second positive transcendental,
  full-support, zero-free, strongly-positive law with the same endpoint.
  A microscopic principle is still required to select the nonzero value.
-/

import UnifiedTheory.Audit.KFCausalSetChiralDynamics
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw

noncomputable section

open scoped BigOperators ComplexConjugate
open Polynomial
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetOrientationRestriction
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

/-! ## 1. The minimal ancestor-pair interaction -/

/-- Ordered pairs of distinct ancestors.  This is zero exactly at ancestor
counts zero and one, so the elementary chiral birth is untouched. -/
def ancestorPairExponent (omega : ℕ) : ℕ := omega * (omega - 1)

/-- The physically distinct, unordered pairs among the ancestors. -/
def ancestorUnorderedPairCount (omega : ℕ) : ℕ := omega.choose 2

/-- The ordered-pair exponent is exactly twice the unordered-pair count.
Consequently the real coupling can enter the law only through its square. -/
theorem ancestorPairExponent_eq_twice_unordered (omega : ℕ) :
    ancestorPairExponent omega = 2 * ancestorUnorderedPairCount omega := by
  rw [ancestorUnorderedPairCount, Nat.choose_two_right,
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self omega)]
  rfl

/-- Exact Gaussian implementation of the two conjugate quarter-turn powers. -/
def chiralGaussianPower (chirality : Fin 2) (m : ℕ) : ℂ :=
  if chirality = 0 then gaussianToComplex (gaussianIPow m)
  else conj (gaussianToComplex (gaussianIPow m))

@[simp]
theorem chiralGaussianPower_re (chirality : Fin 2) (m : ℕ) :
    (chiralGaussianPower chirality m).re = (gaussianIPow m).1 := by
  simp only [chiralGaussianPower]
  split_ifs <;> simp [gaussianToComplex, Complex.mul_re]

theorem chiralGaussianPower_eq_phase_pow (chirality : Fin 2) (m : ℕ) :
    chiralGaussianPower chirality m =
      chiralMaximalEventPhase chirality ^ m := by
  fin_cases chirality <;>
    simp [chiralGaussianPower, chiralMaximalEventPhase,
      gaussianToComplex_gaussianIPow, map_pow]

/-- Signature-local interacting amplitude.  `lambda` couples to ancestor
pairs and the independent sign couples to maximal precursor events. -/
def interactingChiralSignatureWeight (lambda : ℝ) (chirality : Fin 2) :
    ℕ → ℕ → ℂ :=
  fun omega maximal =>
    (lambda : ℂ) ^ ancestorPairExponent omega *
      chiralGaussianPower chirality maximal

/-- The coupling visible to the dynamics.  The sign of the original
square-root parameter `lambda` is redundant. -/
def effectivePairCoupling (lambda : ℝ) : ℝ := lambda ^ 2

/-- Equivalent parametrization by one coupling per unordered ancestor pair. -/
def effectivePairChiralSignatureWeight (g : ℝ) (chirality : Fin 2) :
    ℕ → ℕ → ℂ :=
  fun omega maximal =>
    (g : ℂ) ^ ancestorUnorderedPairCount omega *
      chiralGaussianPower chirality maximal

/-- Exact factorization through the effective pair coupling `g = lambda²`. -/
theorem interactingChiralSignatureWeight_factors_effective
    (lambda : ℝ) (chirality : Fin 2) :
    interactingChiralSignatureWeight lambda chirality =
      effectivePairChiralSignatureWeight
        (effectivePairCoupling lambda) chirality := by
  funext omega maximal
  rw [interactingChiralSignatureWeight,
    effectivePairChiralSignatureWeight, effectivePairCoupling,
    ancestorPairExponent_eq_twice_unordered, pow_mul]
  norm_cast

/-- The sign of the square-root coupling is an exact microscopic gauge
redundancy, not a second physical branch. -/
theorem interactingChiralSignatureWeight_neg
    (lambda : ℝ) (chirality : Fin 2) :
    interactingChiralSignatureWeight (-lambda) chirality =
      interactingChiralSignatureWeight lambda chirality := by
  rw [interactingChiralSignatureWeight_factors_effective,
    interactingChiralSignatureWeight_factors_effective]
  simp [effectivePairCoupling]

/-- The effective coupling itself is identifiable: the two-ancestor,
zero-maximal signature already reads off `g` exactly. -/
theorem effectivePairChiralSignatureWeight_injective (chirality : Fin 2) :
    Function.Injective
      (fun g : ℝ => effectivePairChiralSignatureWeight g chirality) := by
  intro g₁ g₂ hWeights
  have hAtTwo := congrFun (congrFun hWeights 2) 0
  have hComplex : (g₁ : ℂ) = (g₂ : ℂ) := by
    simpa [effectivePairChiralSignatureWeight,
      ancestorUnorderedPairCount,
      chiralGaussianPower_eq_phase_pow] using hAtTwo
  exact_mod_cast hComplex

/-- Complete identifiability classification for the original real
parameter: two values give the same all-signature law iff they differ only
by the square-root sign. -/
theorem interactingChiralSignatureWeight_eq_iff
    (lambda₁ lambda₂ : ℝ) (chirality : Fin 2) :
    interactingChiralSignatureWeight lambda₁ chirality =
        interactingChiralSignatureWeight lambda₂ chirality ↔
      lambda₁ = lambda₂ ∨ lambda₁ = -lambda₂ := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · intro hWeights
    apply effectivePairChiralSignatureWeight_injective chirality
    exact
      (interactingChiralSignatureWeight_factors_effective
          lambda₁ chirality).symm.trans
        (hWeights.trans
          (interactingChiralSignatureWeight_factors_effective
            lambda₂ chirality))
  · intro hSquares
    have hEffective :
        effectivePairCoupling lambda₁ = effectivePairCoupling lambda₂ := by
      simpa [effectivePairCoupling] using hSquares
    exact
      (interactingChiralSignatureWeight_factors_effective
          lambda₁ chirality).trans
        ((congrArg
          (fun g : ℝ => effectivePairChiralSignatureWeight g chirality)
          hEffective).trans
        (interactingChiralSignatureWeight_factors_effective
          lambda₂ chirality).symm)

/-- No locally allowed signature is assigned zero raw amplitude. -/
def HasFullRawSignatureSupport (weight : ℕ → ℕ → ℂ) : Prop :=
  ∀ omega maximal, weight omega maximal ≠ 0

/-- Full raw support excludes exactly the degenerate zero coupling. -/
theorem interactingChiralSignatureWeight_fullSupport_iff
    (lambda : ℝ) (chirality : Fin 2) :
    HasFullRawSignatureSupport
        (interactingChiralSignatureWeight lambda chirality) ↔
      lambda ≠ 0 := by
  constructor
  · intro hSupport hZero
    subst lambda
    have hAtTwo := hSupport 2 0
    norm_num [interactingChiralSignatureWeight, ancestorPairExponent,
      chiralGaussianPower_eq_phase_pow] at hAtTwo
  · intro hLambda omega maximal
    apply mul_ne_zero
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hLambda)
    · rw [chiralGaussianPower_eq_phase_pow]
      apply pow_ne_zero
      fin_cases chirality <;>
        simp [chiralMaximalEventPhase]

/-- Raw covariant causal-edge law before normalization. -/
def interactingChiralCausalEdgeAmplitude (lambda : ℝ) (chirality : Fin 2) :
    CovariantComplexCausalEdgeAmplitude :=
  rideoutSorkinSignatureAmplitude
    (interactingChiralSignatureWeight lambda chirality)

theorem interactingChiralAmplitude_isBellCausal
    (lambda : ℝ) (chirality : Fin 2) :
    IsCanonicallyBellCausal
      (interactingChiralCausalEdgeAmplitude lambda chirality) :=
  rideoutSorkinSignatureAmplitude_canonicalBellCausal _

/-- The interaction begins beyond the elementary birth: the zero-ancestor
amplitude is one and the one-ancestor/one-maximal amplitude is exactly the
selected quarter turn. -/
theorem interactingChiralSignatureWeight_elementary
    (lambda : ℝ) (chirality : Fin 2) :
    interactingChiralSignatureWeight lambda chirality 0 0 = 1 ∧
      interactingChiralSignatureWeight lambda chirality 1 1 =
        chiralMaximalEventPhase chirality := by
  constructor <;>
    simp [interactingChiralSignatureWeight, ancestorPairExponent,
      chiralGaussianPower_eq_phase_pow]

/-- The pair interaction has an exact cross term under independent signature
composition.  This is the controlled replacement for the character law that
the zero-partition obstruction ruled out. -/
theorem ancestorPairExponent_add (omega₁ omega₂ : ℕ) :
    ancestorPairExponent (omega₁ + omega₂) =
      ancestorPairExponent omega₁ + ancestorPairExponent omega₂ +
        2 * omega₁ * omega₂ := by
  cases omega₁ with
  | zero => simp [ancestorPairExponent]
  | succ omega₁ =>
      cases omega₂ with
      | zero => simp [ancestorPairExponent]
      | succ omega₂ =>
          simp [ancestorPairExponent]
          ring

/-- Unordered pairs split into internal pairs and one cross pair for every
choice of an ancestor from each component. -/
theorem ancestorUnorderedPairCount_add (omega₁ omega₂ : ℕ) :
    ancestorUnorderedPairCount (omega₁ + omega₂) =
      ancestorUnorderedPairCount omega₁ +
        ancestorUnorderedPairCount omega₂ + omega₁ * omega₂ := by
  have hAdd := ancestorPairExponent_add omega₁ omega₂
  rw [ancestorPairExponent_eq_twice_unordered,
    ancestorPairExponent_eq_twice_unordered,
    ancestorPairExponent_eq_twice_unordered] at hAdd
  refine Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) ?_
  calc
    2 * ancestorUnorderedPairCount (omega₁ + omega₂) =
        2 * ancestorUnorderedPairCount omega₁ +
          2 * ancestorUnorderedPairCount omega₂ +
            2 * omega₁ * omega₂ := hAdd
    _ = 2 * (ancestorUnorderedPairCount omega₁ +
          ancestorUnorderedPairCount omega₂ + omega₁ * omega₂) := by
      ring

/-- Raising the ancestor count by one adds exactly `2*omega` to the ordered
pair exponent.  This is the finite source of the large-rank coupling flow. -/
theorem ancestorPairExponent_succ (omega : ℕ) :
    ancestorPairExponent (omega + 1) =
      ancestorPairExponent omega + 2 * omega := by
  simpa [ancestorPairExponent] using ancestorPairExponent_add omega 1

theorem ancestorUnorderedPairCount_succ (omega : ℕ) :
    ancestorUnorderedPairCount (omega + 1) =
      ancestorUnorderedPairCount omega + omega := by
  simpa [ancestorUnorderedPairCount] using
    ancestorUnorderedPairCount_add omega 1

theorem interactingChiralSignatureWeight_composition_defect
    (lambda : ℝ) (chirality : Fin 2)
    (omega₁ maximal₁ omega₂ maximal₂ : ℕ) :
    interactingChiralSignatureWeight lambda chirality
        (omega₁ + omega₂) (maximal₁ + maximal₂) =
      interactingChiralSignatureWeight lambda chirality omega₁ maximal₁ *
        interactingChiralSignatureWeight lambda chirality omega₂ maximal₂ *
        (lambda : ℂ) ^ (2 * omega₁ * omega₂) := by
  simp only [interactingChiralSignatureWeight,
    ancestorPairExponent_add, pow_add,
    chiralGaussianPower_eq_phase_pow]
  ring

/-- In the identifiable parametrization the composition defect has one factor
of `g` for each cross-component ancestor pair. -/
theorem effectivePairChiralSignatureWeight_composition_defect
    (g : ℝ) (chirality : Fin 2)
    (omega₁ maximal₁ omega₂ maximal₂ : ℕ) :
    effectivePairChiralSignatureWeight g chirality
        (omega₁ + omega₂) (maximal₁ + maximal₂) =
      effectivePairChiralSignatureWeight g chirality omega₁ maximal₁ *
        effectivePairChiralSignatureWeight g chirality omega₂ maximal₂ *
        (g : ℂ) ^ (omega₁ * omega₂) := by
  simp only [effectivePairChiralSignatureWeight,
    ancestorUnorderedPairCount_add, pow_add,
    chiralGaussianPower_eq_phase_pow]
  ring

/-- Adding a one-ancestor chiral component multiplies the effective amplitude
by `g^omega`.  A fixed `g>1` amplifies this factor with rank, while `g<1`
suppresses it; a nontrivial large-rank balance therefore requires running
`g` toward one. -/
theorem effectivePairChiralSignatureWeight_append_singleton
    (g : ℝ) (chirality : Fin 2) (omega maximal : ℕ) :
    effectivePairChiralSignatureWeight g chirality
        (omega + 1) (maximal + 1) =
      effectivePairChiralSignatureWeight g chirality omega maximal *
        chiralMaximalEventPhase chirality * (g : ℂ) ^ omega := by
  simpa [effectivePairChiralSignatureWeight,
    ancestorUnorderedPairCount, chiralGaussianPower_eq_phase_pow] using
    effectivePairChiralSignatureWeight_composition_defect
      g chirality omega maximal 1 1

/-! ## 2. The integer parent-partition polynomial -/

/-- The real parent partition before evaluation at the pair coupling. -/
def interactingChiralRealPartitionPolynomial {n : ℕ}
    (parent : CardinalCausalOrder n) : ℤ[X] :=
  ∑ past : CausalPastSet parent,
    C (gaussianIPow past.maximalCount).1 *
      X ^ ancestorPairExponent past.ancestorCount

@[simp]
theorem emptyCausalPastSet_ancestorCount {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (emptyCausalPastSet parent).ancestorCount = 0 := by
  unfold CausalPastSet.ancestorCount
  simp [emptyCausalPastSet]

@[simp]
theorem emptyCausalPastSet_maximalCount {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (emptyCausalPastSet parent).maximalCount = 0 := by
  unfold CausalPastSet.maximalCount
  simp [CausalPastSet.IsMaximal, emptyCausalPastSet]

theorem ancestorCount_eq_zero_iff_empty {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    past.ancestorCount = 0 ↔ past = emptyCausalPastSet parent := by
  constructor
  · intro hZero
    have hEmpty : IsEmpty {i : Fin n // past.mem i = true} := by
      apply Finite.card_eq_zero_iff.mp
      simpa [CausalPastSet.ancestorCount] using hZero
    letI : IsEmpty {i : Fin n // past.mem i = true} := hEmpty
    apply CausalPastSet.ext
    funext i
    cases hMem : past.mem i with
    | false => rfl
    | true =>
        let selected : {j : Fin n // past.mem j = true} := ⟨i, hMem⟩
        exact isEmptyElim selected
  · rintro rfl
    exact emptyCausalPastSet_ancestorCount parent

theorem maximalCount_eq_one_of_ancestorCount_eq_one {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent)
    (hOne : past.ancestorCount = 1) :
    past.maximalCount = 1 := by
  have hSupport := Nat.card_eq_one_iff_unique.mp hOne
  letI : Subsingleton {i : Fin n // past.mem i = true} := hSupport.1
  unfold CausalPastSet.maximalCount
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro first second
    apply Subtype.ext
    have hSupportEqual := Subsingleton.elim
        (⟨first.val, first.property.1⟩ : {i : Fin n // past.mem i = true})
        (⟨second.val, second.property.1⟩ : {i : Fin n // past.mem i = true})
    exact congrArg (fun x : {i : Fin n // past.mem i = true} => x.val)
      hSupportEqual
  · obtain ⟨chosen⟩ := hSupport.2
    refine ⟨⟨chosen.val, chosen.property, ?_⟩⟩
    intro j hj _hRel
    exact congrArg Subtype.val
      (Subsingleton.elim
        (⟨j, hj⟩ : {i : Fin n // past.mem i = true}) chosen)

/-- Every nonempty precursor contributes zero to the polynomial's constant
coefficient: one ancestor contributes a purely imaginary quarter turn, and
two or more ancestors carry a positive power of `X`. -/
theorem interactingChiralRealPartitionPolynomial_coeff_zero {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (interactingChiralRealPartitionPolynomial parent).coeff 0 = 1 := by
  classical
  unfold interactingChiralRealPartitionPolynomial
  change (Polynomial.lcoeff ℤ 0)
    (∑ past : CausalPastSet parent,
      C (gaussianIPow past.maximalCount).1 *
        X ^ ancestorPairExponent past.ancestorCount) = 1
  rw [map_sum]
  calc
    (∑ past : CausalPastSet parent,
        (Polynomial.lcoeff ℤ 0)
          (C (gaussianIPow past.maximalCount).1 *
            X ^ ancestorPairExponent past.ancestorCount)) =
        (Polynomial.lcoeff ℤ 0)
          (C (gaussianIPow (emptyCausalPastSet parent).maximalCount).1 *
            X ^ ancestorPairExponent
              (emptyCausalPastSet parent).ancestorCount) := by
      apply Fintype.sum_eq_single
      intro past hPast
      change (C (gaussianIPow past.maximalCount).1 *
        X ^ ancestorPairExponent past.ancestorCount).coeff 0 = 0
      rw [coeff_C_mul_X_pow]
      by_cases hExponent : 0 = ancestorPairExponent past.ancestorCount
      · rw [if_pos hExponent]
        have hNonzero : past.ancestorCount ≠ 0 := by
          intro hZero
          apply hPast
          exact (ancestorCount_eq_zero_iff_empty past).mp hZero
        have hOne : past.ancestorCount = 1 := by
          unfold ancestorPairExponent at hExponent
          rcases Nat.mul_eq_zero.mp hExponent.symm with hZero | hPredZero
          · exact (hNonzero hZero).elim
          · omega
        rw [maximalCount_eq_one_of_ancestorCount_eq_one past hOne]
        rfl
      · rw [if_neg hExponent]
    _ = 1 := by simp [ancestorPairExponent, gaussianIPow]

theorem interactingChiralRealPartitionPolynomial_ne_zero {n : ℕ}
    (parent : CardinalCausalOrder n) :
    interactingChiralRealPartitionPolynomial parent ≠ 0 := by
  intro hZero
  have := congrArg (fun p : ℤ[X] => p.coeff 0) hZero
  change (interactingChiralRealPartitionPolynomial parent).coeff 0 = 0 at this
  rw [interactingChiralRealPartitionPolynomial_coeff_zero] at this
  norm_num at this

theorem interactingChiralSignatureWeight_re
    (lambda : ℝ) (chirality : Fin 2) (omega maximal : ℕ) :
    (interactingChiralSignatureWeight lambda chirality omega maximal).re =
      lambda ^ ancestorPairExponent omega *
        ((gaussianIPow maximal).1 : ℝ) := by
  rw [show interactingChiralSignatureWeight lambda chirality omega maximal =
      (lambda : ℂ) ^ ancestorPairExponent omega *
        chiralGaussianPower chirality maximal by rfl]
  have hRealPow : ((lambda : ℂ) ^ ancestorPairExponent omega).re =
      lambda ^ ancestorPairExponent omega := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hImagPow : ((lambda : ℂ) ^ ancestorPairExponent omega).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  rw [Complex.mul_re, hRealPow, hImagPow, chiralGaussianPower_re]
  simp

/-- The real part of the causal partition is evaluation of the integer
polynomial associated with the parent. -/
theorem interactingChiral_partition_re_eq_polynomial_eval {n : ℕ}
    (lambda : ℝ) (chirality : Fin 2) (parent : CardinalCausalOrder n) :
    (causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude lambda chirality) parent).re =
      (interactingChiralRealPartitionPolynomial parent).eval₂
        (Int.castRingHom ℝ) lambda := by
  classical
  unfold causalEdgeAmplitudePartition
  change Complex.reAddGroupHom
      (∑ past : CausalPastSet parent,
        (interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
          parent past) = _
  rw [map_sum]
  change (∑ past : CausalPastSet parent,
    ((interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
      parent past).re) = _
  simp only [
    interactingChiralCausalEdgeAmplitude, rideoutSorkinSignatureAmplitude,
    interactingChiralSignatureWeight_re]
  unfold interactingChiralRealPartitionPolynomial
  change (∑ past : CausalPastSet parent,
      lambda ^ ancestorPairExponent past.ancestorCount *
        ((gaussianIPow past.maximalCount).1 : ℝ)) =
    (Polynomial.eval₂RingHom (Int.castRingHom ℝ) lambda)
      (∑ past : CausalPastSet parent,
        C (gaussianIPow past.maximalCount).1 *
          X ^ ancestorPairExponent past.ancestorCount)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro past _hPast
  simp only [map_mul]
  have hCoefficient :
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) lambda)
          (C (gaussianIPow past.maximalCount).1) =
        ((gaussianIPow past.maximalCount).1 : ℝ) := by
    change Polynomial.eval₂ (Int.castRingHom ℝ) lambda
      (C (gaussianIPow past.maximalCount).1) = _
    rw [eval₂_C]
    rfl
  have hPower :
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) lambda)
          (X ^ ancestorPairExponent past.ancestorCount) =
        lambda ^ ancestorPairExponent past.ancestorCount := by
    change Polynomial.eval₂ (Int.castRingHom ℝ) lambda
      (X ^ ancestorPairExponent past.ancestorCount) = _
    simp
  rw [hCoefficient, hPower]
  change lambda ^ ancestorPairExponent past.ancestorCount *
      ((gaussianIPow past.maximalCount).1 : ℝ) =
    ((gaussianIPow past.maximalCount).1 : ℝ) *
      lambda ^ ancestorPairExponent past.ancestorCount
  ring

/-- Transcendence is sufficient but not necessary for all-rank
normalizability.  At zero coupling every multi-ancestor transition is
removed, while the empty precursor contributes real part one and every
one-ancestor contribution is purely imaginary. -/
theorem zeroCoupling_interactingChiral_partition_re {n : ℕ}
    (chirality : Fin 2) (parent : CardinalCausalOrder n) :
    (causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude 0 chirality) parent).re = 1 := by
  rw [interactingChiral_partition_re_eq_polynomial_eval]
  simp [interactingChiralRealPartitionPolynomial_coeff_zero]

/-- The degenerate zero-coupling law is nevertheless normalizable at every
finite causal parent. -/
theorem zeroCoupling_interactingChiral_partition_ne_zero {n : ℕ}
    (chirality : Fin 2) (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude 0 chirality) parent ≠ 0 := by
  intro hZero
  have hReal := congrArg Complex.re hZero
  rw [zeroCoupling_interactingChiral_partition_re] at hReal
  norm_num at hReal

/-! ## 3. A canonical all-rank zero-free coupling -/

/-- A concrete fixed transcendental pair coupling already present in mathlib. -/
def canonicalPairCoupling : ℝ := liouvilleNumber 2

theorem canonicalPairCoupling_transcendental :
    Transcendental ℤ canonicalPairCoupling := by
  simpa [canonicalPairCoupling] using
    (transcendental_liouvilleNumber (m := 2) (by norm_num))

theorem canonicalPairCoupling_ne_zero : canonicalPairCoupling ≠ 0 := by
  intro hZero
  apply canonicalPairCoupling_transcendental
  rw [hZero]
  exact isAlgebraic_zero

theorem canonicalPairCoupling_pos : 0 < canonicalPairCoupling := by
  rw [canonicalPairCoupling,
    ← LiouvilleNumber.partialSum_add_remainder
      (m := (2 : ℝ)) (by norm_num) 0]
  have hRemainder :=
    LiouvilleNumber.remainder_pos (m := (2 : ℝ)) (by norm_num) 0
  have hPartial : 0 < LiouvilleNumber.partialSum (2 : ℝ) 0 := by
    norm_num [LiouvilleNumber.partialSum]
  nlinarith

theorem canonicalPairCoupling_gt_one : 1 < canonicalPairCoupling := by
  rw [canonicalPairCoupling,
    ← LiouvilleNumber.partialSum_add_remainder
      (m := (2 : ℝ)) (by norm_num) 1]
  have hRemainder :=
    LiouvilleNumber.remainder_pos (m := (2 : ℝ)) (by norm_num) 1
  have hPartial : LiouvilleNumber.partialSum (2 : ℝ) 1 = 1 := by
    norm_num [LiouvilleNumber.partialSum, Finset.sum_range_succ,
      Nat.factorial]
  nlinarith

theorem canonicalPairCoupling_lt_two : canonicalPairCoupling < 2 := by
  rw [canonicalPairCoupling,
    ← LiouvilleNumber.partialSum_add_remainder
      (m := (2 : ℝ)) (by norm_num) 1]
  have hRemainder :=
    LiouvilleNumber.remainder_lt 1 (m := (2 : ℝ)) (by norm_num)
  have hPartial : LiouvilleNumber.partialSum (2 : ℝ) 1 = 1 := by
    norm_num [LiouvilleNumber.partialSum, Finset.sum_range_succ,
      Nat.factorial]
  norm_num at hRemainder
  nlinarith

/-- A concrete transcendental coupling in the subcritical interval `(0,1)`. -/
def subcriticalPairCoupling : ℝ := canonicalPairCoupling - 1

theorem subcriticalPairCoupling_transcendental :
    Transcendental ℤ subcriticalPairCoupling := by
  let p : ℤ[X] := Polynomial.X + Polynomial.C (-1)
  have h := canonicalPairCoupling_transcendental.aeval
    p (by
      rw [show p = Polynomial.X + Polynomial.C (-1) by rfl,
        Polynomial.natDegree_X_add_C]
      norm_num)
      (by
        rw [show p = Polynomial.X + Polynomial.C (-1) by rfl,
          Polynomial.leadingCoeff_X_add_C]
        simp)
  simpa [p, subcriticalPairCoupling, sub_eq_add_neg] using h

theorem subcriticalPairCoupling_mem_unitInterval :
    0 < subcriticalPairCoupling ∧ subcriticalPairCoupling < 1 := by
  unfold subcriticalPairCoupling
  constructor <;>
    nlinarith [canonicalPairCoupling_gt_one, canonicalPairCoupling_lt_two]

theorem subcriticalPairCoupling_ne_zero : subcriticalPairCoupling ≠ 0 :=
  ne_of_gt subcriticalPairCoupling_mem_unitInterval.1

/-- A second explicit nonzero transcendental coupling.  It will witness that
even full support and all-rank normalizability do not select a unique law. -/
def shiftedPairCoupling : ℝ := canonicalPairCoupling + 1

theorem shiftedPairCoupling_transcendental :
    Transcendental ℤ shiftedPairCoupling := by
  let p : ℤ[X] := Polynomial.X + Polynomial.C 1
  have h := canonicalPairCoupling_transcendental.aeval
    p (by
      rw [show p = Polynomial.X + Polynomial.C 1 by rfl,
        Polynomial.natDegree_X_add_C]
      norm_num)
      (by
        rw [show p = Polynomial.X + Polynomial.C 1 by rfl,
          Polynomial.leadingCoeff_X_add_C]
        simp)
  simpa [p, shiftedPairCoupling] using h

theorem shiftedPairCoupling_pos : 0 < shiftedPairCoupling := by
  unfold shiftedPairCoupling
  nlinarith [canonicalPairCoupling_pos]

theorem shiftedPairCoupling_ne_zero : shiftedPairCoupling ≠ 0 :=
  ne_of_gt shiftedPairCoupling_pos

theorem canonicalInteractingChiralWeight_fullSupport
    (chirality : Fin 2) :
    HasFullRawSignatureSupport
      (interactingChiralSignatureWeight canonicalPairCoupling chirality) :=
  (interactingChiralSignatureWeight_fullSupport_iff _ _).mpr
    canonicalPairCoupling_ne_zero

theorem shiftedInteractingChiralWeight_fullSupport
    (chirality : Fin 2) :
    HasFullRawSignatureSupport
      (interactingChiralSignatureWeight shiftedPairCoupling chirality) :=
  (interactingChiralSignatureWeight_fullSupport_iff _ _).mpr
    shiftedPairCoupling_ne_zero

theorem subcriticalInteractingChiralWeight_fullSupport
    (chirality : Fin 2) :
    HasFullRawSignatureSupport
      (interactingChiralSignatureWeight subcriticalPairCoupling chirality) :=
  (interactingChiralSignatureWeight_fullSupport_iff _ _).mpr
    subcriticalPairCoupling_ne_zero

/-- The two full-support couplings give genuinely different all-signature
laws, not representatives of the square-root sign redundancy. -/
theorem canonical_and_shifted_signatureWeights_distinct
    (chirality : Fin 2) :
    interactingChiralSignatureWeight canonicalPairCoupling chirality ≠
      interactingChiralSignatureWeight shiftedPairCoupling chirality := by
  intro hWeights
  rcases (interactingChiralSignatureWeight_eq_iff
      canonicalPairCoupling shiftedPairCoupling chirality).mp hWeights with
      hEqual | hNegative
  · unfold shiftedPairCoupling at hEqual
    linarith
  · have hShiftedPositive := shiftedPairCoupling_pos
    nlinarith [canonicalPairCoupling_pos]

/-- Kinematics plus all-rank normalizability do not uniquely select the
interaction: the canonical full-support law and the zero-coupling sparse law
are distinct, while both have nonzero parent partitions at every rank. -/
theorem canonical_and_zeroCoupling_signatureWeights_distinct
    (chirality : Fin 2) :
    interactingChiralSignatureWeight canonicalPairCoupling chirality ≠
      interactingChiralSignatureWeight 0 chirality := by
  intro hWeights
  rcases (interactingChiralSignatureWeight_eq_iff
      canonicalPairCoupling 0 chirality).mp hWeights with hZero | hNegZero
  · exact canonicalPairCoupling_ne_zero hZero
  · apply canonicalPairCoupling_ne_zero
    simpa using hNegZero

theorem canonicalPairCoupling_sq_ne_one : canonicalPairCoupling ^ 2 ≠ 1 := by
  intro hSquare
  let obstruction : ℤ[X] := X ^ 2 - 1
  have hEvaluation : Polynomial.aeval canonicalPairCoupling obstruction = 0 := by
    simp [obstruction, hSquare]
  have hPolynomialZero :=
    (transcendental_iff.mp canonicalPairCoupling_transcendental)
      obstruction hEvaluation
  have hCoefficient := congrArg (fun p : ℤ[X] => p.coeff 2) hPolynomialZero
  norm_num [obstruction, Polynomial.coeff_one] at hCoefficient

/-- The canonical repair is genuinely interacting rather than a disguised
independent-composition character. -/
theorem canonicalInteractingChiralWeight_not_multiplicative
    (chirality : Fin 2) :
    ¬ IsMultiplicativeSignatureWeight
      (interactingChiralSignatureWeight canonicalPairCoupling chirality) := by
  intro hMultiplicative
  have hCompose := hMultiplicative.2 1 0 1 0
  have hComplexSquare :
      (canonicalPairCoupling : ℂ) ^ 2 = 1 := by
    simpa [interactingChiralSignatureWeight, ancestorPairExponent,
      chiralGaussianPower_eq_phase_pow] using hCompose
  have hRealSquare := congrArg Complex.re hComplexSquare
  apply canonicalPairCoupling_sq_ne_one
  simpa [← Complex.ofReal_pow] using hRealSquare

/-- Any real coupling transcendental over the integers makes every finite
causal parent partition nonzero. -/
theorem interactingChiral_partition_ne_zero_of_transcendental
    {lambda : ℝ} (hTranscendental : Transcendental ℤ lambda)
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude lambda chirality) parent ≠ 0 := by
  intro hZero
  have hRealZero := congrArg Complex.re hZero
  rw [interactingChiral_partition_re_eq_polynomial_eval] at hRealZero
  have hPolynomialZero :
      interactingChiralRealPartitionPolynomial parent = 0 :=
    (transcendental_iff.mp hTranscendental)
      (interactingChiralRealPartitionPolynomial parent) (by
        simpa [Polynomial.aeval_def] using hRealZero)
  exact interactingChiralRealPartitionPolynomial_ne_zero parent hPolynomialZero

theorem canonical_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
      parent ≠ 0 :=
  interactingChiral_partition_ne_zero_of_transcendental
    canonicalPairCoupling_transcendental chirality parent

theorem shifted_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude shiftedPairCoupling chirality)
      parent ≠ 0 :=
  interactingChiral_partition_ne_zero_of_transcendental
    shiftedPairCoupling_transcendental chirality parent

/-- The explicit subcritical test coupling is also full-support and zero-free
at every finite parent.  This separates all-rank normalizability from the
large-rank sparse-flow behavior diagnosed by the generalization audit. -/
theorem subcritical_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ} (parent : CardinalCausalOrder n) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude subcriticalPairCoupling chirality)
      parent ≠ 0 :=
  interactingChiral_partition_ne_zero_of_transcendental
    subcriticalPairCoupling_transcendental chirality parent

/-- The former 14-event destructive-zero benchmark is repaired for both
chiralities without invoking totalization. -/
theorem canonical_interactingChiral_obstruction_partition_ne_zero
    (chirality : Fin 2) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
      chainEightBelowAntichainSix ≠ 0 :=
  canonical_interactingChiral_partition_ne_zero
    chirality chainEightBelowAntichainSix

/-! ## 4. The normalized all-depth law, with no exceptional branch -/

theorem zeroCoupling_unlabeled_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude 0 chirality) parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact zeroCoupling_interactingChiral_partition_ne_zero
    chirality parentRepresentative

theorem shifted_unlabeled_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude shiftedPairCoupling chirality)
      parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact shifted_interactingChiral_partition_ne_zero
    chirality parentRepresentative

/-- A second full-support, zero-free, normalized all-depth law. -/
def shiftedChiralCausalSetGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  totalizedCausalEdgeGrowthLaw
    (interactingChiralCausalEdgeAmplitude shiftedPairCoupling chirality)

theorem shiftedChiralCausalSetGrowthLaw_transition_eq_direct
    (chirality : Fin 2) {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (shiftedChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child =
      unlabeledAggregatedCausalEdgeAmplitude
          (interactingChiralCausalEdgeAmplitude shiftedPairCoupling chirality)
          (currentUnlabeledCausalOrder n pathPrefix) child /
        unlabeledCausalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude shiftedPairCoupling chirality)
          (currentUnlabeledCausalOrder n pathPrefix) := by
  simp [shiftedChiralCausalSetGrowthLaw, totalizedCausalEdgeGrowthLaw,
    totalizedNormalizedCausalEdgeAmplitude,
    shifted_unlabeled_interactingChiral_partition_ne_zero]

theorem shiftedChiralCausalSetGrowthLaw_stronglyPositive
    (chirality : Fin 2) :
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (shiftedChiralCausalSetGrowthLaw chirality)) :=
  infiniteRankedCylinderDecoherence_stronglyPositive _

/-- A second all-depth normalized candidate.  It is sparse rather than
full-support: births with two or more ancestors have zero raw amplitude. -/
def sparseChiralCausalSetGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  totalizedCausalEdgeGrowthLaw
    (interactingChiralCausalEdgeAmplitude 0 chirality)

/-- Although defined through the general totalized constructor, the sparse
law never reaches its exceptional uniform branch. -/
theorem sparseChiralCausalSetGrowthLaw_transition_eq_direct
    (chirality : Fin 2) {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (sparseChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child =
      unlabeledAggregatedCausalEdgeAmplitude
          (interactingChiralCausalEdgeAmplitude 0 chirality)
          (currentUnlabeledCausalOrder n pathPrefix) child /
        unlabeledCausalEdgeAmplitudePartition
          (interactingChiralCausalEdgeAmplitude 0 chirality)
          (currentUnlabeledCausalOrder n pathPrefix) := by
  simp [sparseChiralCausalSetGrowthLaw, totalizedCausalEdgeGrowthLaw,
    totalizedNormalizedCausalEdgeAmplitude,
    zeroCoupling_unlabeled_interactingChiral_partition_ne_zero]

theorem sparseChiralCausalSetGrowthLaw_stronglyPositive
    (chirality : Fin 2) :
    IsStronglyPositiveGrowthFunctional
      (infiniteRankedCylinderDecoherence
        (sparseChiralCausalSetGrowthLaw chirality)) :=
  infiniteRankedCylinderDecoherence_stronglyPositive _

theorem canonical_unlabeled_interactingChiral_partition_ne_zero
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
      parent ≠ 0 := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact canonical_interactingChiral_partition_ne_zero
    chirality parentRepresentative

/-- Coherently aggregate raw transition slots and divide by the now-proved
nonzero parent partition.  Unlike the former chiral law, this definition has
no uniform exceptional branch. -/
def canonicalInteractingChiralTransition
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) : ℂ :=
  unlabeledAggregatedCausalEdgeAmplitude
      (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
      parent child /
    unlabeledCausalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
      parent

theorem canonicalInteractingChiralTransition_sum_one
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    ∑ child : UnlabeledCardinalCausalOrder (n + 1),
      canonicalInteractingChiralTransition chirality parent child = 1 := by
  classical
  simp only [canonicalInteractingChiralTransition, ← Finset.sum_div]
  rw [sum_unlabeledAggregatedCausalEdgeAmplitude,
    div_self (canonical_unlabeled_interactingChiral_partition_ne_zero
      chirality parent)]

/-- The complete normalized causal growth law selected by one chirality. -/
def completeChiralCausalSetGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := fun n pathPrefix child =>
    canonicalInteractingChiralTransition chirality
      (currentUnlabeledCausalOrder n pathPrefix) child
  normalized := fun _n pathPrefix =>
    canonicalInteractingChiralTransition_sum_one chirality
      (currentUnlabeledCausalOrder _ pathPrefix)

/-- The universal sequential-growth machinery now supplies normalized,
projectively consistent, strongly positive decoherence functionals on all
finite depths and on the infinite unlabeled cylinder algebra. -/
theorem completeChiralLaw_projective_stronglyPositive
    (chirality : Fin 2) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (completeChiralCausalSetGrowthLaw chirality) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                (completeChiralCausalSetGrowthLaw chirality) (n + 1))
              (refineRankedGrowthEvent event₁)
              (refineRankedGrowthEvent event₂) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                (completeChiralCausalSetGrowthLaw chirality) n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (completeChiralCausalSetGrowthLaw chirality))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (completeChiralCausalSetGrowthLaw chirality))
      ∧ infiniteRankedCylinderDecoherence
          (completeChiralCausalSetGrowthLaw chirality)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 :=
  normalized_stronglyPositive_infiniteRankedCylinder_family
    (completeChiralCausalSetGrowthLaw chirality)

/-! ## 5. Recovery of the finite orientation endpoint -/

theorem interacting_rankOne_amplitude_eq_chiral
    (lambda : ℝ) (chirality : Fin 2)
    (past : CausalPastSet (cardinalCausalAntichain 1)) :
    (interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
        (cardinalCausalAntichain 1) past =
      (chiralCausalEdgeAmplitude chirality).amplitude
        (cardinalCausalAntichain 1) past := by
  rcases rankOneCausalPast_cases past with hEmpty | hFull
  · subst past
    simp [interactingChiralCausalEdgeAmplitude,
      interactingChiralSignatureWeight, rideoutSorkinSignatureAmplitude,
      chiralCausalEdgeAmplitude, chiralMultiplicativeSignatureWeight,
      multiplicativeSignatureWeight, ancestorPairExponent,
      chiralGaussianPower_eq_phase_pow]
  · subst past
    simp [interactingChiralCausalEdgeAmplitude,
      interactingChiralSignatureWeight, rideoutSorkinSignatureAmplitude,
      chiralCausalEdgeAmplitude, chiralMultiplicativeSignatureWeight,
      multiplicativeSignatureWeight, ancestorPairExponent,
      chiralGaussianPower_eq_phase_pow]

theorem interacting_rankOne_partition_eq_chiral
    (lambda : ℝ) (chirality : Fin 2) :
    causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        (cardinalCausalAntichain 1) =
      causalEdgeAmplitudePartition (chiralCausalEdgeAmplitude chirality)
        (cardinalCausalAntichain 1) := by
  classical
  unfold causalEdgeAmplitudePartition
  apply Finset.sum_congr rfl
  intro past _hPast
  exact interacting_rankOne_amplitude_eq_chiral lambda chirality past

theorem interacting_rankOne_aggregate_eq_chiral
    (lambda : ℝ) (chirality : Fin 2)
    (child : UnlabeledCardinalCausalOrder 2) :
    labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        (cardinalCausalAntichain 1) child =
      labeledAggregatedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality)
        (cardinalCausalAntichain 1) child := by
  classical
  unfold labeledAggregatedCausalEdgeAmplitude
  apply Finset.sum_congr rfl
  intro past _hPast
  exact interacting_rankOne_amplitude_eq_chiral lambda chirality past.val

theorem completeChiral_rankOne_transition_eq_chiral
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1) :
    (completeChiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child =
      (chiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child := by
  unfold completeChiralCausalSetGrowthLaw
  change canonicalInteractingChiralTransition chirality
      (currentUnlabeledCausalOrder 1 pathPrefix) child = _
  dsimp only [chiralCausalSetGrowthLaw, totalizedCausalEdgeGrowthLaw]
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  unfold canonicalInteractingChiralTransition
  rw [unlabeledAggregatedCausalEdgeAmplitude_mk,
    unlabeledCausalEdgeAmplitudePartition_mk,
    interacting_rankOne_aggregate_eq_chiral canonicalPairCoupling,
    interacting_rankOne_partition_eq_chiral canonicalPairCoupling]
  have hNonzero := chiral_rankOne_partition_ne_zero chirality
  simp [totalizedNormalizedCausalEdgeAmplitude, hNonzero]

/-- The sparse zero-coupling completion has the same first nontrivial
transition as the canonical completion and the original chiral character. -/
theorem sparseChiral_rankOne_transition_eq_chiral
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1) :
    (sparseChiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child =
      (chiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child := by
  dsimp only [sparseChiralCausalSetGrowthLaw, chiralCausalSetGrowthLaw,
    totalizedCausalEdgeGrowthLaw]
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  simp only [totalizedNormalizedCausalEdgeAmplitude,
    unlabeledCausalEdgeAmplitudePartition_mk,
    unlabeledAggregatedCausalEdgeAmplitude_mk,
    interacting_rankOne_partition_eq_chiral 0,
    interacting_rankOne_aggregate_eq_chiral 0]

theorem shiftedChiral_rankOne_transition_eq_chiral
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (child : CausalSetGrowthBranch 1) :
    (shiftedChiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child =
      (chiralCausalSetGrowthLaw chirality).transition
        1 pathPrefix child := by
  dsimp only [shiftedChiralCausalSetGrowthLaw, chiralCausalSetGrowthLaw,
    totalizedCausalEdgeGrowthLaw]
  rw [unlabeledCardinalCausalOrder_one_unique
    (currentUnlabeledCausalOrder 1 pathPrefix)]
  simp only [totalizedNormalizedCausalEdgeAmplitude,
    unlabeledCausalEdgeAmplitudePartition_mk,
    unlabeledAggregatedCausalEdgeAmplitude_mk,
    interacting_rankOne_partition_eq_chiral shiftedPairCoupling,
    interacting_rankOne_aggregate_eq_chiral shiftedPairCoupling]

theorem causalGrowth_depthOne_path_amplitude_one
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (path : RankedGrowthPath CausalSetGrowthBranch 1) :
    finiteRankedPathAmplitude law 1 path = 1 := by
  rcases path with ⟨root, child⟩
  have hNormalized := law.normalized 0 root
  have hSingle :
      (∑ branch : CausalSetGrowthBranch 0,
        law.transition 0 root branch) = law.transition 0 root child := by
    apply Fintype.sum_eq_single
    intro other hOther
    exact (hOther (unlabeledCardinalCausalOrder_one_unique other |>.trans
      (unlabeledCardinalCausalOrder_one_unique child).symm)).elim
  rw [hSingle] at hNormalized
  simpa [finiteRankedPathAmplitude] using hNormalized

theorem completeChiral_depthTwo_pathAmplitude_eq_chiral
    (chirality : Fin 2)
    (path : RankedGrowthPath CausalSetGrowthBranch 2) :
    finiteRankedPathAmplitude (completeChiralCausalSetGrowthLaw chirality)
        2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path := by
  rcases path with ⟨pathPrefix, child⟩
  rw [finiteRankedPathAmplitude_snoc, finiteRankedPathAmplitude_snoc,
    causalGrowth_depthOne_path_amplitude_one,
    causalGrowth_depthOne_path_amplitude_one,
    one_mul, one_mul,
    completeChiral_rankOne_transition_eq_chiral]

theorem sparseChiral_depthTwo_pathAmplitude_eq_chiral
    (chirality : Fin 2)
    (path : RankedGrowthPath CausalSetGrowthBranch 2) :
    finiteRankedPathAmplitude (sparseChiralCausalSetGrowthLaw chirality)
        2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path := by
  rcases path with ⟨pathPrefix, child⟩
  rw [finiteRankedPathAmplitude_snoc, finiteRankedPathAmplitude_snoc,
    causalGrowth_depthOne_path_amplitude_one,
    causalGrowth_depthOne_path_amplitude_one,
    one_mul, one_mul,
    sparseChiral_rankOne_transition_eq_chiral]

theorem shiftedChiral_depthTwo_pathAmplitude_eq_chiral
    (chirality : Fin 2)
    (path : RankedGrowthPath CausalSetGrowthBranch 2) :
    finiteRankedPathAmplitude (shiftedChiralCausalSetGrowthLaw chirality)
        2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path := by
  rcases path with ⟨pathPrefix, child⟩
  rw [finiteRankedPathAmplitude_snoc, finiteRankedPathAmplitude_snoc,
    causalGrowth_depthOne_path_amplitude_one,
    causalGrowth_depthOne_path_amplitude_one,
    one_mul, one_mul,
    shiftedChiral_rankOne_transition_eq_chiral]

theorem completeChiral_inducedOrientationKernel_exact (chirality : Fin 2) :
    inducedOrientationKernel (completeChiralCausalSetGrowthLaw chirality)
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel
        (chiralBoundaryOrientationParameter chirality) := by
  rw [← chiral_inducedOrientationKernel_exact chirality]
  ext first second
  unfold inducedOrientationKernel finiteRankedDepthDecoherence
  simp only [amplitude_growthEventDecoherence_eq]
  have hSectorAmplitude (orientation : Fin 2) :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining.depth path) =
      ∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude
          (chiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining.depth path := by
    apply Finset.sum_congr rfl
    intro path _hPath
    change finiteRankedPathAmplitude
        (completeChiralCausalSetGrowthLaw chirality) 2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path
    exact completeChiral_depthTwo_pathAmplitude_eq_chiral chirality path
  rw [hSectorAmplitude first, hSectorAmplitude second]

/-- The sparse and canonical all-depth completions are invisible to the
depth-two orientation experiment: both induce the same pure endpoint. -/
theorem sparseChiral_inducedOrientationKernel_exact (chirality : Fin 2) :
    inducedOrientationKernel (sparseChiralCausalSetGrowthLaw chirality)
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel
        (chiralBoundaryOrientationParameter chirality) := by
  rw [← chiral_inducedOrientationKernel_exact chirality]
  ext first second
  unfold inducedOrientationKernel finiteRankedDepthDecoherence
  simp only [amplitude_growthEventDecoherence_eq]
  have hSectorAmplitude (orientation : Fin 2) :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude
          (sparseChiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining.depth path) =
      ∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude
          (chiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining.depth path := by
    apply Finset.sum_congr rfl
    intro path _hPath
    change finiteRankedPathAmplitude
        (sparseChiralCausalSetGrowthLaw chirality) 2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path
    exact sparseChiral_depthTwo_pathAmplitude_eq_chiral chirality path
  rw [hSectorAmplitude first, hSectorAmplitude second]

/-- Even full support, all-rank zero-freeness, strong positivity, and the
pure depth-two endpoint leave more than one effective pair coupling. -/
theorem shiftedChiral_inducedOrientationKernel_exact (chirality : Fin 2) :
    inducedOrientationKernel (shiftedChiralCausalSetGrowthLaw chirality)
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel
        (chiralBoundaryOrientationParameter chirality) := by
  rw [← chiral_inducedOrientationKernel_exact chirality]
  ext first second
  unfold inducedOrientationKernel finiteRankedDepthDecoherence
  simp only [amplitude_growthEventDecoherence_eq]
  have hSectorAmplitude (orientation : Fin 2) :
      (∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude
          (shiftedChiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining.depth path) =
      ∑ path ∈ chiralRankTwoCoarseGraining.sector orientation,
        finiteRankedPathAmplitude
          (chiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining.depth path := by
    apply Finset.sum_congr rfl
    intro path _hPath
    change finiteRankedPathAmplitude
        (shiftedChiralCausalSetGrowthLaw chirality) 2 path =
      finiteRankedPathAmplitude (chiralCausalSetGrowthLaw chirality) 2 path
    exact shiftedChiral_depthTwo_pathAmplitude_eq_chiral chirality path
  rw [hSectorAmplitude first, hSectorAmplitude second]

/-- Selection no-go: full microscopic support, all-depth normalized growth,
infinite-cylinder strong positivity, and the exact pure orientation endpoint
still admit at least two genuinely different ancestor-pair laws. -/
theorem fullSupport_endpoint_consistency_does_not_select_pairCoupling
    (chirality : Fin 2) :
    interactingChiralSignatureWeight canonicalPairCoupling chirality ≠
        interactingChiralSignatureWeight shiftedPairCoupling chirality
      ∧ HasFullRawSignatureSupport
          (interactingChiralSignatureWeight canonicalPairCoupling chirality)
      ∧ HasFullRawSignatureSupport
          (interactingChiralSignatureWeight shiftedPairCoupling chirality)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (completeChiralCausalSetGrowthLaw chirality))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (shiftedChiralCausalSetGrowthLaw chirality))
      ∧ inducedOrientationKernel
          (completeChiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining =
        inducedOrientationKernel
          (shiftedChiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining := by
  refine ⟨canonical_and_shifted_signatureWeights_distinct chirality,
    canonicalInteractingChiralWeight_fullSupport chirality,
    shiftedInteractingChiralWeight_fullSupport chirality,
    infiniteRankedCylinderDecoherence_stronglyPositive _,
    shiftedChiralCausalSetGrowthLaw_stronglyPositive chirality, ?_⟩
  rw [completeChiral_inducedOrientationKernel_exact,
    shiftedChiral_inducedOrientationKernel_exact]

/-- Complete-law capstone: the local ±i endpoint is recovered exactly, while
the all-rank dynamics is normalized without a fallback and carries the full
projective strongly-positive infinite-cylinder theory. -/
theorem completeChiralLaw_recovers_endpoint_without_totalization
    (chirality : Fin 2) :
    causalEdgeAmplitudePartition
      (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
      (cardinalCausalAntichain 1) =
        1 + chiralMaximalEventPhase chirality
      ∧ inducedOrientationKernel
          (completeChiralCausalSetGrowthLaw chirality)
          chiralRankTwoCoarseGraining =
        balancedHistoryKernel
          (chiralBoundaryOrientationParameter chirality)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (completeChiralCausalSetGrowthLaw chirality)) := by
  exact ⟨interacting_rankOne_partition_eq_chiral
      canonicalPairCoupling chirality |>.trans
      (chiral_rankOne_partition chirality),
    completeChiral_inducedOrientationKernel_exact chirality,
    infiniteRankedCylinderDecoherence_stronglyPositive _⟩

#print axioms canonical_interactingChiral_partition_ne_zero
#print axioms subcritical_interactingChiral_partition_ne_zero
#print axioms effectivePairChiralSignatureWeight_append_singleton
#print axioms interactingChiralSignatureWeight_eq_iff
#print axioms interactingChiralSignatureWeight_fullSupport_iff
#print axioms zeroCoupling_interactingChiral_partition_ne_zero
#print axioms sparseChiralCausalSetGrowthLaw_stronglyPositive
#print axioms sparseChiral_inducedOrientationKernel_exact
#print axioms fullSupport_endpoint_consistency_does_not_select_pairCoupling
#print axioms completeChiralLaw_projective_stronglyPositive
#print axioms completeChiral_inducedOrientationKernel_exact
#print axioms completeChiralLaw_recovers_endpoint_without_totalization

end

end UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw

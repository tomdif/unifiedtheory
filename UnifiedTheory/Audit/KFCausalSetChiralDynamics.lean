/-
  Audit/KFCausalSetChiralDynamics.lean

  WHAT THE REMAINING MICROPHYSICS CAN AND CANNOT SELECT

  The local quarter-turn character is not globally zero-free.  The finite
  causet consisting of an eight-chain below a six-antichain has vanishing raw
  chiral partition: its lower-chain ideals contribute `1 + 8 i`, while the
  nonempty upper-antichain ideals contribute `(1+i)^6 - 1 = -1 - 8 i`.
  The exact cancellation proves that totalization (or a different dynamical
  rule) is structurally necessary, not merely a technical precaution.

  The second half isolates the two missing microscopic inputs.  Elementary
  relation-complement symmetry supplies the balanced Born law that forces the
  quarter turn.  Reflection cannot choose between its conjugate signs; a
  nonzero reflection-odd chirality source selects a unique endpoint, whereas
  zero source leaves both endpoints degenerate.
-/

import UnifiedTheory.Audit.KFCausalSetChiralGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralDynamics

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth

/-! ## 1. A finite destructive-interference parent -/

/-- An eight-chain ordinally below a six-antichain.  The first eight events
form the chain; each is below every one of the last six events, which are
mutually incomparable. -/
def chainEightBelowAntichainSix : CardinalCausalOrder 14 where
  rel := fun i j => decide (i = j ∨ (i.val < 8 ∧ i.val < j.val))
  refl := by
    intro i
    simp
  antisymm := by
    intro i j hij hji
    simp only [decide_eq_true_eq] at hij hji
    rcases hij with hEq | hLt
    · exact hEq
    rcases hji with hEq | hLt'
    · exact hEq.symm
    · omega
  trans := by
    intro i j k hij hjk
    simp only [decide_eq_true_eq] at hij hjk ⊢
    rcases hij with rfl | hij
    · exact hjk
    rcases hjk with rfl | hjk
    · exact Or.inr hij
    · exact Or.inr ⟨hij.1, Nat.lt_trans hij.2 hjk.2⟩

/-- A fully computable presentation of a causal past set.  This is equivalent
to `CausalPastSet`, but unlike its choice-generated global `Fintype` instance
it can be evaluated by the kernel for a concrete finite parent. -/
abbrev ComputableCausalPastCode {n : ℕ} (parent : CardinalCausalOrder n) :=
  {mem : Fin n → Bool //
    ∀ x y : Fin n, mem x = true → parent.rel y x = true → mem y = true}

instance computableCausalPastCodeFintype {n : ℕ}
    (parent : CardinalCausalOrder n) :
    Fintype (ComputableCausalPastCode parent) := inferInstance

instance computableCausalPastCodeDecidableEq {n : ℕ}
    (parent : CardinalCausalOrder n) :
    DecidableEq (ComputableCausalPastCode parent) := inferInstance

/-- The computable codes are exactly the transition-edge precursor slots. -/
def computableCausalPastCodeEquiv {n : ℕ}
    (parent : CardinalCausalOrder n) :
    ComputableCausalPastCode parent ≃ CausalPastSet parent where
  toFun code := ⟨code.val, code.property⟩
  invFun past := ⟨past.mem, past.downwardClosed⟩
  left_inv := by intro code; cases code; rfl
  right_inv := by intro past; cases past; rfl

/-- Maximal elements of a computable precursor code. -/
abbrev ComputableCausalPastCode.IsMaximal {n : ℕ}
    {parent : CardinalCausalOrder n}
    (code : ComputableCausalPastCode parent) (i : Fin n) : Prop :=
  code.val i = true ∧
    ∀ j : Fin n, code.val j = true → parent.rel i j = true → j = i

instance computableCausalPastCodeIsMaximalDecidable {n : ℕ}
    {parent : CardinalCausalOrder n}
    (code : ComputableCausalPastCode parent) (i : Fin n) :
    Decidable (code.IsMaximal i) := inferInstance

instance causalPastSetIsMaximalDecidable {n : ℕ}
    {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) (i : Fin n) :
    Decidable (past.IsMaximal i) := by
  unfold CausalPastSet.IsMaximal
  infer_instance

/-- Executable maximal-event count. -/
def ComputableCausalPastCode.maximalCount {n : ℕ}
    {parent : CardinalCausalOrder n}
    (code : ComputableCausalPastCode parent) : ℕ :=
  (Finset.univ.filter code.IsMaximal).card

theorem computableCausalPastCode_maximalCount_eq {n : ℕ}
    {parent : CardinalCausalOrder n}
    (code : ComputableCausalPastCode parent) :
    (computableCausalPastCodeEquiv parent code).maximalCount =
      code.maximalCount := by
  unfold CausalPastSet.maximalCount ComputableCausalPastCode.maximalCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

/-! The obstruction parent has a small structural precursor presentation. -/

/-- Downward-closed Boolean subsets of the lower eight-chain. -/
abbrev LowerChainPastCode :=
  {mem : Fin 8 → Bool //
    ∀ x y : Fin 8, mem x = true → y.val ≤ x.val → mem y = true}

/-- Nonempty Boolean subsets of the upper six-antichain. -/
abbrev NonemptyUpperPastCode :=
  {mem : Fin 6 → Bool // ∃ i : Fin 6, mem i = true}

instance lowerChainPastCodeFintype : Fintype LowerChainPastCode := inferInstance
instance lowerChainPastCodeDecidableEq : DecidableEq LowerChainPastCode := inferInstance
instance nonemptyUpperPastCodeFintype : Fintype NonemptyUpperPastCode := inferInstance
instance nonemptyUpperPastCodeDecidableEq : DecidableEq NonemptyUpperPastCode := inferInstance

def lowerEvent (i : Fin 8) : Fin 14 := ⟨i.val, by omega⟩
def upperEvent (i : Fin 6) : Fin 14 := ⟨i.val + 8, by omega⟩

@[simp] theorem lowerEvent_val (i : Fin 8) : (lowerEvent i).val = i.val := rfl
@[simp] theorem upperEvent_val (i : Fin 6) : (upperEvent i).val = i.val + 8 := rfl

/-- A lower-chain past, extended by `false` on the upper antichain. -/
def lowerStructuredPastCode (lower : LowerChainPastCode) :
    ComputableCausalPastCode chainEightBelowAntichainSix := by
  refine ⟨fun i => if h : i.val < 8 then lower.val ⟨i.val, h⟩ else false, ?_⟩
  intro x y hx hyx
  simp only [chainEightBelowAntichainSix, decide_eq_true_eq] at hyx
  rcases hyx with rfl | hStrict
  · exact hx
  by_cases hxLower : x.val < 8
  · simp only [hxLower, ↓reduceDIte] at hx
    have hyLower : y.val < 8 := hStrict.1
    simp only [hyLower, ↓reduceDIte]
    exact lower.property ⟨x.val, hxLower⟩ ⟨y.val, hyLower⟩ hx
      (Nat.le_of_lt hStrict.2)
  · simp [hxLower] at hx

/-- A nonempty upper-antichain subset, with the entire lower chain forced into
its causal past. -/
def upperStructuredPastCode (upper : NonemptyUpperPastCode) :
    ComputableCausalPastCode chainEightBelowAntichainSix := by
  refine ⟨fun i => if h : i.val < 8 then true else
    upper.val ⟨i.val - 8, by omega⟩, ?_⟩
  intro x y hx hyx
  simp only [chainEightBelowAntichainSix, decide_eq_true_eq] at hyx
  rcases hyx with rfl | hStrict
  · exact hx
  · simp [hStrict.1]

/-- Restrict a full precursor to the lower chain. -/
def restrictLowerPastCode
    (code : ComputableCausalPastCode chainEightBelowAntichainSix) :
    LowerChainPastCode := by
  refine ⟨fun i => code.val (lowerEvent i), ?_⟩
  intro x y hx hyx
  apply code.property (lowerEvent x) (lowerEvent y) hx
  simp only [chainEightBelowAntichainSix, decide_eq_true_eq]
  by_cases hEq : y = x
  · exact Or.inl (congrArg lowerEvent hEq)
  · right
    constructor
    · exact y.isLt
    · simp only [lowerEvent_val]
      omega

/-- Restrict a full precursor to the upper antichain. -/
def restrictUpperPastCode
    (code : ComputableCausalPastCode chainEightBelowAntichainSix) : Fin 6 → Bool :=
  fun i => code.val (upperEvent i)

/-- If any upper event is selected, downward closure forces the entire lower
chain into the precursor. -/
theorem lower_forced_of_upper_selected
    (code : ComputableCausalPastCode chainEightBelowAntichainSix)
    {upper : Fin 6} (hUpper : code.val (upperEvent upper) = true)
    (lower : Fin 8) : code.val (lowerEvent lower) = true := by
  apply code.property (upperEvent upper) (lowerEvent lower) hUpper
  simp only [chainEightBelowAntichainSix, decide_eq_true_eq,
    lowerEvent_val, upperEvent_val]
  exact Or.inr (by omega)

/-- Split every precursor into either a lower-chain ideal or a nonempty upper
subset (whose lower chain is then forced). -/
def structuredPastCodeInv
    (code : ComputableCausalPastCode chainEightBelowAntichainSix) :
    LowerChainPastCode ⊕ NonemptyUpperPastCode := by
  by_cases hUpper : ∃ i : Fin 6, restrictUpperPastCode code i = true
  · exact Sum.inr ⟨restrictUpperPastCode code, hUpper⟩
  · exact Sum.inl (restrictLowerPastCode code)

def structuredPastCodeToFull :
    LowerChainPastCode ⊕ NonemptyUpperPastCode →
      ComputableCausalPastCode chainEightBelowAntichainSix
  | Sum.inl lower => lowerStructuredPastCode lower
  | Sum.inr upper => upperStructuredPastCode upper

theorem structuredPastCodeToFull_left_inv
    (code : ComputableCausalPastCode chainEightBelowAntichainSix) :
    structuredPastCodeToFull (structuredPastCodeInv code) = code := by
  unfold structuredPastCodeInv
  split_ifs with hUpper
  · apply Subtype.ext
    funext i
    by_cases hi : i.val < 8
    · simp only [structuredPastCodeToFull, upperStructuredPastCode, hi,
        ↓reduceDIte]
      obtain ⟨upper, hSelected⟩ := hUpper
      have hForced := lower_forced_of_upper_selected code hSelected ⟨i.val, hi⟩
      simpa [lowerEvent] using hForced.symm
    · simp only [structuredPastCodeToFull, upperStructuredPastCode, hi,
        ↓reduceDIte, restrictUpperPastCode]
      have hEvent : upperEvent ⟨i.val - 8, by omega⟩ = i := by
        apply Fin.ext
        simp only [upperEvent_val]
        omega
      rw [hEvent]
  · apply Subtype.ext
    funext i
    by_cases hi : i.val < 8
    · simp only [structuredPastCodeToFull, lowerStructuredPastCode, hi,
        ↓reduceDIte, restrictLowerPastCode, lowerEvent]
    · simp only [structuredPastCodeToFull, lowerStructuredPastCode, hi,
        ↓reduceDIte]
      have hNotSelected : code.val i ≠ true := by
        intro hSelected
        apply hUpper
        let upper : Fin 6 := ⟨i.val - 8, by omega⟩
        refine ⟨upper, ?_⟩
        change code.val (upperEvent upper) = true
        have hEvent : upperEvent upper = i := by
          apply Fin.ext
          simp [upper, upperEvent]
          omega
        simpa [hEvent] using hSelected
      cases hValue : code.val i
      · rfl
      · exact False.elim (hNotSelected hValue)

theorem structuredPastCodeInv_left_inv
    (structured : LowerChainPastCode ⊕ NonemptyUpperPastCode) :
    structuredPastCodeInv (structuredPastCodeToFull structured) = structured := by
  rcases structured with lower | upper
  · unfold structuredPastCodeInv
    simp only [structuredPastCodeToFull]
    have hNoUpper : ¬ ∃ i : Fin 6,
        restrictUpperPastCode (lowerStructuredPastCode lower) i = true := by
      simp [restrictUpperPastCode, lowerStructuredPastCode, upperEvent]
    rw [dif_neg hNoUpper]
    congr 1
    apply Subtype.ext
    funext i
    simp [restrictLowerPastCode, lowerStructuredPastCode, lowerEvent]
  · unfold structuredPastCodeInv
    simp only [structuredPastCodeToFull]
    have hSomeUpper : ∃ i : Fin 6,
        restrictUpperPastCode (upperStructuredPastCode upper) i = true := by
      obtain ⟨i, hi⟩ := upper.property
      refine ⟨i, ?_⟩
      simpa [restrictUpperPastCode, upperStructuredPastCode, upperEvent] using hi
    rw [dif_pos hSomeUpper]
    congr 1

/-- Structural equivalence exposing only `9 + 63 = 72` precursor slots. -/
def structuredPastCodeEquiv :
    (LowerChainPastCode ⊕ NonemptyUpperPastCode) ≃
      ComputableCausalPastCode chainEightBelowAntichainSix where
  toFun := structuredPastCodeToFull
  invFun := structuredPastCodeInv
  left_inv := structuredPastCodeInv_left_inv
  right_inv := structuredPastCodeToFull_left_inv

/-- Gaussian integers, used only to make the finite cancellation executable. -/
abbrev GaussianInt := ℤ × ℤ

/-- Multiplication by `i` in Gaussian-integer coordinates. -/
def gaussianMulI (z : GaussianInt) : GaussianInt := (-z.2, z.1)

/-- Exact Gaussian-integer powers of `i`. -/
def gaussianIPow : ℕ → GaussianInt
  | 0 => (1, 0)
  | n + 1 => gaussianMulI (gaussianIPow n)

/-- Embed Gaussian integers in the complex numbers. -/
def gaussianToComplex : GaussianInt →+ ℂ where
  toFun z := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I
  map_zero' := by apply Complex.ext <;> norm_num
  map_add' := by
    intro first second
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

@[simp]
theorem gaussianToComplex_gaussianIPow (n : ℕ) :
    gaussianToComplex (gaussianIPow n) = Complex.I ^ n := by
  induction n with
  | zero => norm_num [gaussianIPow, gaussianToComplex]
  | succ n ih =>
      simp only [gaussianIPow]
      rw [pow_succ, ← ih]
      generalize gaussianIPow n = z
      rcases z with ⟨a, b⟩
      simp only [gaussianToComplex, gaussianMulI, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk]
      rw [add_mul, mul_assoc, Complex.I_mul_I]
      push_cast
      ring

/-- The nine lower-chain ideals contribute `1 + 8 i`. -/
theorem lowerStructuredPast_gaussian_partition :
    (∑ lower : LowerChainPastCode,
      gaussianIPow (lowerStructuredPastCode lower).maximalCount) = (1, 8) := by
  decide

/-- The 63 nonempty upper-antichain subsets contribute `-1 - 8 i`. -/
theorem upperStructuredPast_gaussian_partition :
    (∑ upper : NonemptyUpperPastCode,
      gaussianIPow (upperStructuredPastCode upper).maximalCount) = (-1, -8) := by
  decide

/-- Kernel-checked structural certificate for the exact 14-event cancellation. -/
theorem chainEightBelowAntichainSix_gaussian_partition_zero :
    (∑ code : ComputableCausalPastCode chainEightBelowAntichainSix,
      gaussianIPow code.maximalCount) = (0, 0) := by
  calc
    (∑ code : ComputableCausalPastCode chainEightBelowAntichainSix,
      gaussianIPow code.maximalCount) =
        ∑ structured : LowerChainPastCode ⊕ NonemptyUpperPastCode,
          gaussianIPow (structuredPastCodeToFull structured).maximalCount := by
      apply Fintype.sum_equiv structuredPastCodeEquiv.symm
      intro code
      change gaussianIPow code.maximalCount = gaussianIPow
        (structuredPastCodeToFull (structuredPastCodeInv code)).maximalCount
      rw [structuredPastCodeToFull_left_inv]
    _ = (∑ lower : LowerChainPastCode,
          gaussianIPow (lowerStructuredPastCode lower).maximalCount) +
        ∑ upper : NonemptyUpperPastCode,
          gaussianIPow (upperStructuredPastCode upper).maximalCount := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = (0, 0) := by
      rw [lowerStructuredPast_gaussian_partition,
        upperStructuredPast_gaussian_partition]
      norm_num

/-- **Finite obstruction theorem.**  The positive-chirality raw transition
partition vanishes on an explicit 14-event unlabeled causet. -/
theorem chiral_positive_partition_can_vanish :
    causalEdgeAmplitudePartition (chiralCausalEdgeAmplitude 0)
      chainEightBelowAntichainSix = 0 := by
  classical
  unfold causalEdgeAmplitudePartition
  calc
    (∑ past : CausalPastSet chainEightBelowAntichainSix,
        (chiralCausalEdgeAmplitude 0).amplitude
          chainEightBelowAntichainSix past) =
        ∑ code : ComputableCausalPastCode chainEightBelowAntichainSix,
          Complex.I ^ code.maximalCount := by
      apply Fintype.sum_equiv
        (computableCausalPastCodeEquiv chainEightBelowAntichainSix).symm
      intro past
      simp [chiralCausalEdgeAmplitude,
        rideoutSorkinSignatureAmplitude,
        chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight,
        chiralMaximalEventPhase]
      rw [← computableCausalPastCode_maximalCount_eq
        ((computableCausalPastCodeEquiv
          chainEightBelowAntichainSix).symm past)]
      simp
    _ = gaussianToComplex
        (∑ code : ComputableCausalPastCode chainEightBelowAntichainSix,
          gaussianIPow code.maximalCount) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro code _
      rw [gaussianToComplex_gaussianIPow]
    _ = 0 := by
      rw [chainEightBelowAntichainSix_gaussian_partition_zero]
      exact map_zero gaussianToComplex

/-- Reflection gives the same zero obstruction in the conjugate chirality. -/
theorem chiral_negative_partition_can_vanish :
    causalEdgeAmplitudePartition (chiralCausalEdgeAmplitude 1)
      chainEightBelowAntichainSix = 0 := by
  classical
  unfold causalEdgeAmplitudePartition
  calc
    (∑ past : CausalPastSet chainEightBelowAntichainSix,
      (chiralCausalEdgeAmplitude 1).amplitude
        chainEightBelowAntichainSix past) =
      ∑ past : CausalPastSet chainEightBelowAntichainSix,
        star ((chiralCausalEdgeAmplitude 0).amplitude
          chainEightBelowAntichainSix past) := by
      apply Finset.sum_congr rfl
      intro past _
      simp [chiralCausalEdgeAmplitude,
        rideoutSorkinSignatureAmplitude,
        chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight,
        chiralMaximalEventPhase]
    _ = star (∑ past : CausalPastSet chainEightBelowAntichainSix,
        (chiralCausalEdgeAmplitude 0).amplitude
          chainEightBelowAntichainSix past) := by
      exact (star_sum Finset.univ (fun past :
        CausalPastSet chainEightBelowAntichainSix =>
          (chiralCausalEdgeAmplitude 0).amplitude
            chainEightBelowAntichainSix past)).symm
    _ = 0 := by
      change star (causalEdgeAmplitudePartition
        (chiralCausalEdgeAmplitude 0) chainEightBelowAntichainSix) = 0
      rw [chiral_positive_partition_can_vanish]
      simp

/-- At the obstruction parent, the all-depth law really takes its uniform
fallback branch.  The fallback is therefore active physics, not dead code. -/
theorem chiral_totalization_is_uniform_at_obstruction
    (chirality : Fin 2)
    (child : UnlabeledCardinalCausalOrder 15) :
    totalizedNormalizedCausalEdgeAmplitude
        (chiralCausalEdgeAmplitude chirality)
        (Quotient.mk _ chainEightBelowAntichainSix) child =
      uniformRideoutSorkinAggregatedTransition
        (Quotient.mk _ chainEightBelowAntichainSix) child := by
  unfold totalizedNormalizedCausalEdgeAmplitude
  have hZero : unlabeledCausalEdgeAmplitudePartition
      (chiralCausalEdgeAmplitude chirality)
      (Quotient.mk _ chainEightBelowAntichainSix) = 0 := by
    fin_cases chirality
    · exact chiral_positive_partition_can_vanish
    · exact chiral_negative_partition_can_vanish
  rw [if_pos hZero]

/-! ## 2. The missing microscopic balance law -/

/-- Born probabilities for the empty and full elementary precursor slots. -/
def elementaryEmptyBornWeight (b : ℂ) : ℝ :=
  Complex.normSq (1 / (1 + b))

def elementaryFullBornWeight (b : ℂ) : ℝ :=
  Complex.normSq (b / (1 + b))

/-- Relation-complement symmetry at the unique one-event parent: neither
absence nor presence of the one possible causal relation is preferred. -/
def ElementaryRelationComplementSymmetric (b : ℂ) : Prop :=
  elementaryEmptyBornWeight b = elementaryFullBornWeight b

/-- Normalization plus complement symmetry makes both elementary outcomes
exactly balanced. -/
theorem elementary_complement_symmetry_forces_balance
    (b : ℂ)
    (hNormalized : elementaryEmptyBornWeight b +
      elementaryFullBornWeight b = 1)
    (hSymmetric : ElementaryRelationComplementSymmetric b) :
    elementaryEmptyBornWeight b = 1 / 2 ∧
      elementaryFullBornWeight b = 1 / 2 := by
  unfold ElementaryRelationComplementSymmetric at hSymmetric
  constructor <;> unfold elementaryEmptyBornWeight elementaryFullBornWeight at * <;>
    linarith

/-- Born normalization by itself leaves a continuous imaginary family.  This
is the no-go showing why relation-complement symmetry is genuine additional
microphysics rather than a consequence of normalization. -/
theorem imaginary_relative_amplitudes_are_Born_normalized (t : ℝ) :
    elementaryEmptyBornWeight ((t : ℂ) * Complex.I) +
      elementaryFullBornWeight ((t : ℂ) * Complex.I) = 1 := by
  have hDenominator : (1 + t ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg t]
  unfold elementaryEmptyBornWeight elementaryFullBornWeight
  rw [Complex.normSq_div, Complex.normSq_div]
  norm_num [Complex.normSq_apply, pow_two]
  field_simp [hDenominator]

/-- Distinct real parameters give distinct normalized microscopic laws. -/
theorem imaginary_relative_amplitude_family_injective :
    Function.Injective (fun t : ℝ => (t : ℂ) * Complex.I) := by
  intro first second hEqual
  have hImaginary := congrArg Complex.im hEqual
  simpa using hImaginary

/-- **Microscopic derivation of the two chiral sectors.**  A unit elementary
relative amplitude, normalized Born weights, and relation-complement symmetry
force the two and only two quarter-turn amplitudes. -/
theorem elementary_symmetry_derives_chiral_phase
    (b : ℂ) (hPartition : 1 + b ≠ 0)
    (hNormalized : elementaryEmptyBornWeight b +
      elementaryFullBornWeight b = 1)
    (hSymmetric : ElementaryRelationComplementSymmetric b) :
    b = Complex.I ∨ b = -Complex.I := by
  obtain ⟨hEmpty, hFull⟩ :=
    elementary_complement_symmetry_forces_balance b hNormalized hSymmetric
  exact balanced_normalized_binary_birth_forces_quarter_turn
    b hPartition hEmpty hFull

/-! ## 3. Reflection breaking selects the sign -/

/-- The admissible orientation interval from strong positivity. -/
def IsAdmissibleOrientationParameter (y : ℝ) : Prop := |y| ≤ 1 / 2

/-- Minimal reflection-odd source energy.  Reflection sends both `h` and `y`
to their negatives and leaves the energy invariant. -/
def chiralitySourceEnergy (h y : ℝ) : ℝ := -h * y

theorem chiralitySourceEnergy_reflection (h y : ℝ) :
    chiralitySourceEnergy (-h) (-y) = chiralitySourceEnergy h y := by
  simp [chiralitySourceEnergy]

/-- A positive chirality source uniquely selects the positive pure endpoint. -/
theorem positive_source_unique_minimizer {h y : ℝ}
    (hPositive : 0 < h)
    (hy : IsAdmissibleOrientationParameter y) :
    chiralitySourceEnergy h (1 / 2) ≤ chiralitySourceEnergy h y
      ∧ (chiralitySourceEnergy h y = chiralitySourceEnergy h (1 / 2) ↔
        y = 1 / 2) := by
  unfold IsAdmissibleOrientationParameter at hy
  have hUpper : y ≤ 1 / 2 := (abs_le.mp hy).2
  unfold chiralitySourceEnergy
  constructor
  · nlinarith
  · constructor
    · intro hEqual
      nlinarith
    · rintro rfl
      rfl

/-- A negative chirality source uniquely selects the negative pure endpoint. -/
theorem negative_source_unique_minimizer {h y : ℝ}
    (hNegative : h < 0)
    (hy : IsAdmissibleOrientationParameter y) :
    chiralitySourceEnergy h (-1 / 2) ≤ chiralitySourceEnergy h y
      ∧ (chiralitySourceEnergy h y = chiralitySourceEnergy h (-1 / 2) ↔
        y = -1 / 2) := by
  unfold IsAdmissibleOrientationParameter at hy
  have hLower : -(1 / 2 : ℝ) ≤ y := (abs_le.mp hy).1
  unfold chiralitySourceEnergy
  constructor
  · nlinarith
  · constructor
    · intro hEqual
      nlinarith
    · rintro rfl
      rfl

/-- At zero source the dynamics is exactly unable to select a sign: all
admissible parameters, including both pure endpoints and mixed interiors, are
degenerate. -/
theorem zero_source_no_sign_selection (y : ℝ) :
    chiralitySourceEnergy 0 y = 0 := by
  simp [chiralitySourceEnergy]

/-- The two pure sectors are exchanged by reflection and become uniquely
selected by opposite infinitesimal source signs. -/
theorem reflection_breaking_selects_opposite_endpoints
    (h : ℝ) (hNonzero : h ≠ 0) :
    (0 < h ∧ ∀ y, IsAdmissibleOrientationParameter y →
        chiralitySourceEnergy h (1 / 2) ≤ chiralitySourceEnergy h y ∧
        (chiralitySourceEnergy h y = chiralitySourceEnergy h (1 / 2) ↔
          y = 1 / 2))
      ∨
    (h < 0 ∧ ∀ y, IsAdmissibleOrientationParameter y →
        chiralitySourceEnergy h (-1 / 2) ≤ chiralitySourceEnergy h y ∧
        (chiralitySourceEnergy h y = chiralitySourceEnergy h (-1 / 2) ↔
          y = -1 / 2)) := by
  rcases lt_or_gt_of_ne hNonzero with hNegative | hPositive
  · exact Or.inr ⟨hNegative, fun _ hy =>
      negative_source_unique_minimizer hNegative hy⟩
  · exact Or.inl ⟨hPositive, fun _ hy =>
      positive_source_unique_minimizer hPositive hy⟩

#print axioms chiral_positive_partition_can_vanish
#print axioms chiral_negative_partition_can_vanish
#print axioms chiral_totalization_is_uniform_at_obstruction
#print axioms imaginary_relative_amplitudes_are_Born_normalized
#print axioms elementary_symmetry_derives_chiral_phase
#print axioms reflection_breaking_selects_opposite_endpoints

end

end UnifiedTheory.Audit.KFCausalSetChiralDynamics

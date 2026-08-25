/-
  Audit/KFCausalSetPhaseSafeHarmonicBornShell.lean

  PHASE-SAFE BORN-SHELL COMPLETION

  Born normalization fixes the modulus of the scalar acting on the
  support-relative zero-sum carrier, but not its phase.  On a finite physical
  successor support, each corrected coordinate forbids at most one phase.
  An open semicircle contains infinitely many phases, so one can choose a
  compatible phase avoiding all of those finitely many coordinate zeros.

  The harmonic specialization makes one such choice for chirality zero and
  uses complex conjugation for chirality one.  Consequently the resulting
  all-rank law has exact (rather than merely one-sided) physical support and
  retains reflection conjugacy.  The choice is noncomputable and is not the
  least-change positive-radial representative.  Rotating the centered
  component can change individual branch Born probabilities, so this is an
  added full-support selection principle, not a gauge redundancy or a unique
  consequence of the vacuum action.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetPhaseSafeHarmonicBornShell

noncomputable section

open scoped BigOperators ComplexConjugate
open Set
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
open UnifiedTheory.Audit.KFTOEGate1HarmonicBornShellSelection

universe u

/-! ## 1. Finite phase avoidance -/

/-- Upper-semicircle phase with real coordinate `x`. -/
def upperSemicirclePhase (x : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ)

@[simp]
theorem upperSemicirclePhase_re (x : ℝ) :
    (upperSemicirclePhase x).re = x := by
  simp [upperSemicirclePhase]

theorem upperSemicirclePhase_normSq_one {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Complex.normSq (upperSemicirclePhase x) = 1 := by
  apply Complex.normSq_ofReal_add_I_mul_sqrt_one_sub
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩

/-- Rotating a complex scale by a unit phase preserves its squared modulus. -/
theorem star_mul_self_mul_upperSemicirclePhase
    (base : ℂ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    star (base * upperSemicirclePhase x) *
        (base * upperSemicirclePhase x) =
      star base * base := by
  have hPhase : star (upperSemicirclePhase x) *
      upperSemicirclePhase x = 1 := by
    calc
      star (upperSemicirclePhase x) * upperSemicirclePhase x =
          (Complex.normSq (upperSemicirclePhase x) : ℂ) := by
            exact (Complex.normSq_eq_conj_mul_self).symm
      _ = 1 := by rw [upperSemicirclePhase_normSq_one hx]; norm_num
  rw [star_mul]
  calc
    star (upperSemicirclePhase x) * star base *
          (base * upperSemicirclePhase x) =
        (star base * base) *
          (star (upperSemicirclePhase x) * upperSemicirclePhase x) := by
            ring
    _ = star base * base := by rw [hPhase]; ring

/-- A nonzero compatible radial representative can always be phase-rotated
so that the Born-shell correction is nonzero at every point of a finite,
nonempty support.  Each branch contributes only the real coordinate of its
single forbidden phase to a finite exclusion set. -/
theorem exists_phaseSafe_scale
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ) (base : ℂ) (hBase : base ≠ 0) :
    ∃ scale : ℂ,
      star scale * scale = star base * base ∧
      ∀ branch ∈ support,
        finiteSupportBornShellCorrection support scale amplitude branch ≠ 0 := by
  classical
  let uniform : ℂ := supportUniformAmplitude support
  let centered : Branch → ℂ := supportCenteredAmplitude support amplitude
  let forbiddenReal : Finset ℝ := support.image fun branch =>
    (-uniform / (base * centered branch)).re
  obtain ⟨x, hx, hxAvoids⟩ :=
    (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).exists_notMem_finset
      forbiddenReal
  let phase := upperSemicirclePhase x
  refine ⟨base * phase,
    star_mul_self_mul_upperSemicirclePhase base hx, ?_⟩
  intro branch hBranch hZero
  have hUniform : uniform ≠ 0 := by
    have hCard : (support.card : ℂ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hSupport)
    simp [uniform, supportUniformAmplitude, hCard]
  have hCentered : centered branch ≠ 0 := by
    intro hCenteredZero
    have : uniform = 0 := by
      simpa [finiteSupportBornShellCorrection, hBranch, centered,
        phase, hCenteredZero] using hZero
    exact hUniform this
  have hProduct : base * centered branch ≠ 0 := mul_ne_zero hBase hCentered
  have hPhaseForbidden : phase = -uniform / (base * centered branch) := by
    rw [eq_div_iff hProduct]
    have hMul : base * phase * centered branch = -uniform := by
      exact eq_neg_of_add_eq_zero_left (by
        simpa [finiteSupportBornShellCorrection, hBranch, uniform,
          add_comm,
          centered] using hZero)
    calc
      phase * (base * centered branch) =
          base * phase * centered branch := by ring
      _ = -uniform := hMul
  have hRealForbidden : x =
      (-uniform / (base * centered branch)).re := by
    simpa [phase] using congrArg Complex.re hPhaseForbidden
  apply hxAvoids
  exact Finset.mem_image.mpr ⟨branch, hBranch, hRealForbidden.symm⟩

/-! ## 2. Local phase-safe harmonic scales -/

/-- The harmonic Born-shell equation at one causal parent. -/
def HarmonicLocalBornCompatible (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (scale : ℂ) : Prop :=
  star scale * scale *
      (supportComplexBornMass (physicalCausalSuccessors n pathPrefix)
          ((harmonicCriticalCausalSetGrowthLaw chirality).transition
            n pathPrefix) -
        supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)) =
    1 - supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)

/-- No coordinate on the physical successor support is erased at one causal
parent. -/
def HarmonicLocalSupportExact (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (scale : ℂ) : Prop :=
  ∀ child ∈ physicalCausalSuccessors n pathPrefix,
    finiteSupportBornShellCorrection
        (physicalCausalSuccessors n pathPrefix) scale
        ((harmonicCriticalCausalSetGrowthLaw chirality).transition
          n pathPrefix) child ≠ 0

/-- At every harmonic causal parent there is a scale that simultaneously
solves the Born equation and retains every physical successor.  At the
singleton root the zero scale already works; at every genuine branch the
positive radial scale supplies the forced modulus and finite phase avoidance
supplies a nonvanishing representative on that circle. -/
theorem harmonicLocal_phaseSafe_scale_exists
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∃ scale : ℂ,
      HarmonicLocalBornCompatible chirality n pathPrefix scale ∧
      HarmonicLocalSupportExact chirality n pathPrefix scale := by
  classical
  let support := physicalCausalSuccessors n pathPrefix
  let amplitude :=
    (harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix
  have hSupport : support.Nonempty :=
    physicalCausalSuccessors_nonempty n pathPrefix
  by_cases hSingleton : support.card = 1
  · refine ⟨0, ?_, ?_⟩
    · have hCompatible :=
        explicitHarmonicCriticalBornShellScale_compatible
          chirality n pathPrefix
      have hExplicit :
          explicitHarmonicCriticalBornShellScale chirality n pathPrefix = 0 := by
        simp [explicitHarmonicCriticalBornShellScale, support, hSingleton]
      rw [hExplicit] at hCompatible
      simpa [HarmonicLocalBornCompatible, support, amplitude] using hCompatible
    · intro child hChild
      have hUniform : supportUniformAmplitude support ≠ 0 := by
        have hCard : (support.card : ℂ) ≠ 0 := by
          exact_mod_cast (Finset.card_ne_zero.mpr hSupport)
        simp [supportUniformAmplitude, hCard]
      simpa [HarmonicLocalSupportExact,
        finiteSupportBornShellCorrection, hChild, support, amplitude]
        using hUniform
  · have hMultiple : 1 < support.card := by
      have hPositive := physicalCausalSuccessors_card_pos n pathPrefix
      change 0 < support.card at hPositive
      omega
    have hNonuniform : ∃ child ∈ support,
        amplitude child ≠ supportUniformAmplitude support :=
      harmonicCriticalNonuniformOnBranching chirality n pathPrefix hMultiple
    have hExcessPositive : 0 < supportBornExcess support amplitude :=
      supportBornExcess_pos_of_nonuniform support amplitude hNonuniform
    have hCardOne : (1 : ℝ) < support.card := by exact_mod_cast hMultiple
    have hNumeratorPositive : 0 < 1 - (support.card : ℝ)⁻¹ :=
      sub_pos.mpr (inv_lt_one_of_one_lt₀ hCardOne)
    have hRatioPositive :
        0 < (1 - (support.card : ℝ)⁻¹) /
          supportBornExcess support amplitude :=
      div_pos hNumeratorPositive hExcessPositive
    let base := explicitHarmonicCriticalBornShellScale
      chirality n pathPrefix
    have hBase : base ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      simpa [base, explicitHarmonicCriticalBornShellScale, support,
        hSingleton, supportBornShellScale, amplitude] using
          (Real.sqrt_pos.2 hRatioPositive)
    obtain ⟨scale, hNorm, hExact⟩ :=
      exists_phaseSafe_scale support hSupport amplitude base hBase
    refine ⟨scale, ?_, ?_⟩
    · have hCompatible :=
        explicitHarmonicCriticalBornShellScale_compatible
          chirality n pathPrefix
      change star base * base *
          (supportComplexBornMass support amplitude -
            supportUniformAmplitude support) =
        1 - supportUniformAmplitude support at hCompatible
      change star scale * scale *
          (supportComplexBornMass support amplitude -
            supportUniformAmplitude support) =
        1 - supportUniformAmplitude support
      rw [hNorm]
      exact hCompatible
    · simpa [HarmonicLocalSupportExact, support, amplitude] using hExact

/-! ## 3. Reflection-paired global choice -/

/-- Complex conjugation commutes with support-relative Born-shell correction
provided the scale is conjugated as well. -/
theorem star_finiteSupportBornShellCorrection_general
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (scale : ℂ) (amplitude : Branch → ℂ)
    (branch : Branch) :
    star (finiteSupportBornShellCorrection support scale amplitude branch) =
      finiteSupportBornShellCorrection support (star scale)
        (fun other => star (amplitude other)) branch := by
  classical
  by_cases hBranch : branch ∈ support
  · simp [finiteSupportBornShellCorrection, hBranch,
      supportCenteredAmplitude, supportUniformAmplitude]
  · simp [finiteSupportBornShellCorrection, hBranch]

/-- Support Born mass is invariant under pointwise conjugation. -/
theorem supportComplexBornMass_star
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) :
    supportComplexBornMass support (fun branch => star (amplitude branch)) =
      supportComplexBornMass support amplitude := by
  classical
  unfold supportComplexBornMass
  apply Finset.sum_congr rfl
  intro branch _hBranch
  rw [star_star]
  ring

theorem harmonicTransition_reflection_fun
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    (harmonicCriticalCausalSetGrowthLaw
        (reflectedMicroscopicChirality chirality)).transition
        n pathPrefix =
      fun child => star
        ((harmonicCriticalCausalSetGrowthLaw chirality).transition
          n pathPrefix child) := by
  funext child
  exact (star_harmonicCriticalTransition chirality
    (currentUnlabeledCausalOrder n pathPrefix) child).symm

/-- A locally valid phase-safe scale for one chirality conjugates to a
locally valid phase-safe scale for the reflected chirality. -/
theorem harmonicLocal_phaseSafe_reflection
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (scale : ℂ)
    (hCompatible :
      HarmonicLocalBornCompatible chirality n pathPrefix scale)
    (hExact : HarmonicLocalSupportExact chirality n pathPrefix scale) :
    HarmonicLocalBornCompatible
        (reflectedMicroscopicChirality chirality) n pathPrefix (star scale) ∧
      HarmonicLocalSupportExact
        (reflectedMicroscopicChirality chirality) n pathPrefix (star scale) := by
  let support := physicalCausalSuccessors n pathPrefix
  let amplitude :=
    (harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix
  have hReflectedAmplitude :
      (harmonicCriticalCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix = fun child => star (amplitude child) := by
    simpa [amplitude] using
      harmonicTransition_reflection_fun chirality n pathPrefix
  constructor
  · change star (star scale) * star scale *
        (supportComplexBornMass support
            ((harmonicCriticalCausalSetGrowthLaw
              (reflectedMicroscopicChirality chirality)).transition
                n pathPrefix) - supportUniformAmplitude support) =
      1 - supportUniformAmplitude support
    rw [hReflectedAmplitude, supportComplexBornMass_star]
    change star scale * scale *
        (supportComplexBornMass support amplitude -
          supportUniformAmplitude support) =
      1 - supportUniformAmplitude support at hCompatible
    simpa [mul_comm] using hCompatible
  · intro child hChild
    change finiteSupportBornShellCorrection support (star scale)
        ((harmonicCriticalCausalSetGrowthLaw
          (reflectedMicroscopicChirality chirality)).transition
            n pathPrefix) child ≠ 0
    rw [hReflectedAmplitude]
    rw [← star_finiteSupportBornShellCorrection_general]
    intro hStarZero
    apply hExact child hChild
    have hConjugate := congrArg star hStarZero
    simpa using hConjugate

/-- One noncomputably selected full-support phase representative in the
chirality-zero sector. -/
noncomputable def phaseSafeChiralityZeroScale (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) : ℂ :=
  Classical.choose (harmonicLocal_phaseSafe_scale_exists 0 n pathPrefix)

theorem phaseSafeChiralityZeroScale_spec (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    HarmonicLocalBornCompatible 0 n pathPrefix
        (phaseSafeChiralityZeroScale n pathPrefix) ∧
      HarmonicLocalSupportExact 0 n pathPrefix
        (phaseSafeChiralityZeroScale n pathPrefix) :=
  Classical.choose_spec (harmonicLocal_phaseSafe_scale_exists 0 n pathPrefix)

/-- Reflection-paired full-support convention.  Chirality zero is selected by
finite avoidance; chirality one is its complex conjugate. -/
noncomputable def phaseSafeHarmonicScale (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) : ℂ :=
  if chirality = 0 then phaseSafeChiralityZeroScale n pathPrefix
  else star (phaseSafeChiralityZeroScale n pathPrefix)

theorem phaseSafeHarmonicScale_spec (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    HarmonicLocalBornCompatible chirality n pathPrefix
        (phaseSafeHarmonicScale chirality n pathPrefix) ∧
      HarmonicLocalSupportExact chirality n pathPrefix
        (phaseSafeHarmonicScale chirality n pathPrefix) := by
  fin_cases chirality
  · simpa [phaseSafeHarmonicScale] using
      phaseSafeChiralityZeroScale_spec n pathPrefix
  · have hZero := phaseSafeChiralityZeroScale_spec n pathPrefix
    have hReflected := harmonicLocal_phaseSafe_reflection 0 n pathPrefix
      (phaseSafeChiralityZeroScale n pathPrefix) hZero.1 hZero.2
    simpa [phaseSafeHarmonicScale, reflectedMicroscopicChirality] using
      hReflected

theorem star_phaseSafeHarmonicScale (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    star (phaseSafeHarmonicScale chirality n pathPrefix) =
      phaseSafeHarmonicScale
        (reflectedMicroscopicChirality chirality) n pathPrefix := by
  fin_cases chirality <;>
    simp [phaseSafeHarmonicScale, reflectedMicroscopicChirality]

/-- All-rank compatible Born-shell profile carrying the extra noncomputable
full-support phase-selection convention. -/
noncomputable def phaseSafeHarmonicBornShellScale (chirality : Fin 2) :
    HarmonicCriticalBornShellScale chirality where
  scale := phaseSafeHarmonicScale chirality
  compatible := fun n pathPrefix =>
    (phaseSafeHarmonicScale_spec chirality n pathPrefix).1

/-- The action-selected raw harmonic law completed using the additional
full-support phase convention. -/
noncomputable def phaseSafeHarmonicBornShellGrowthLaw (chirality : Fin 2) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  harmonicCriticalBornShellGrowthLaw chirality
    (phaseSafeHarmonicBornShellScale chirality)

/-! ## 4. Exact physical support and atlas realization -/

/-- The phase-safe law is nonzero exactly on genuine one-element causal
extensions. -/
theorem phaseSafeHarmonicTransition_ne_zero_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
      IsPhysicalCausalGrowthStep n pathPrefix child := by
  constructor
  · intro hNonzero
    by_contra hNotPhysical
    apply hNonzero
    exact physicalBornShellTransition_supported
      (harmonicCriticalCausalSetGrowthLaw chirality)
      (harmonicCriticalPhysicalBornShellProfile chirality
        (phaseSafeHarmonicBornShellScale chirality))
      n pathPrefix child hNotPhysical
  · intro hPhysical
    change finiteSupportBornShellCorrection
        (physicalCausalSuccessors n pathPrefix)
        (phaseSafeHarmonicScale chirality n pathPrefix)
        ((harmonicCriticalCausalSetGrowthLaw chirality).transition
          n pathPrefix) child ≠ 0
    exact (phaseSafeHarmonicScale_spec chirality n pathPrefix).2 child
      (by simpa [physicalCausalSuccessors] using hPhysical)

/-- Reflection continues to exchange the two phase-safe chiral laws. -/
theorem star_phaseSafeHarmonicTransition
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    star ((phaseSafeHarmonicBornShellGrowthLaw chirality).transition
        n pathPrefix child) =
      (phaseSafeHarmonicBornShellGrowthLaw
        (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix child := by
  change star (finiteSupportBornShellCorrection
      (physicalCausalSuccessors n pathPrefix)
      (phaseSafeHarmonicScale chirality n pathPrefix)
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix)
      child) =
    finiteSupportBornShellCorrection
      (physicalCausalSuccessors n pathPrefix)
      (phaseSafeHarmonicScale
        (reflectedMicroscopicChirality chirality) n pathPrefix)
      ((harmonicCriticalCausalSetGrowthLaw
        (reflectedMicroscopicChirality chirality)).transition n pathPrefix)
      child
  rw [star_finiteSupportBornShellCorrection_general]
  rw [star_phaseSafeHarmonicScale]
  congr 1
  funext other
  exact star_harmonicCriticalTransition chirality
    (currentUnlabeledCausalOrder n pathPrefix) other

theorem phaseSafeHarmonic_atlasTransition_ne_zero
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    (phaseSafeHarmonicBornShellGrowthLaw chirality).transition n
        (atlasStepPrefix n hnext) (atlasStepChild n hnext) ≠ 0 := by
  exact (phaseSafeHarmonicTransition_ne_zero_iff_physical chirality n
    (atlasStepPrefix n hnext) (atlasStepChild n hnext)).2
      (atlasStep_isPhysical n hnext)

theorem phaseSafeHarmonic_atlasPathAmplitude_ne_zero
    (chirality : Fin 2) :
    ∀ (n : ℕ) (h : n ≤ 140),
      finiteRankedPathAmplitude
          (phaseSafeHarmonicBornShellGrowthLaw chirality) n
          (globalAtlasPhysicalGrowthPath n h) ≠ 0
  | 0, _ => by simp [finiteRankedPathAmplitude]
  | n + 1, h => by
      change
        finiteRankedPathAmplitude
            (phaseSafeHarmonicBornShellGrowthLaw chirality) n
            (atlasStepPrefix n h) *
          (phaseSafeHarmonicBornShellGrowthLaw chirality).transition
            n (atlasStepPrefix n h) (atlasStepChild n h) ≠ 0
      exact mul_ne_zero
        (phaseSafeHarmonic_atlasPathAmplitude_ne_zero chirality n
          (Nat.le_trans (Nat.le_succ n) h))
        (phaseSafeHarmonic_atlasTransition_ne_zero chirality n h)

/-- Global capstone for the phase-selected alternative.  The conjunction is
unconditional, but its law is explicitly the added full-support convention,
not the uniquely least-changing positive-radial law. -/
theorem phaseSafeHarmonicBornShell_global_capstone (chirality : Fin 2) :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      ∑ child, (phaseSafeHarmonicBornShellGrowthLaw chirality).transition
        n pathPrefix child = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      finiteComplexBornMass
        ((phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix) = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      (phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
        IsPhysicalCausalGrowthStep n pathPrefix child) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      star ((phaseSafeHarmonicBornShellGrowthLaw chirality).transition
          n pathPrefix child) =
        (phaseSafeHarmonicBornShellGrowthLaw
          (reflectedMicroscopicChirality chirality)).transition
            n pathPrefix child) ∧
    finiteRankedPathAmplitude
        (phaseSafeHarmonicBornShellGrowthLaw chirality) 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0 := by
  have hAll := harmonicCriticalBornShell_all_rank chirality
    (phaseSafeHarmonicBornShellScale chirality)
  exact ⟨hAll.1, hAll.2.1,
    phaseSafeHarmonicTransition_ne_zero_iff_physical chirality,
    star_phaseSafeHarmonicTransition chirality,
    phaseSafeHarmonic_atlasPathAmplitude_ne_zero chirality 140 le_rfl⟩

#print axioms exists_phaseSafe_scale
#print axioms harmonicLocal_phaseSafe_scale_exists
#print axioms phaseSafeHarmonicScale_spec
#print axioms phaseSafeHarmonicTransition_ne_zero_iff_physical
#print axioms phaseSafeHarmonicBornShell_global_capstone

end

end UnifiedTheory.Audit.KFCausalSetPhaseSafeHarmonicBornShell

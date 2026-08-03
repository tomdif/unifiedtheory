/-
  Audit/KFCausalBornShellGeneralLaw.lean

  GENERAL BORN-SHELL COMPLETION OF FINITE CAUSAL BRANCHING

  A coherently normalized finite amplitude has a canonical decomposition into
  its permutation-invariant uniform component and a zero-sum component.  This
  file proves in arbitrary finite branching rank that rescaling only the
  zero-sum component preserves the coherent total.  The Born equation fixes
  the squared radial modulus uniquely whenever that component is nonzero.

  The uniform boundary is a real obstruction: its zero-sum direction
  vanishes, so no radial rule can turn a nondeterministic uniform scalar law
  into a Born-normalized one.  A fully symmetric parent therefore requires a
  mixed/operator-valued treatment or additional symmetry-breaking data.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalHolonomyBornProjectiveGrowth
open UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning

universe u

/-! ## 1. Uniform plus zero-sum decomposition at arbitrary finite rank -/

/-- The invariant amplitude carried by one member of a nonempty finite branch
type. -/
def finiteUniformAmplitude (Branch : Type u) [Fintype Branch] : ℂ :=
  ((Fintype.card Branch : ℂ))⁻¹

/-- Projection away from the invariant line. -/
def finiteCenteredAmplitude {Branch : Type u} [Fintype Branch]
    (amplitude : Branch → ℂ) (branch : Branch) : ℂ :=
  amplitude branch - finiteUniformAmplitude Branch

/-- Squared Hilbert norm of a finite scalar amplitude, retained as a complex
number so it composes directly with the operator normalization equations. -/
def finiteComplexBornMass {Branch : Type u} [Fintype Branch]
    (amplitude : Branch → ℂ) : ℂ :=
  ∑ branch, star (amplitude branch) * amplitude branch

/-- Radial correction on the standard zero-sum representation. -/
def finiteBornShellCorrection {Branch : Type u} [Fintype Branch]
    (scale : ℂ) (amplitude : Branch → ℂ) (branch : Branch) : ℂ :=
  finiteUniformAmplitude Branch +
    scale * finiteCenteredAmplitude amplitude branch

theorem finiteUniformAmplitude_sum_one
    (Branch : Type u) [Fintype Branch] [Nonempty Branch] :
    ∑ _branch : Branch, finiteUniformAmplitude Branch = 1 := by
  classical
  have hCard : Fintype.card Branch ≠ 0 := Fintype.card_ne_zero
  simp [finiteUniformAmplitude, hCard, nsmul_eq_mul]

theorem finiteCenteredAmplitude_sum_zero
    {Branch : Type u} [Fintype Branch] [Nonempty Branch]
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1) :
    ∑ branch, finiteCenteredAmplitude amplitude branch = 0 := by
  classical
  simp only [finiteCenteredAmplitude, Finset.sum_sub_distrib]
  rw [hCoherent, finiteUniformAmplitude_sum_one]
  ring

/-- Every radial correction preserves coherent normalization. -/
theorem finiteBornShellCorrection_sum_one
    {Branch : Type u} [Fintype Branch] [Nonempty Branch]
    (scale : ℂ) (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1) :
    ∑ branch, finiteBornShellCorrection scale amplitude branch = 1 := by
  classical
  unfold finiteBornShellCorrection
  rw [Finset.sum_add_distrib, finiteUniformAmplitude_sum_one]
  rw [← Finset.mul_sum, finiteCenteredAmplitude_sum_zero amplitude hCoherent]
  ring

/-! ## 2. Pythagoras and the general Born-shell criterion -/

/-- The uniform and zero-sum components are orthogonal. -/
theorem finiteCenteredAmplitude_bornMass
    {Branch : Type u} [Fintype Branch] [Nonempty Branch]
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1) :
    finiteComplexBornMass (finiteCenteredAmplitude amplitude) =
      finiteComplexBornMass amplitude - finiteUniformAmplitude Branch := by
  classical
  let uniform : ℂ := finiteUniformAmplitude Branch
  have hUniformSum : ∑ _branch : Branch, uniform = 1 := by
    simpa [uniform] using finiteUniformAmplitude_sum_one Branch
  have hStarSum : ∑ branch, star (amplitude branch) = 1 := by
    calc
      (∑ branch, star (amplitude branch)) =
          star (∑ branch, amplitude branch) := by
            rw [star_sum]
      _ = 1 := by rw [hCoherent]; simp
  have hUniformStar : star uniform = uniform := by
    simp [uniform, finiteUniformAmplitude]
  have hUniformNorm :
      (Fintype.card Branch : ℂ) * (uniform * uniform) = uniform := by
    have hCard : (Fintype.card Branch : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card Branch ≠ 0)
    simp [uniform, finiteUniformAmplitude, hCard]
  unfold finiteComplexBornMass
  calc
    (∑ branch,
        star (finiteCenteredAmplitude amplitude branch) *
          finiteCenteredAmplitude amplitude branch) =
      ∑ branch,
        (star (amplitude branch) * amplitude branch -
          uniform * star (amplitude branch) -
          uniform * amplitude branch + uniform * uniform) := by
        apply Finset.sum_congr rfl
        intro branch _hBranch
        simp only [finiteCenteredAmplitude, uniform, hUniformStar,
          star_sub]
        ring
    _ = (∑ branch, star (amplitude branch) * amplitude branch) -
          uniform * (∑ branch, star (amplitude branch)) -
          uniform * (∑ branch, amplitude branch) +
          (Fintype.card Branch : ℂ) * (uniform * uniform) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        ring
    _ = (∑ branch, star (amplitude branch) * amplitude branch) -
          uniform := by
        rw [hStarSum, hCoherent, hUniformNorm]
        ring
    _ = _ := by rfl

/-- Arbitrary-rank Born-shell theorem. -/
theorem finiteBornShellCorrection_bornMass_one
    {Branch : Type u} [Fintype Branch] [Nonempty Branch]
    (scale : ℂ) (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1)
    (hScale :
      star scale * scale *
          (finiteComplexBornMass amplitude - finiteUniformAmplitude Branch) =
        1 - finiteUniformAmplitude Branch) :
    finiteComplexBornMass (finiteBornShellCorrection scale amplitude) = 1 := by
  classical
  let uniform : ℂ := finiteUniformAmplitude Branch
  let centered : Branch → ℂ := finiteCenteredAmplitude amplitude
  have hCenteredSum : ∑ branch, centered branch = 0 := by
    simpa [centered] using finiteCenteredAmplitude_sum_zero amplitude hCoherent
  have hStarCenteredSum : ∑ branch, star (centered branch) = 0 := by
    calc
      (∑ branch, star (centered branch)) =
          star (∑ branch, centered branch) := by rw [star_sum]
      _ = 0 := by rw [hCenteredSum]; simp
  have hCenteredMass : finiteComplexBornMass centered =
      finiteComplexBornMass amplitude - uniform := by
    simpa [centered, uniform] using
      finiteCenteredAmplitude_bornMass amplitude hCoherent
  have hUniformStar : star uniform = uniform := by
    simp [uniform, finiteUniformAmplitude]
  have hUniformNorm :
      (Fintype.card Branch : ℂ) * (uniform * uniform) = uniform := by
    have hCard : (Fintype.card Branch : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card Branch ≠ 0)
    simp [uniform, finiteUniformAmplitude, hCard]
  unfold finiteComplexBornMass
  calc
    (∑ branch,
        star (finiteBornShellCorrection scale amplitude branch) *
          finiteBornShellCorrection scale amplitude branch) =
      ∑ branch,
        (uniform * uniform +
          uniform * scale * centered branch +
          uniform * star scale * star (centered branch) +
          (star scale * scale) *
            (star (centered branch) * centered branch)) := by
        apply Finset.sum_congr rfl
        intro branch _hBranch
        simp only [finiteBornShellCorrection, uniform, centered,
          hUniformStar, star_add, StarMul.star_mul]
        ring

    _ = (Fintype.card Branch : ℂ) * (uniform * uniform) +
          uniform * scale * (∑ branch, centered branch) +
          uniform * star scale * (∑ branch, star (centered branch)) +
          (star scale * scale) *
            (∑ branch, star (centered branch) * centered branch) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ, ← Finset.mul_sum]
    _ = uniform + (star scale * scale) *
      (finiteComplexBornMass amplitude - uniform) := by
        rw [hUniformNorm, hCenteredSum, hStarCenteredSum]
        simp only [mul_zero, add_zero]
        rw [show (∑ branch, star (centered branch) * centered branch) =
            finiteComplexBornMass centered by rfl, hCenteredMass]
    _ = 1 := by
        rw [show star scale * scale *
            (finiteComplexBornMass amplitude - uniform) = 1 - uniform by
          simpa [uniform] using hScale]
        ring

/-- Away from the uniform boundary, coherent and Born normalization determine
the squared radial modulus uniquely.  The remaining phase is a genuine
unitary freedom of the zero-sum carrier, not a normalization ambiguity. -/
theorem finiteBornShell_scale_normSq_unique
    {Branch : Type u} [Fintype Branch]
    (amplitude : Branch → ℂ) (first second : ℂ)
    (hNonuniform :
      finiteComplexBornMass amplitude - finiteUniformAmplitude Branch ≠ 0)
    (hFirst :
      star first * first *
          (finiteComplexBornMass amplitude - finiteUniformAmplitude Branch) =
        1 - finiteUniformAmplitude Branch)
    (hSecond :
      star second * second *
          (finiteComplexBornMass amplitude - finiteUniformAmplitude Branch) =
        1 - finiteUniformAmplitude Branch) :
    star first * first = star second * second := by
  exact mul_right_cancel₀ hNonuniform (hFirst.trans hSecond.symm)

/-! ## 3. The symmetric boundary obstruction -/

theorem finiteCenteredAmplitude_uniform_eq_zero
    (Branch : Type u) [Fintype Branch]
    (branch : Branch) :
    finiteCenteredAmplitude (fun _ : Branch => finiteUniformAmplitude Branch)
        branch = 0 := by
  simp [finiteCenteredAmplitude]

/-- Every radial correction fixes the completely uniform amplitude. -/
theorem finiteBornShellCorrection_uniform_fixed
    (Branch : Type u) [Fintype Branch] (scale : ℂ) :
    finiteBornShellCorrection scale
        (fun _ : Branch => finiteUniformAmplitude Branch) =
      (fun _ : Branch => finiteUniformAmplitude Branch) := by
  funext branch
  simp [finiteBornShellCorrection,
    finiteCenteredAmplitude_uniform_eq_zero]

/-- For more than one branch the uniform scalar amplitude has Born mass
strictly below one, so no radial correction can repair it. -/
theorem finiteUniformAmplitude_bornMass_lt_one
    (Branch : Type u) [Fintype Branch] [Nonempty Branch]
    (hMultiple : 1 < Fintype.card Branch) :
    (finiteComplexBornMass
      (fun _ : Branch => finiteUniformAmplitude Branch)).re < 1 := by
  have hCardPositive : (0 : ℝ) < Fintype.card Branch := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Branch)
  have hCardOne : (1 : ℝ) < Fintype.card Branch := by exact_mod_cast hMultiple
  simp [finiteComplexBornMass, finiteUniformAmplitude,
    Complex.normSq_apply, nsmul_eq_mul]
  field_simp
  nlinarith

theorem no_radial_Born_repair_of_uniform_branching
    (Branch : Type u) [Fintype Branch] [Nonempty Branch]
    (hMultiple : 1 < Fintype.card Branch) (scale : ℂ) :
    finiteComplexBornMass
        (finiteBornShellCorrection scale
          (fun _ : Branch => finiteUniformAmplitude Branch)) ≠ 1 := by
  rw [finiteBornShellCorrection_uniform_fixed]
  intro hOne
  have hReal := congrArg Complex.re hOne
  norm_num at hReal
  have hLt := finiteUniformAmplitude_bornMass_lt_one Branch hMultiple
  linarith

/-! ## 4. Permutation covariance -/

/-- Relabel a finite amplitude along an equivalence. -/
def transportFiniteAmplitude {Branch Branch' : Type u}
    (equivalence : Branch ≃ Branch') (amplitude : Branch → ℂ) : Branch' → ℂ :=
  fun branch' => amplitude (equivalence.symm branch')

theorem finiteBornShellCorrection_equivariant
    {Branch Branch' : Type u} [Fintype Branch] [Fintype Branch']
    (equivalence : Branch ≃ Branch') (scale : ℂ) (amplitude : Branch → ℂ) :
    transportFiniteAmplitude equivalence
        (finiteBornShellCorrection scale amplitude) =
      finiteBornShellCorrection scale
        (transportFiniteAmplitude equivalence amplitude) := by
  funext branch'
  simp [transportFiniteAmplitude, finiteBornShellCorrection,
    finiteCenteredAmplitude, finiteUniformAmplitude,
    Fintype.card_congr equivalence]

/-- General law: every nonuniform coherent finite amplitude can be completed
by a permutation-equivariant radial action on its zero-sum carrier, while the
uniform multi-branch boundary has no such scalar completion. -/
theorem finiteBornShell_general_capstone
    {Branch : Type u} [Fintype Branch] [Nonempty Branch]
    (amplitude : Branch → ℂ) (scale : ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1)
    (hScale :
      star scale * scale *
          (finiteComplexBornMass amplitude - finiteUniformAmplitude Branch) =
        1 - finiteUniformAmplitude Branch) :
    (∑ branch, finiteBornShellCorrection scale amplitude branch = 1)
      ∧ finiteComplexBornMass
          (finiteBornShellCorrection scale amplitude) = 1 := by
  exact ⟨finiteBornShellCorrection_sum_one scale amplitude hCoherent,
    finiteBornShellCorrection_bornMass_one scale amplitude hCoherent hScale⟩

/-! ## 5. Support-relative completion for physical branching

The ambient rank contains many causets which are not one-element extensions
of the current parent.  Centering over that ambient type would assign a
nonzero uniform component to forbidden births.  The correct carrier is the
zero-sum representation of the *physical successor support*.
-/

/-- Uniform amplitude on a specified finite support. -/
def supportUniformAmplitude {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) : ℂ :=
  (support.card : ℂ)⁻¹

/-- Centering relative to the admissible support only. -/
def supportCenteredAmplitude {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (branch : Branch) : ℂ :=
  amplitude branch - supportUniformAmplitude support

/-- Born mass carried by the admissible support. -/
def supportComplexBornMass {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) : ℂ :=
  ∑ branch ∈ support, star (amplitude branch) * amplitude branch

/-- Extend the support-relative radial correction by zero away from the
admissible transition graph. -/
def finiteSupportBornShellCorrection {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (scale : ℂ) (amplitude : Branch → ℂ)
    (branch : Branch) : ℂ := by
  classical
  exact if branch ∈ support then
      supportUniformAmplitude support +
        scale * supportCenteredAmplitude support amplitude branch
    else 0

theorem supportUniformAmplitude_sum_one
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty) :
    ∑ _branch ∈ support, supportUniformAmplitude support = 1 := by
  have hCard : support.card ≠ 0 := Finset.card_ne_zero.mpr hSupport
  simp [supportUniformAmplitude, hCard, nsmul_eq_mul]

theorem supportUniformAmplitude_bornMass
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty) :
    supportComplexBornMass support
        (fun _ : Branch => supportUniformAmplitude support) =
      supportUniformAmplitude support := by
  have hCard : (support.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hSupport)
  have hStar : star (supportUniformAmplitude support) =
      supportUniformAmplitude support := by
    simp [supportUniformAmplitude]
  unfold supportComplexBornMass
  simp only [hStar, Finset.sum_const, nsmul_eq_mul]
  simp [supportUniformAmplitude, hCard]

theorem supportUniformAmplitude_re_lt_one
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hMultiple : 1 < support.card) :
    (supportUniformAmplitude support).re < 1 := by
  have hCardPositive : (0 : ℝ) < support.card := by
    exact_mod_cast (Nat.zero_lt_of_lt hMultiple)
  have hCardOne : (1 : ℝ) < support.card := by exact_mod_cast hMultiple
  simp [supportUniformAmplitude]
  field_simp
  nlinarith

/-- A multi-successor isotropic parent cannot satisfy the scalar Born-shell
equation: there is no zero-sum direction on which a radial action can work. -/
theorem no_support_Born_scale_of_uniform_branching
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (hMultiple : 1 < support.card) (scale : ℂ) :
    ¬ (star scale * scale *
        (supportComplexBornMass support
            (fun _ : Branch => supportUniformAmplitude support) -
          supportUniformAmplitude support) =
      1 - supportUniformAmplitude support) := by
  intro hScale
  rw [supportUniformAmplitude_bornMass support hSupport] at hScale
  simp only [sub_self, mul_zero] at hScale
  have hReal := congrArg Complex.re hScale
  norm_num at hReal
  have hLt := supportUniformAmplitude_re_lt_one support hMultiple
  linarith

/-- Canonical nonnegative radial scale determined by a positive support Born
excess. -/
def supportBornShellScale {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (excess : ℝ) : ℂ :=
  (Real.sqrt
    ((1 - (support.card : ℝ)⁻¹) / excess) : ℝ)

/-- Strict excess above the uniform Cauchy floor is sufficient to solve the
Born-shell equation, with an explicit nonnegative real scale. -/
theorem supportBornShellScale_solves_of_strict_excess
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hMultiple : 1 < support.card)
    (amplitude : Branch → ℂ) (excess : ℝ) (hExcessPositive : 0 < excess)
    (hExcess :
      supportComplexBornMass support amplitude -
          supportUniformAmplitude support = (excess : ℂ)) :
    star (supportBornShellScale support excess) *
        supportBornShellScale support excess *
        (supportComplexBornMass support amplitude -
          supportUniformAmplitude support) =
      1 - supportUniformAmplitude support := by
  have hCardPositive : (0 : ℝ) < support.card := by
    exact_mod_cast (Nat.zero_lt_of_lt hMultiple)
  have hCardOne : (1 : ℝ) < support.card := by exact_mod_cast hMultiple
  have hInvLt : (support.card : ℝ)⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ hCardOne
  have hGapNonnegative :
      0 ≤ 1 - (support.card : ℝ)⁻¹ := le_of_lt (sub_pos.mpr hInvLt)
  have hRatioNonnegative :
      0 ≤ (1 - (support.card : ℝ)⁻¹) / excess :=
    div_nonneg hGapNonnegative (le_of_lt hExcessPositive)
  rw [hExcess]
  unfold supportBornShellScale supportUniformAmplitude
  rw [show star ((Real.sqrt
      ((1 - (support.card : ℝ)⁻¹) / excess) : ℝ) : ℂ) =
      ((Real.sqrt
        ((1 - (support.card : ℝ)⁻¹) / excess) : ℝ) : ℂ) by simp]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [show Real.sqrt ((1 - (support.card : ℝ)⁻¹) / excess) *
      Real.sqrt ((1 - (support.card : ℝ)⁻¹) / excess) =
        (1 - (support.card : ℝ)⁻¹) / excess by
    simpa [pow_two] using Real.sq_sqrt hRatioNonnegative]
  rw [div_mul_cancel₀ _ (ne_of_gt hExcessPositive)]
  simp

theorem supportCenteredAmplitude_sum_zero
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1) :
    ∑ branch ∈ support,
        supportCenteredAmplitude support amplitude branch = 0 := by
  simp only [supportCenteredAmplitude, Finset.sum_sub_distrib]
  rw [hCoherent, supportUniformAmplitude_sum_one support hSupport]
  ring

theorem finiteSupportBornShellCorrection_sum_one
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (scale : ℂ) (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1) :
    ∑ branch, finiteSupportBornShellCorrection support scale amplitude branch = 1 := by
  classical
  unfold finiteSupportBornShellCorrection
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_add_distrib, supportUniformAmplitude_sum_one support hSupport]
  rw [← Finset.mul_sum,
    supportCenteredAmplitude_sum_zero support hSupport amplitude hCoherent]
  ring

/-- Support-relative Pythagoras theorem. -/
theorem supportCenteredAmplitude_bornMass
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1) :
    supportComplexBornMass support
        (supportCenteredAmplitude support amplitude) =
      supportComplexBornMass support amplitude -
        supportUniformAmplitude support := by
  classical
  let uniform : ℂ := supportUniformAmplitude support
  have hStarSum : ∑ branch ∈ support, star (amplitude branch) = 1 := by
    calc
      (∑ branch ∈ support, star (amplitude branch)) =
          star (∑ branch ∈ support, amplitude branch) := by
            rw [star_sum]
      _ = 1 := by rw [hCoherent]; simp
  have hUniformStar : star uniform = uniform := by
    simp [uniform, supportUniformAmplitude]
  have hUniformNorm :
      (support.card : ℂ) * (uniform * uniform) = uniform := by
    have hCard : (support.card : ℂ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hSupport)
    simp [uniform, supportUniformAmplitude, hCard]
  unfold supportComplexBornMass
  calc
    (∑ branch ∈ support,
        star (supportCenteredAmplitude support amplitude branch) *
          supportCenteredAmplitude support amplitude branch) =
      ∑ branch ∈ support,
        (star (amplitude branch) * amplitude branch -
          uniform * star (amplitude branch) -
          uniform * amplitude branch + uniform * uniform) := by
        apply Finset.sum_congr rfl
        intro branch _hBranch
        simp only [supportCenteredAmplitude, uniform, hUniformStar, star_sub]
        ring
    _ = (∑ branch ∈ support,
          star (amplitude branch) * amplitude branch) -
          uniform * (∑ branch ∈ support, star (amplitude branch)) -
          uniform * (∑ branch ∈ support, amplitude branch) +
          (support.card : ℂ) * (uniform * uniform) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (∑ branch ∈ support,
          star (amplitude branch) * amplitude branch) - uniform := by
        rw [hStarSum, hCoherent, hUniformNorm]
        ring
    _ = _ := by rfl

/-- The real squared norm of the support-relative zero-sum component. -/
def supportBornExcess {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ) : ℝ :=
  ∑ branch ∈ support,
    Complex.normSq (supportCenteredAmplitude support amplitude branch)

theorem supportBornExcess_eq_complex_difference
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1) :
    (supportBornExcess support amplitude : ℂ) =
      supportComplexBornMass support amplitude -
        supportUniformAmplitude support := by
  rw [← supportCenteredAmplitude_bornMass support hSupport amplitude hCoherent]
  unfold supportBornExcess supportComplexBornMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro branch _hBranch
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem supportBornExcess_pos_of_nonuniform
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (amplitude : Branch → ℂ)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    0 < supportBornExcess support amplitude := by
  obtain ⟨branch, hBranch, hDifferent⟩ := hNonuniform
  unfold supportBornExcess
  apply Finset.sum_pos'
  · intro other _hOther
    exact Complex.normSq_nonneg _
  · refine ⟨branch, hBranch, Complex.normSq_pos.mpr ?_⟩
    simpa [supportCenteredAmplitude, sub_ne_zero] using hDifferent

/-- Every coherent nonuniform amplitude on a multi-element support admits an
explicit nonnegative radial Born-shell scale. -/
theorem exists_support_Born_scale_of_nonuniform
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (hMultiple : 1 < support.card) (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (hNonuniform : ∃ branch ∈ support,
      amplitude branch ≠ supportUniformAmplitude support) :
    ∃ scale : ℂ,
      star scale * scale *
          (supportComplexBornMass support amplitude -
            supportUniformAmplitude support) =
        1 - supportUniformAmplitude support := by
  let excess := supportBornExcess support amplitude
  have hExcessPositive : 0 < excess :=
    supportBornExcess_pos_of_nonuniform support amplitude hNonuniform
  refine ⟨supportBornShellScale support excess, ?_⟩
  apply supportBornShellScale_solves_of_strict_excess support hMultiple
    amplitude excess hExcessPositive
  exact (supportBornExcess_eq_complex_difference
    support hSupport amplitude hCoherent).symm

theorem finiteSupportBornShellCorrection_bornMass_one
    {Branch : Type u} [Fintype Branch]
    (support : Finset Branch) (hSupport : support.Nonempty)
    (scale : ℂ) (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch ∈ support, amplitude branch = 1)
    (hScale :
      star scale * scale *
          (supportComplexBornMass support amplitude -
            supportUniformAmplitude support) =
        1 - supportUniformAmplitude support) :
    finiteComplexBornMass
        (finiteSupportBornShellCorrection support scale amplitude) = 1 := by
  classical
  let uniform : ℂ := supportUniformAmplitude support
  let centered : Branch → ℂ := supportCenteredAmplitude support amplitude
  have hCenteredSum : ∑ branch ∈ support, centered branch = 0 := by
    simpa [centered] using
      supportCenteredAmplitude_sum_zero support hSupport amplitude hCoherent
  have hStarCenteredSum :
      ∑ branch ∈ support, star (centered branch) = 0 := by
    calc
      (∑ branch ∈ support, star (centered branch)) =
          star (∑ branch ∈ support, centered branch) := by
            rw [star_sum]
      _ = 0 := by rw [hCenteredSum]; simp
  have hCenteredMass : supportComplexBornMass support centered =
      supportComplexBornMass support amplitude - uniform := by
    simpa [centered, uniform] using
      supportCenteredAmplitude_bornMass support hSupport amplitude hCoherent
  have hUniformStar : star uniform = uniform := by
    simp [uniform, supportUniformAmplitude]
  have hUniformNorm :
      (support.card : ℂ) * (uniform * uniform) = uniform := by
    have hCard : (support.card : ℂ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hSupport)
    simp [uniform, supportUniformAmplitude, hCard]
  unfold finiteComplexBornMass finiteSupportBornShellCorrection
  change (∑ branch,
    star (if branch ∈ support then
      uniform + scale * centered branch else 0) *
    (if branch ∈ support then
      uniform + scale * centered branch else 0)) = 1
  calc
    (∑ branch,
        star (if branch ∈ support then
          uniform + scale * centered branch else 0) *
        (if branch ∈ support then
          uniform + scale * centered branch else 0)) =
      ∑ branch ∈ support,
        star (if branch ∈ support then
          uniform + scale * centered branch else 0) *
        (if branch ∈ support then
          uniform + scale * centered branch else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro branch _hUniv hNotMem
        simp [hNotMem]
    _ = ∑ branch ∈ support,
        (uniform * uniform +
          uniform * scale * centered branch +
          uniform * star scale * star (centered branch) +
          (star scale * scale) *
            (star (centered branch) * centered branch)) := by
        apply Finset.sum_congr rfl
        intro branch hBranch
        simp only [if_pos hBranch, hUniformStar, star_add, StarMul.star_mul]
        ring
    _ = (support.card : ℂ) * (uniform * uniform) +
          uniform * scale * (∑ branch ∈ support, centered branch) +
          uniform * star scale *
            (∑ branch ∈ support, star (centered branch)) +
          (star scale * scale) *
            (∑ branch ∈ support,
              star (centered branch) * centered branch) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
    _ = uniform + (star scale * scale) *
          (supportComplexBornMass support amplitude - uniform) := by
        rw [hUniformNorm, hCenteredSum, hStarCenteredSum]
        simp only [mul_zero, add_zero]
        rw [show (∑ branch ∈ support,
            star (centered branch) * centered branch) =
              supportComplexBornMass support centered by rfl, hCenteredMass]
    _ = 1 := by
        rw [show star scale * scale *
            (supportComplexBornMass support amplitude - uniform) =
              1 - uniform by simpa [uniform] using hScale]
        ring

/-! ## 6. All-rank physical causal completion -/

/-- Coherent aggregation over raw precursor slots has exact physical support
for every covariant edge law, independently of its weights. -/
theorem unlabeledAggregatedCausalEdgeAmplitude_eq_zero_of_not_physical
    (edgeLaw : CovariantComplexCausalEdgeAmplitude) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hNotPhysical : ¬ IsUnlabeledOneElementExtension parent child) :
    unlabeledAggregatedCausalEdgeAmplitude edgeLaw parent child = 0 := by
  revert hNotPhysical
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative hNotPhysicalRepresentative
  have hCard : Fintype.card
      (LabeledCausalTransitionFiber parentRepresentative child) = 0 := by
    change labeledCausalTransitionMultiplicity parentRepresentative child = 0
    exact causalTransitionMultiplicity_eq_zero_of_not_physical
      (Quotient.mk _ parentRepresentative) child hNotPhysicalRepresentative
  letI : IsEmpty (LabeledCausalTransitionFiber parentRepresentative child) :=
    Fintype.card_eq_zero_iff.mp hCard
  simp [unlabeledAggregatedCausalEdgeAmplitude,
    labeledAggregatedCausalEdgeAmplitude]

/-- The actual harmonic critical transition is supported exactly on genuine
one-element unlabeled causal extensions. -/
theorem harmonicCriticalTransition_eq_zero_of_not_physical
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hNotPhysical : ¬ IsUnlabeledOneElementExtension parent child) :
    harmonicCriticalTransition chirality parent child = 0 := by
  unfold harmonicCriticalTransition
  rw [unlabeledAggregatedCausalEdgeAmplitude_eq_zero_of_not_physical
    (interactingChiralCausalEdgeAmplitude
      (harmonicCriticalPairCoupling n) chirality)
    parent child hNotPhysical]
  simp

theorem harmonicCriticalTransition_sum_on_physical_support
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ child ∈ physicalCausalSuccessors n pathPrefix,
        (harmonicCriticalCausalSetGrowthLaw chirality).transition
          n pathPrefix child = 1 := by
  change ∑ child ∈ physicalCausalSuccessors n pathPrefix,
      harmonicCriticalTransition chirality
        (currentUnlabeledCausalOrder n pathPrefix) child = 1
  rw [Finset.sum_subset (Finset.subset_univ _) (fun child _hAll hNotMem =>
    harmonicCriticalTransition_eq_zero_of_not_physical chirality
      (currentUnlabeledCausalOrder n pathPrefix) child (by
        simpa [physicalCausalSuccessors] using hNotMem))]
  exact harmonicCriticalTransition_sum_one chirality
    (currentUnlabeledCausalOrder n pathPrefix)

/-- The exact data needed to promote a normalized causal growth law to the
intersection of its coherent-normalization hyperplane and Born unit sphere.
The support field is not optional: it prevents the correction from creating
unphysical causal births. -/
structure PhysicalBornShellProfile
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch) where
  scale : ∀ n : ℕ, RankedGrowthPath CausalSetGrowthBranch n → ℂ
  supported : ∀ (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n),
    ¬ IsPhysicalCausalGrowthStep n pathPrefix child →
      law.transition n pathPrefix child = 0
  compatible : ∀ (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
    star (scale n pathPrefix) * scale n pathPrefix *
        (supportComplexBornMass (physicalCausalSuccessors n pathPrefix)
            (law.transition n pathPrefix) -
          supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)) =
      1 - supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)

/-- For the actual harmonic law, physical support is now a theorem.  Its only
remaining scalar completion datum is therefore a radial scale solving the
local Born equation at every parent. -/
structure HarmonicCriticalBornShellScale (chirality : Fin 2) where
  scale : ∀ n : ℕ, RankedGrowthPath CausalSetGrowthBranch n → ℂ
  compatible : ∀ (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
    star (scale n pathPrefix) * scale n pathPrefix *
        (supportComplexBornMass (physicalCausalSuccessors n pathPrefix)
            ((harmonicCriticalCausalSetGrowthLaw chirality).transition
              n pathPrefix) -
          supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)) =
      1 - supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)

/-- The one remaining all-parent condition after support has been derived:
every genuinely branching harmonic transition must have a nonzero zero-sum
component. -/
def HarmonicCriticalNonuniformOnBranching (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
    1 < (physicalCausalSuccessors n pathPrefix).card →
      ∃ child ∈ physicalCausalSuccessors n pathPrefix,
        (harmonicCriticalCausalSetGrowthLaw chirality).transition
            n pathPrefix child ≠
          supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)

theorem harmonicCritical_local_Born_scale_exists
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (hNonuniform : 1 < (physicalCausalSuccessors n pathPrefix).card →
      ∃ child ∈ physicalCausalSuccessors n pathPrefix,
        (harmonicCriticalCausalSetGrowthLaw chirality).transition
            n pathPrefix child ≠
          supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)) :
    ∃ scale : ℂ,
      star scale * scale *
          (supportComplexBornMass (physicalCausalSuccessors n pathPrefix)
              ((harmonicCriticalCausalSetGrowthLaw chirality).transition
                n pathPrefix) -
            supportUniformAmplitude (physicalCausalSuccessors n pathPrefix)) =
        1 - supportUniformAmplitude
          (physicalCausalSuccessors n pathPrefix) := by
  let support := physicalCausalSuccessors n pathPrefix
  have hSupport : support.Nonempty :=
    physicalCausalSuccessors_nonempty n pathPrefix
  by_cases hSingleton : support.card = 1
  · refine ⟨0, ?_⟩
    simp [supportUniformAmplitude, support, hSingleton]
  · have hMultiple : 1 < support.card := by
      have hPositive := physicalCausalSuccessors_card_pos n pathPrefix
      change 0 < support.card at hPositive
      omega
    apply exists_support_Born_scale_of_nonuniform support hSupport hMultiple
      ((harmonicCriticalCausalSetGrowthLaw chirality).transition n pathPrefix)
    · exact harmonicCriticalTransition_sum_on_physical_support
        chirality n pathPrefix
    · exact hNonuniform hMultiple

/-- Choice of the canonical normalization class at every parent.  The choice
is only of a phase representative; `finiteBornShell_scale_normSq_unique`
already proves that the squared modulus is forced. -/
noncomputable def harmonicCriticalBornShellScaleOfNonuniform
    (chirality : Fin 2)
    (hNonuniform : HarmonicCriticalNonuniformOnBranching chirality) :
    HarmonicCriticalBornShellScale chirality where
  scale := fun n pathPrefix => Classical.choose
    (harmonicCritical_local_Born_scale_exists chirality n pathPrefix
      (hNonuniform n pathPrefix))
  compatible := fun n pathPrefix => Classical.choose_spec
    (harmonicCritical_local_Born_scale_exists chirality n pathPrefix
      (hNonuniform n pathPrefix))

/-- Exact frontier theorem: a scalar all-rank harmonic Born-shell completion
exists if and only if the actual harmonic transition avoids the uniform
multi-successor boundary at every parent. -/
theorem harmonicCriticalBornShellScale_nonempty_iff_nonuniform
    (chirality : Fin 2) :
    Nonempty (HarmonicCriticalBornShellScale chirality) ↔
      HarmonicCriticalNonuniformOnBranching chirality := by
  classical
  constructor
  · rintro ⟨radial⟩ n pathPrefix hMultiple
    let support := physicalCausalSuccessors n pathPrefix
    by_contra hExists
    push_neg at hExists
    have hSupport : support.Nonempty :=
      physicalCausalSuccessors_nonempty n pathPrefix
    have hMass :
        supportComplexBornMass support
            ((harmonicCriticalCausalSetGrowthLaw chirality).transition
              n pathPrefix) =
          supportComplexBornMass support
            (fun _ : CausalSetGrowthBranch n =>
              supportUniformAmplitude support) := by
      unfold supportComplexBornMass
      apply Finset.sum_congr rfl
      intro child hChild
      rw [hExists child hChild]
    have hCompatible := radial.compatible n pathPrefix
    change 1 < support.card at hMultiple
    change star (radial.scale n pathPrefix) * radial.scale n pathPrefix *
        (supportComplexBornMass support
            ((harmonicCriticalCausalSetGrowthLaw chirality).transition
              n pathPrefix) - supportUniformAmplitude support) =
      1 - supportUniformAmplitude support at hCompatible
    rw [hMass] at hCompatible
    exact (no_support_Born_scale_of_uniform_branching
      support hSupport hMultiple (radial.scale n pathPrefix)) hCompatible
  · intro hNonuniform
    exact ⟨harmonicCriticalBornShellScaleOfNonuniform
      chirality hNonuniform⟩

def harmonicCriticalPhysicalBornShellProfile (chirality : Fin 2)
    (radial : HarmonicCriticalBornShellScale chirality) :
    PhysicalBornShellProfile (harmonicCriticalCausalSetGrowthLaw chirality) where
  scale := radial.scale
  supported := by
    intro n pathPrefix child hNotPhysical
    exact harmonicCriticalTransition_eq_zero_of_not_physical chirality
      (currentUnlabeledCausalOrder n pathPrefix) child hNotPhysical
  compatible := radial.compatible

theorem physical_transition_sum_on_support
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ child ∈ physicalCausalSuccessors n pathPrefix,
        law.transition n pathPrefix child = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ _) (fun child _hAll hNotMem =>
    profile.supported n pathPrefix child (by
      simpa [physicalCausalSuccessors] using hNotMem))]
  exact law.normalized n pathPrefix

/-- The support-relative, Born-normalized all-rank causal transition. -/
def physicalBornShellTransition
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) : ℂ :=
  finiteSupportBornShellCorrection
    (physicalCausalSuccessors n pathPrefix) (profile.scale n pathPrefix)
    (law.transition n pathPrefix) child

theorem physicalBornShellTransition_sum_one
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ child, physicalBornShellTransition law profile n pathPrefix child = 1 := by
  exact finiteSupportBornShellCorrection_sum_one
    (physicalCausalSuccessors n pathPrefix)
    (physicalCausalSuccessors_nonempty n pathPrefix)
    (profile.scale n pathPrefix) (law.transition n pathPrefix)
    (physical_transition_sum_on_support law profile n pathPrefix)

def physicalBornShellGrowthLaw
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition := physicalBornShellTransition law profile
  normalized := physicalBornShellTransition_sum_one law profile

theorem physicalBornShellTransition_supported
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    physicalBornShellTransition law profile n pathPrefix child = 0 := by
  simp [physicalBornShellTransition, finiteSupportBornShellCorrection,
    physicalCausalSuccessors, hNotPhysical]

theorem physicalBornShellTransition_bornMass_one
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    finiteComplexBornMass
        (physicalBornShellTransition law profile n pathPrefix) = 1 := by
  exact finiteSupportBornShellCorrection_bornMass_one
    (physicalCausalSuccessors n pathPrefix)
    (physicalCausalSuccessors_nonempty n pathPrefix)
    (profile.scale n pathPrefix) (law.transition n pathPrefix)
    (physical_transition_sum_on_support law profile n pathPrefix)
    (profile.compatible n pathPrefix)

/-- All-rank capstone: whenever the support-relative radial scale exists, one
and the same corrected causal law is physical, coherently normalized, and
Born normalized at every parent. -/
theorem physicalBornShell_all_rank_capstone
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      ∑ child, (physicalBornShellGrowthLaw law profile).transition
        n pathPrefix child = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      finiteComplexBornMass
        ((physicalBornShellGrowthLaw law profile).transition n pathPrefix) = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      ¬ IsPhysicalCausalGrowthStep n pathPrefix child →
        (physicalBornShellGrowthLaw law profile).transition
          n pathPrefix child = 0) := by
  exact ⟨physicalBornShellTransition_sum_one law profile,
    physicalBornShellTransition_bornMass_one law profile,
    physicalBornShellTransition_supported law profile⟩

/-- The all-rank repaired law enters the already-established infinite cylinder
semantics.  Born normalization is new local information; projective
consistency and strong positivity follow from coherent normalization and the
history-amplitude construction. -/
theorem physicalBornShell_infiniteCylinder_promotion
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (profile : PhysicalBornShellProfile law) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (physicalBornShellGrowthLaw law profile) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          ∀ steps,
            growthEventDecoherence
                (finiteRankedDepthDecoherence
                  (physicalBornShellGrowthLaw law profile) (n + steps))
                (refineRankedGrowthEventBy event₁ steps)
                (refineRankedGrowthEventBy event₂ steps) =
              growthEventDecoherence
                (finiteRankedDepthDecoherence
                  (physicalBornShellGrowthLaw law profile) n)
                event₁ event₂)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (physicalBornShellGrowthLaw law profile))
      ∧ infiniteRankedCylinderDecoherence
          (physicalBornShellGrowthLaw law profile)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 := by
  exact ⟨finiteRankedDepthDecoherence_normalized _,
    finiteRankedDepthDecoherence_projective_by _,
    infiniteRankedCylinderDecoherence_stronglyPositive _,
    infiniteRankedCylinderDecoherence_normalized _⟩

def harmonicCriticalBornShellGrowthLaw (chirality : Fin 2)
    (radial : HarmonicCriticalBornShellScale chirality) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  physicalBornShellGrowthLaw (harmonicCriticalCausalSetGrowthLaw chirality)
    (harmonicCriticalPhysicalBornShellProfile chirality radial)

/-- The harmonic specialization is physical and doubly normalized at every
parent once its radial equations are solved. -/
theorem harmonicCriticalBornShell_all_rank (chirality : Fin 2)
    (radial : HarmonicCriticalBornShellScale chirality) :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      ∑ child, (harmonicCriticalBornShellGrowthLaw chirality radial).transition
        n pathPrefix child = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      finiteComplexBornMass
        ((harmonicCriticalBornShellGrowthLaw chirality radial).transition
          n pathPrefix) = 1) ∧
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (child : CausalSetGrowthBranch n),
      ¬ IsPhysicalCausalGrowthStep n pathPrefix child →
        (harmonicCriticalBornShellGrowthLaw chirality radial).transition
          n pathPrefix child = 0) := by
  exact physicalBornShell_all_rank_capstone _ _

/-- Actual-law cylinder promotion.  Once the harmonic radial equations are
solved, no additional support, projectivity, positivity, or infinite-cylinder
axiom is needed. -/
theorem harmonicCriticalBornShell_promotion (chirality : Fin 2)
    (radial : HarmonicCriticalBornShellScale chirality) :
    (∀ n, IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          (harmonicCriticalBornShellGrowthLaw chirality radial) n))
      ∧ (∀ (n) (event₁ event₂ :
            Finset (RankedGrowthPath CausalSetGrowthBranch n)),
          ∀ steps,
            growthEventDecoherence
                (finiteRankedDepthDecoherence
                  (harmonicCriticalBornShellGrowthLaw chirality radial)
                  (n + steps))
                (refineRankedGrowthEventBy event₁ steps)
                (refineRankedGrowthEventBy event₂ steps) =
              growthEventDecoherence
                (finiteRankedDepthDecoherence
                  (harmonicCriticalBornShellGrowthLaw chirality radial) n)
                event₁ event₂)
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteRankedCylinderDecoherence
            (harmonicCriticalBornShellGrowthLaw chirality radial))
      ∧ infiniteRankedCylinderDecoherence
          (harmonicCriticalBornShellGrowthLaw chirality radial)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch)
          (totalInfiniteRankedCylinderEvent CausalSetGrowthBranch) = 1 := by
  exact physicalBornShell_infiniteCylinder_promotion _ _

#print axioms finiteCenteredAmplitude_bornMass
#print axioms finiteBornShellCorrection_bornMass_one
#print axioms finiteBornShell_scale_normSq_unique
#print axioms no_radial_Born_repair_of_uniform_branching
#print axioms finiteBornShellCorrection_equivariant
#print axioms finiteBornShell_general_capstone
#print axioms supportBornShellScale_solves_of_strict_excess
#print axioms exists_support_Born_scale_of_nonuniform
#print axioms supportCenteredAmplitude_bornMass
#print axioms finiteSupportBornShellCorrection_bornMass_one
#print axioms harmonicCriticalTransition_eq_zero_of_not_physical
#print axioms harmonicCriticalBornShellScale_nonempty_iff_nonuniform
#print axioms physicalBornShell_all_rank_capstone
#print axioms physicalBornShell_infiniteCylinder_promotion
#print axioms harmonicCriticalBornShell_all_rank
#print axioms harmonicCriticalBornShell_promotion

end


end UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

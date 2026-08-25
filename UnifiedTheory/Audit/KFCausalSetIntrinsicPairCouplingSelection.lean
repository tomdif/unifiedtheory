/-
  Audit/KFCausalSetIntrinsicPairCouplingSelection.lean

  INTRINSIC SELECTION AUDIT FOR THE ANCESTOR-PAIR COUPLING

  The fixed Liouville coupling in the first complete chiral law is an
  arithmetic zero-freeness witness, not a value selected by causal growth.
  This module tests four genuinely structural alternatives without assuming
  equality with that witness.

  At the full source decomposition of the two-antichain, the effective-pair
  amplitudes are

      1,  2 (±i),  -g.

  Consequently simultaneous coherent and Born normalization of the
  unmodified law forces `g = 0`.  This is an exact no-go for using the second
  normalization to select a nonzero interaction.

  Two independent structural conditions instead have the same nondegenerate
  fixed point.  Requiring singleton components to compose without a cross
  interaction forces `g = 1`; requiring empty/full complement sectors to
  have equal Born weight also forces `g = 1` when `g` is nonnegative.

  Finally, the existing vacuum spectator action gives a finite-rank running
  law.  Event-slot relabeling invariance and unit normalization make each
  newborn contribution `1/(n+1)`; summing from the empty causet fixes the
  rank-two charge to `3/2`, the square-root pair coupling to `7/4`, and the
  effective coupling to `49/16`.  Its effective coupling converges to the
  common structural fixed point `1`.

  Thus the intrinsic result is a parameter-free running trajectory.  It does
  not derive the unrelated fixed transcendental witness, and the final
  theorem proves that the two values are unequal.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection

noncomputable section

open scoped BigOperators ComplexConjugate
open Filter Topology
open Polynomial
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetHarmonicRefinementLaw
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction

/-! ## 1. The complete two-antichain source calculation -/

/-- Coherently aggregated amplitude of one ancestor-count sector above the
two-antichain, written directly in the identifiable effective coupling `g`. -/
def effectiveTwoAntichainSectorAmplitude
    (g : ℝ) (chirality : Fin 2) (sector : Fin 3) : ℂ :=
  (Nat.choose 2 sector.val : ℂ) *
    effectivePairChiralSignatureWeight
      g chirality sector.val sector.val

@[simp]
theorem effectiveTwoAntichainSectorAmplitude_zero
    (g : ℝ) (chirality : Fin 2) :
    effectiveTwoAntichainSectorAmplitude g chirality 0 = 1 := by
  simp [effectiveTwoAntichainSectorAmplitude,
    effectivePairChiralSignatureWeight, ancestorUnorderedPairCount,
    chiralGaussianPower_eq_phase_pow]

@[simp]
theorem effectiveTwoAntichainSectorAmplitude_one
    (g : ℝ) (chirality : Fin 2) :
    effectiveTwoAntichainSectorAmplitude g chirality 1 =
      2 * chiralMaximalEventPhase chirality := by
  simp [effectiveTwoAntichainSectorAmplitude,
    effectivePairChiralSignatureWeight, ancestorUnorderedPairCount,
    chiralGaussianPower_eq_phase_pow]

@[simp]
theorem effectiveTwoAntichainSectorAmplitude_two
    (g : ℝ) (chirality : Fin 2) :
    effectiveTwoAntichainSectorAmplitude g chirality 2 = -(g : ℂ) := by
  fin_cases chirality <;>
    norm_num [effectiveTwoAntichainSectorAmplitude,
      effectivePairChiralSignatureWeight, ancestorUnorderedPairCount,
      chiralGaussianPower_eq_phase_pow, chiralMaximalEventPhase]

/-- Coherent raw parent partition after grouping the four precursor slots into
the three unlabeled ancestor-count sectors. -/
def effectiveTwoAntichainPartition
    (g : ℝ) (chirality : Fin 2) : ℂ :=
  ∑ sector, effectiveTwoAntichainSectorAmplitude g chirality sector

theorem effectiveTwoAntichainPartition_exact
    (g : ℝ) (chirality : Fin 2) :
    effectiveTwoAntichainPartition g chirality =
      1 + 2 * chiralMaximalEventPhase chirality - g := by
  rw [effectiveTwoAntichainPartition, Fin.sum_univ_three,
    effectiveTwoAntichainSectorAmplitude_zero,
    effectiveTwoAntichainSectorAmplitude_one,
    effectiveTwoAntichainSectorAmplitude_two]
  ring

theorem effectiveTwoAntichainPartition_normSq
    (g : ℝ) (chirality : Fin 2) :
    Complex.normSq (effectiveTwoAntichainPartition g chirality) =
      (1 - g) ^ 2 + 4 := by
  rw [effectiveTwoAntichainPartition_exact]
  fin_cases chirality <;>
    norm_num [Complex.normSq_apply, chiralMaximalEventPhase] <;>
    ring

theorem effectiveTwoAntichainPartition_ne_zero
    (g : ℝ) (chirality : Fin 2) :
    effectiveTwoAntichainPartition g chirality ≠ 0 := by
  intro hZero
  have hNorm := effectiveTwoAntichainPartition_normSq g chirality
  rw [hZero] at hNorm
  norm_num [Complex.normSq_apply] at hNorm
  nlinarith [sq_nonneg (1 - g)]

/-- Diagonal Born mass of the three coherent source sectors before dividing
by their common coherent partition. -/
def effectiveTwoAntichainRawBornMass
    (g : ℝ) (chirality : Fin 2) : ℝ :=
  ∑ sector,
    Complex.normSq (effectiveTwoAntichainSectorAmplitude g chirality sector)

theorem effectiveTwoAntichainRawBornMass_exact
    (g : ℝ) (chirality : Fin 2) :
    effectiveTwoAntichainRawBornMass g chirality = g ^ 2 + 5 := by
  rw [effectiveTwoAntichainRawBornMass, Fin.sum_univ_three,
    effectiveTwoAntichainSectorAmplitude_zero,
    effectiveTwoAntichainSectorAmplitude_one,
    effectiveTwoAntichainSectorAmplitude_two]
  fin_cases chirality <;>
    norm_num [Complex.normSq_apply, chiralMaximalEventPhase] <;>
    ring

/-- The ordinary normalized sector amplitudes obtained from the same coherent
partition as the sequential-growth law. -/
def effectiveTwoAntichainNormalizedSectorAmplitude
    (g : ℝ) (chirality : Fin 2) (sector : Fin 3) : ℂ :=
  effectiveTwoAntichainSectorAmplitude g chirality sector /
    effectiveTwoAntichainPartition g chirality

/-- Exact double-normalization no-go: the coherently normalized effective-pair
law is Born normalized on the complete two-antichain source partition exactly
at the degenerate coupling `g = 0`. -/
theorem effectiveTwoAntichain_normalizedBornMass_eq_one_iff
    (g : ℝ) (chirality : Fin 2) :
    (∑ sector,
        Complex.normSq
          (effectiveTwoAntichainNormalizedSectorAmplitude
            g chirality sector)) = 1 ↔
      g = 0 := by
  have hNormNe :
      Complex.normSq (effectiveTwoAntichainPartition g chirality) ≠ 0 := by
    exact (Complex.normSq_eq_zero.not.mpr
      (effectiveTwoAntichainPartition_ne_zero g chirality))
  simp only [effectiveTwoAntichainNormalizedSectorAmplitude,
    Complex.normSq_div, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hNormNe]
  change effectiveTwoAntichainRawBornMass g chirality =
      Complex.normSq (effectiveTwoAntichainPartition g chirality) ↔ g = 0
  rw [
    effectiveTwoAntichainRawBornMass_exact,
    effectiveTwoAntichainPartition_normSq]
  constructor
  · intro h
    nlinarith
  · rintro rfl
    norm_num

/-! ## 2. Two independent routes to the same fixed point -/

/-- At the first nontrivial composition test, two singleton signatures carry
no additional cross interaction.  This is the local fixed-point form of
independent composition, not an equality with a preselected amplitude. -/
def HasNeutralSingletonComposition
    (g : ℝ) (chirality : Fin 2) : Prop :=
  effectivePairChiralSignatureWeight g chirality 2 2 =
    effectivePairChiralSignatureWeight g chirality 1 1 *
      effectivePairChiralSignatureWeight g chirality 1 1

/-- Neutral composition of two singleton components selects `g = 1`. -/
theorem neutralSingletonComposition_iff
    (g : ℝ) (chirality : Fin 2) :
    HasNeutralSingletonComposition g chirality ↔ g = 1 := by
  unfold HasNeutralSingletonComposition
  fin_cases chirality <;>
    norm_num [effectivePairChiralSignatureWeight,
      ancestorUnorderedPairCount, chiralGaussianPower_eq_phase_pow,
      chiralMaximalEventPhase, Complex.ext_iff]

/-- Complement balance compares the Born weights of the empty and full
precursor sectors of the two-antichain. -/
def HasTwoAntichainExtremeBornBalance
    (g : ℝ) (chirality : Fin 2) : Prop :=
  Complex.normSq (effectiveTwoAntichainSectorAmplitude g chirality 0) =
    Complex.normSq (effectiveTwoAntichainSectorAmplitude g chirality 2)

/-- For a nonnegative physical coupling, empty/full complement balance also
selects the same fixed point `g = 1`. -/
theorem twoAntichainExtremeBornBalance_iff
    (g : ℝ) (chirality : Fin 2) (hg : 0 ≤ g) :
    HasTwoAntichainExtremeBornBalance g chirality ↔ g = 1 := by
  unfold HasTwoAntichainExtremeBornBalance
  rw [effectiveTwoAntichainSectorAmplitude_zero,
    effectiveTwoAntichainSectorAmplitude_two]
  norm_num [Complex.normSq_apply]
  constructor
  · intro h
    nlinarith
  · rintro rfl
    norm_num

/-! ## 3. Vacuum action selection and the running coupling -/

/-- Effective unordered-pair coupling selected at rank `n` by the microscopic
vacuum spectator action. -/
def microscopicSpectatorEffectivePairCoupling
    (action : VacuumSpectatorCausalAction) (n : ℕ) : ℝ :=
  effectivePairCoupling (microscopicSpectatorPairCoupling action n)

/-- Vacuum accumulation fixes the rank-two square-root pair coupling to
`7/4`; it is not a free boundary datum. -/
theorem microscopicSpectatorPairCoupling_rankTwo
    (action : VacuumSpectatorCausalAction) :
    microscopicSpectatorPairCoupling action 2 = 7 / 4 := by
  rw [microscopicSpectatorPairCoupling_eq_harmonic]
  norm_num [harmonicCriticalPairCoupling,
    harmonicCriticalPairCouplingQ, harmonic, Finset.sum_range_succ]

/-- The identifiable effective coupling at rank two is therefore `49/16`. -/
theorem microscopicSpectatorEffectivePairCoupling_rankTwo
    (action : VacuumSpectatorCausalAction) :
    microscopicSpectatorEffectivePairCoupling action 2 = 49 / 16 := by
  rw [microscopicSpectatorEffectivePairCoupling, effectivePairCoupling,
    microscopicSpectatorPairCoupling_rankTwo]
  norm_num

/-- The action-selected running effective coupling converges to the unique
nonnegative complement-balanced, composition-neutral fixed point. -/
theorem microscopicSpectatorEffectivePairCoupling_tendsto_one
    (action : VacuumSpectatorCausalAction) :
    Tendsto (microscopicSpectatorEffectivePairCoupling action)
      atTop (nhds 1) := by
  have h := microscopicSpectatorPairCoupling_tendsto_one action
  change Tendsto
    (fun n => microscopicSpectatorPairCoupling action n ^ 2)
    atTop (nhds 1)
  simpa [pow_two] using h.mul h

/-- The fixed transcendental zero-freeness witness is not the rank-two value
selected by the intrinsic vacuum action. -/
theorem canonicalEffectivePairCoupling_ne_microscopicRankTwo
    (action : VacuumSpectatorCausalAction) :
    effectivePairCoupling canonicalPairCoupling ≠
      microscopicSpectatorEffectivePairCoupling action 2 := by
  rw [microscopicSpectatorEffectivePairCoupling_rankTwo]
  intro hEqual
  let obstruction : ℤ[X] := C 16 * X ^ 2 - C 49
  have hScaled :
      16 * canonicalPairCoupling ^ 2 - 49 = 0 := by
    simpa [effectivePairCoupling] using
      (show 16 * effectivePairCoupling canonicalPairCoupling - 49 = 0 by
        nlinarith [hEqual])
  have hEvaluation : Polynomial.aeval canonicalPairCoupling obstruction = 0 := by
    simp only [obstruction, map_sub, map_mul, map_pow, aeval_C, aeval_X]
    norm_num
    exact hScaled
  have hPolynomialZero :=
    (transcendental_iff.mp canonicalPairCoupling_transcendental)
      obstruction hEvaluation
  have hCoefficient :=
    congrArg (fun p : ℤ[X] => p.coeff 2) hPolynomialZero
  norm_num [obstruction, Polynomial.coeff_one] at hCoefficient

/-- Selection capstone.  The vacuum action fixes a nontrivial ultraviolet
value and runs to the common structural fixed point, while raw double
normalization provably selects only the sparse law. -/
theorem intrinsicPairCouplingSelection_capstone
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    microscopicSpectatorEffectivePairCoupling action 2 = 49 / 16
      ∧ Tendsto (microscopicSpectatorEffectivePairCoupling action)
          atTop (nhds 1)
      ∧ HasNeutralSingletonComposition 1 chirality
      ∧ HasTwoAntichainExtremeBornBalance 1 chirality
      ∧ (∀ g : ℝ,
          (∑ sector,
              Complex.normSq
                (effectiveTwoAntichainNormalizedSectorAmplitude
                  g chirality sector)) = 1 ↔ g = 0)
      ∧ effectivePairCoupling canonicalPairCoupling ≠
          microscopicSpectatorEffectivePairCoupling action 2 := by
  exact ⟨microscopicSpectatorEffectivePairCoupling_rankTwo action,
    microscopicSpectatorEffectivePairCoupling_tendsto_one action,
    (neutralSingletonComposition_iff 1 chirality).2 rfl,
    (twoAntichainExtremeBornBalance_iff 1 chirality (by norm_num)).2 rfl,
    fun g => effectiveTwoAntichain_normalizedBornMass_eq_one_iff g chirality,
    canonicalEffectivePairCoupling_ne_microscopicRankTwo action⟩

/-- No-argument specialization: the explicitly constructed vacuum action
inhabits the selection theorem, so the result is not conditional on the
existence of an action record. -/
theorem canonicalVacuum_intrinsicPairCouplingSelection_capstone
    (chirality : Fin 2) :
    microscopicSpectatorEffectivePairCoupling
        canonicalVacuumSpectatorCausalAction 2 = 49 / 16
      ∧ Tendsto
          (microscopicSpectatorEffectivePairCoupling
            canonicalVacuumSpectatorCausalAction) atTop (nhds 1)
      ∧ HasNeutralSingletonComposition 1 chirality
      ∧ HasTwoAntichainExtremeBornBalance 1 chirality
      ∧ (∀ g : ℝ,
          (∑ sector,
              Complex.normSq
                (effectiveTwoAntichainNormalizedSectorAmplitude
                  g chirality sector)) = 1 ↔ g = 0)
      ∧ effectivePairCoupling canonicalPairCoupling ≠
          microscopicSpectatorEffectivePairCoupling
            canonicalVacuumSpectatorCausalAction 2 :=
  intrinsicPairCouplingSelection_capstone
    canonicalVacuumSpectatorCausalAction chirality

#print axioms effectiveTwoAntichain_normalizedBornMass_eq_one_iff
#print axioms neutralSingletonComposition_iff
#print axioms twoAntichainExtremeBornBalance_iff
#print axioms microscopicSpectatorPairCoupling_rankTwo
#print axioms microscopicSpectatorEffectivePairCoupling_rankTwo
#print axioms microscopicSpectatorEffectivePairCoupling_tendsto_one
#print axioms canonicalEffectivePairCoupling_ne_microscopicRankTwo
#print axioms intrinsicPairCouplingSelection_capstone
#print axioms canonicalVacuum_intrinsicPairCouplingSelection_capstone

end

end UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection

/-
  Test the same rank-one BDG action gap after complex partition normalization.

  With real raw magnitudes, the Born sum of the normalized two-child law is
  one exactly when rho_chain * rho_antichain * cos(phi) = 0.  Consequently a
  branching law of this form requires a quarter-turn relative phase.  The
  externally matched phase 4/sqrt(6) has strictly negative cosine and cannot
  reproduce the repository's branching harmonic pair, even after division
  by the complex partition function.  A signed pi/2 phase does reproduce it.

  This is an incompatibility between those specified microscopic choices at
  one actual causal parent.  It does not preclude another growth law, later
  branching, or a modified microscopic action, and is not a physical TOE.
-/

import UnifiedTheory.Audit.KFCausalBDG4DPhaseRankOne
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBDG4DNormalizedPhase

noncomputable section
open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit
open UnifiedTheory.Audit.KFCausalBDG4DPhaseRankOne

/-- The dimensionless phase chosen by the external four-dimensional matching. -/
def matchedPhase : ℝ := 4 / Real.sqrt 6

def partition (phi : ℝ) (rho : Bool → ℝ) : ℂ :=
  ∑ member, rankOneAmplitude phi rho member

def amplitude (phi : ℝ) (rho : Bool → ℝ) (member : Bool) : ℂ :=
  rankOneAmplitude phi rho member / partition phi rho

theorem coherent_normalized (phi : ℝ) (rho : Bool → ℝ)
    (hZ : partition phi rho ≠ 0) : ∑ member, amplitude phi rho member = 1 := by
  simp only [amplitude, ← Finset.sum_div]
  exact div_self hZ

/-- The exact extra condition for Born normalization after coherent partition
normalization.  Real prefactors need not be positive for this identity. -/
theorem born_normalized_iff (phi : ℝ) (rho : Bool → ℝ)
    (hZ : partition phi rho ≠ 0) :
    (∑ member, Complex.normSq (amplitude phi rho member)) = 1 ↔
      rho true * rho false * Real.cos phi = 0 := by
  have hn : Complex.normSq (partition phi rho) ≠ 0 := by
    intro hz
    exact hZ (Complex.normSq_eq_zero.mp hz)
  have hz : partition phi rho =
      rankOneAmplitude phi rho true + rankOneAmplitude phi rho false := by
    simp [partition]
  have hre : (rankOneAmplitude phi rho true *
      (starRingEnd ℂ) (rankOneAmplitude phi rho false)).re =
      rho true * rho false * Real.cos phi := by
    rw [(rankOne_amplitudes phi rho).1, (rankOne_amplitudes phi rho).2]
    simp [Complex.mul_re, Complex.exp_re]
    ring
  simp only [amplitude, Complex.normSq_div, Fintype.sum_bool, ← add_div]
  rw [div_eq_one_iff_eq hn, hz, Complex.normSq_add, hre]
  constructor <;> intro h <;> linarith

theorem matchedPhase_between : Real.pi / 2 < matchedPhase ∧ matchedPhase < Real.pi := by
  have hs : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt (6 : ℝ)) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hlow : (2 : ℝ) < Real.sqrt 6 := by nlinarith
  have hhigh : Real.sqrt (6 : ℝ) < 5 / 2 := by nlinarith
  have hp : Real.pi / 2 < (8 : ℝ) / 5 := by linarith [Real.pi_lt_d2]
  constructor
  · apply lt_trans hp
    unfold matchedPhase
    apply (lt_div_iff₀ hs).2
    nlinarith
  · apply lt_trans (show matchedPhase < 2 from ?_)
      (show (2 : ℝ) < Real.pi from lt_trans (by norm_num) Real.pi_gt_three)
    unfold matchedPhase
    apply (div_lt_iff₀ hs).2
    nlinarith

theorem matchedPhase_cos_negative : Real.cos matchedPhase < 0 := by
  apply Real.cos_neg_of_pi_div_two_lt_of_lt matchedPhase_between.1
  linarith [matchedPhase_between.2, Real.pi_pos]

/-- At the matched phase, an exactly bi-normalized partition law has at most
one nonzero raw branch.  There is no assertion about higher causal ranks. -/
theorem matchedPhase_one_raw_branch_zero (rho : Bool → ℝ)
    (hZ : partition matchedPhase rho ≠ 0)
    (hBorn : (∑ member, Complex.normSq (amplitude matchedPhase rho member)) = 1) :
    rho true = 0 ∨ rho false = 0 := by
  have h := (born_normalized_iff matchedPhase rho hZ).1 hBorn
  have hm : rho true * rho false = 0 :=
    (mul_eq_zero.mp h).resolve_right (ne_of_lt matchedPhase_cos_negative)
  exact mul_eq_zero.mp hm

theorem harmonic_not_matchedPhase (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (rho : Bool → ℝ) (hZ : partition matchedPhase rho ≠ 0) :
    ¬ ∀ member,
      (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition 1 pathPrefix
          (causalTransitionTarget (cardinalCausalAntichain 1) (rankOneCausalPast member)) =
        amplitude matchedPhase rho member := by
  intro h
  have ht := congrArg Complex.normSq (h true)
  have hf := congrArg Complex.normSq (h false)
  change Complex.normSq ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
    1 pathPrefix rankOneTimidChild) = _ at ht
  change Complex.normSq ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
    1 pathPrefix rankOneGregariousChild) = _ at hf
  rw [canonicalHarmonicBorn_rankOne_timid_probability] at ht
  rw [canonicalHarmonicBorn_rankOne_gregarious_probability] at hf
  have hBorn : (∑ member, Complex.normSq (amplitude matchedPhase rho member)) = 1 := by
    rw [Fintype.sum_bool, ← ht, ← hf]
    norm_num
  rcases matchedPhase_one_raw_branch_zero rho hZ hBorn with hr | hr
  · simp [amplitude, rankOneAmplitude, hr] at ht
  · simp [amplitude, rankOneAmplitude, hr] at hf

/-- The exact alternative phase for the canonical harmonic chirality. -/
def harmonicPhase (chirality : Fin 2) : ℝ :=
  if chirality = 0 then -(Real.pi / 2) else Real.pi / 2

theorem harmonicPhase_exp (chirality : Fin 2) :
    Complex.exp (Complex.I * (harmonicPhase chirality : ℂ)) =
      -KFCausalSetBellCausality.chiralMaximalEventPhase chirality := by
  fin_cases chirality <;>
    apply Complex.ext <;>
    simp [harmonicPhase, Complex.exp_re, Complex.exp_im,
      KFCausalSetBellCausality.chiralMaximalEventPhase]

/-- A concrete repair of this local compatibility test: unit raw magnitudes
and the signed quarter-turn reproduce both actual harmonic amplitudes.  This
does not identify that alternative phase with the gravitational matching. -/
theorem harmonicPhase_realizes_harmonic (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    partition (harmonicPhase chirality) (fun _ => 1) ≠ 0 ∧
      ∀ member,
        (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition 1 pathPrefix
            (causalTransitionTarget (cardinalCausalAntichain 1) (rankOneCausalPast member)) =
          amplitude (harmonicPhase chirality) (fun _ => 1) member := by
  have hp : partition (harmonicPhase chirality) (fun _ => 1) =
      1 - KFCausalSetBellCausality.chiralMaximalEventPhase chirality := by
    simp only [partition, Fintype.sum_bool, (rankOne_amplitudes _ _).1,
      (rankOne_amplitudes _ _).2, Complex.ofReal_one, one_mul,
      harmonicPhase_exp, sub_eq_add_neg]
  constructor
  · intro he
    rw [hp] at he
    exact normalizing_partition_nonreal chirality (by rw [he]; simp)
  · intro member
    cases member
    · change _ = rankOneAmplitude _ _ false / partition _ _
      rw [(rankOne_amplitudes _ _).1, hp, harmonicPhase_exp]
      simpa using (complex_normalization_recovers_harmonic chirality pathPrefix).2
    · change _ = rankOneAmplitude _ _ true / partition _ _
      rw [(rankOne_amplitudes _ _).2, hp]
      exact (complex_normalization_recovers_harmonic chirality pathPrefix).1

#print axioms coherent_normalized
#print axioms born_normalized_iff
#print axioms matchedPhase_between
#print axioms matchedPhase_cos_negative
#print axioms matchedPhase_one_raw_branch_zero
#print axioms harmonic_not_matchedPhase
#print axioms harmonicPhase_exp
#print axioms harmonicPhase_realizes_harmonic

end
end UnifiedTheory.Audit.KFCausalBDG4DNormalizedPhase

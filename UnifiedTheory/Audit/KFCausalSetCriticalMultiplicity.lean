/-
  Audit/KFCausalSetCriticalMultiplicity.lean

  MULTIPLICITY CORRECTS THE CRITICAL WINDOW

  The adjacent-sector factor g^omega compares one precursor with one enlarged
  precursor.  It does not include the number of precursor slots in a sector.
  For an (n+1)-antichain there is one timid/full precursor but n+1 precursors
  missing one ancestor.  Two distinct coarse-graining channels result.  The
  incoherent labeled-slot Born-mass ratio is

      (n+1) / g^(2n).

  In the repository's unlabeled dynamics, all isomorphic precursor slots are
  added coherently before taking a squared norm.  Its physical child-sector
  ratio is therefore

      (n+1)^2 / g^(2n).

  Consequently every running law with finite scaled logarithm

      n log g_(n+1) -> kappa

  sends this aggregate ratio to infinity.  In particular, every member of the
  positive-rational family lambda_n=1+(a/b)/(n+1) eventually loses timid
  balance on antichains despite remaining exactly zero-free.

  Coherent unlabeled Born balance instead requires

      2n log g_(n+1) = 2 log(n+1) + O(1),

  exposing a logarithmic correction absent from the earlier one-edge scaling
  criterion.  This theorem does not select that corrected trajectory; it proves
  that finite-kappa critical running cannot be the final infrared law when
  precursor multiplicity matters.
-/

import UnifiedTheory.Audit.KFCausalSetPartitionCoefficientStructure
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetRationalCriticalFamily

/-! ## 1. Exact antichain sector degeneracy -/

/-- Every precursor of an antichain is exactly a finite subset of its events.
This makes the sector degeneracy a theorem about actual causal transition
slots, rather than an independent combinatorial ansatz. -/
def antichainPastEquivFinset (n : ℕ) :
    CausalPastSet (cardinalCausalAntichain n) ≃ Finset (Fin n) where
  toFun past := Finset.univ.filter (fun i => past.mem i = true)
  invFun s :=
    { mem := fun i => decide (i ∈ s)
      downwardClosed := by
        intro x y hx hyx
        have hxy : y = x := by
          simpa [cardinalCausalAntichain] using hyx
        subst y
        exact hx }
  left_inv past := by
    apply CausalPastSet.ext
    funext i
    simp
  right_inv s := by
    ext i
    simp

theorem antichainPastEquivFinset_card (n : ℕ)
    (past : CausalPastSet (cardinalCausalAntichain n)) :
    (antichainPastEquivFinset n past).card = past.ancestorCount := by
  change (Finset.univ.filter (fun i => past.mem i = true)).card =
    Nat.card {i : Fin n // past.mem i = true}
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype
    (Finset.univ.filter (fun i => past.mem i = true)) (by simp)).symm

/-- The actual transition slots in the `omega`-ancestor sector of an
`n`-antichain. -/
def AntichainPrecursorSector (n omega : ℕ) :=
  {past : CausalPastSet (cardinalCausalAntichain n) //
    past.ancestorCount = omega}

def antichainPrecursorSectorEquiv (n omega : ℕ) :
    AntichainPrecursorSector n omega ≃
      {s : Finset (Fin n) // s.card = omega} :=
  Equiv.subtypeEquiv (antichainPastEquivFinset n) (by
    intro past
    constructor
    · intro h
      rw [antichainPastEquivFinset_card]
      exact h
    · intro h
      rw [← antichainPastEquivFinset_card]
      exact h)

noncomputable instance antichainPrecursorSectorFintype (n omega : ℕ) :
    Fintype (AntichainPrecursorSector n omega) :=
  Fintype.ofEquiv {s : Finset (Fin n) // s.card = omega}
    (antichainPrecursorSectorEquiv n omega).symm

/-- The `omega` sector of the actual antichain precursor space has binomial
degeneracy. -/
theorem antichainPrecursorSector_card (n omega : ℕ) :
    Fintype.card (AntichainPrecursorSector n omega) = Nat.choose n omega := by
  exact (Fintype.card_congr (antichainPrecursorSectorEquiv n omega)).trans
    (by simpa using (Fintype.card_finset_len (α := Fin n) omega))

/-- Raw Born mass of the ancestor-number `omega` sector of a `total`-event
antichain.  There are `choose total omega` precursor slots, and each squared
effective pair amplitude is `g^(2 choose(omega,2))`. -/
def antichainBornSectorMass (g : ℝ) (total omega : ℕ) : ℝ :=
  (Nat.choose total omega : ℝ) *
    g ^ (2 * Nat.choose omega 2)

/-- Born mass after the isomorphic antichain precursor slots in one `omega`
sector have first been coherently aggregated into their unlabeled child.  The
binomial multiplicity is therefore squared. -/
def antichainCoherentBornSectorMass (g : ℝ) (total omega : ℕ) : ℝ :=
  (Nat.choose total omega : ℝ) ^ 2 *
    g ^ (2 * Nat.choose omega 2)

/-- Exact aggregate ratio between the one-missing sector and the timid sector
of an `(n+1)`-antichain. -/
theorem antichainOneMissingBornToTimidRatio
    (g : ℝ) (hg : g ≠ 0) (n : ℕ) :
    antichainBornSectorMass g (n + 1) n /
        antichainBornSectorMass g (n + 1) (n + 1) =
      (((n + 1 : ℕ) : ℝ)) / g ^ (2 * n) := by
  simp only [antichainBornSectorMass, Nat.choose_succ_self_right,
    Nat.choose_self, Nat.cast_add, Nat.cast_one, one_mul]
  rw [show Nat.choose (n + 1) 2 = Nat.choose n 2 + n by
    rw [Nat.choose_succ_succ']
    simp [Nat.add_comm]]
  rw [Nat.mul_add, pow_add]
  field_simp

/-- Exact coherent-unlabeled ratio.  This is the channel used by the
repository's aggregated unlabeled transition law; it differs by one extra
factor of `n+1` from the precursor-slot ratio above. -/
theorem antichainCoherentOneMissingBornToTimidRatio
    (g : ℝ) (hg : g ≠ 0) (n : ℕ) :
    antichainCoherentBornSectorMass g (n + 1) n /
        antichainCoherentBornSectorMass g (n + 1) (n + 1) =
      (((n + 1 : ℕ) : ℝ)) ^ 2 / g ^ (2 * n) := by
  simp only [antichainCoherentBornSectorMass, Nat.choose_succ_self_right,
    Nat.choose_self, Nat.cast_add, Nat.cast_one, one_pow, one_mul]
  rw [show Nat.choose (n + 1) 2 = Nat.choose n 2 + n by
    rw [Nat.choose_succ_succ']
    simp [Nat.add_comm]]
  rw [Nat.mul_add, pow_add]
  field_simp

/-- The same ratio for a rank-dependent effective pair coupling.  Index `n`
describes a parent of rank `n+1`. -/
def criticalOneMissingBornToTimidRatio (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) / (g (n + 1)) ^ (2 * n)

/-- The rank-dependent ratio after coherent aggregation to an unlabeled child. -/
def criticalCoherentOneMissingBornToTimidRatio (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ 2 / (g (n + 1)) ^ (2 * n)

/-! ## 2. Every finite-kappa trajectory fails aggregate timid balance -/

theorem criticalOneMissingBornToTimidRatio_tendsto_atTop
    (g : ℕ → ℝ) (kappa : ℝ) (hg : ∀ n, 0 < g n)
    (hlog : Tendsto
      (fun n : ℕ => (n : ℝ) * Real.log (g (n + 1)))
      atTop (nhds kappa)) :
    Tendsto (criticalOneMissingBornToTimidRatio g) atTop atTop := by
  have hTwiceLog : Tendsto
      (fun n : ℕ => 2 * ((n : ℝ) * Real.log (g (n + 1))))
      atTop (nhds (2 * kappa)) := by
    simpa using hlog.const_mul 2
  have hPower : Tendsto (fun n : ℕ => (g (n + 1)) ^ (2 * n))
      atTop (nhds (Real.exp (2 * kappa))) := by
    have hExp : Tendsto
        (fun n : ℕ =>
          Real.exp (2 * ((n : ℝ) * Real.log (g (n + 1)))))
        atTop (nhds (Real.exp (2 * kappa))) :=
      Real.continuous_exp.continuousAt.tendsto.comp hTwiceLog
    apply hExp.congr'
    filter_upwards [] with n
    symm
    calc
      g (n + 1) ^ (2 * n) =
          Real.exp (Real.log (g (n + 1))) ^ (2 * n) := by
        rw [Real.exp_log (hg (n + 1))]
      _ = Real.exp
          (((2 * n : ℕ) : ℝ) * Real.log (g (n + 1))) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp
          (2 * ((n : ℝ) * Real.log (g (n + 1)))) := by
        congr 1
        push_cast
        ring
  have hInv := hPower.inv₀ (ne_of_gt (Real.exp_pos _))
  have hTop := hInv.pos_mul_atTop (inv_pos.mpr (Real.exp_pos _))
    (tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply hTop.congr'
  filter_upwards [] with n
  simp [criticalOneMissingBornToTimidRatio, div_eq_mul_inv, mul_comm]

/-- Finite scaled logarithm also makes the coherently aggregated unlabeled
ratio diverge.  Thus passing from labeled slots to unlabeled children
strengthens, rather than removes, the multiplicity obstruction. -/
theorem criticalCoherentOneMissingBornToTimidRatio_tendsto_atTop
    (g : ℕ → ℝ) (kappa : ℝ) (hg : ∀ n, 0 < g n)
    (hlog : Tendsto
      (fun n : ℕ => (n : ℝ) * Real.log (g (n + 1)))
      atTop (nhds kappa)) :
    Tendsto (criticalCoherentOneMissingBornToTimidRatio g) atTop atTop := by
  have hSlot := criticalOneMissingBornToTimidRatio_tendsto_atTop g kappa hg hlog
  refine tendsto_atTop_mono' atTop ?_ hSlot
  filter_upwards [] with n
  have hden : 0 < (g (n + 1)) ^ (2 * n) := pow_pos (hg (n + 1)) _
  rw [criticalOneMissingBornToTimidRatio,
    criticalCoherentOneMissingBornToTimidRatio,
    div_le_div_iff_of_pos_right hden]
  have hOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith [sq_nonneg ((((n + 1 : ℕ) : ℝ)) - 1)]

/-! ## 3. Application to the positive-rational critical family -/

/-- Every positive-rational finite-kappa schedule has a divergent aggregate
one-missing/timid Born ratio on antichains.  Exact zero-freeness therefore does
not imply aggregate-sector balance. -/
theorem rationalCriticalFamily_oneMissingBornRatio_tendsto_atTop
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (criticalOneMissingBornToTimidRatio
        (rationalCriticalFamilyEffectiveCoupling a b))
      atTop atTop := by
  let g := rationalCriticalFamilyEffectiveCoupling a b
  let kappa : ℝ := 2 * ((a : ℝ) / (b : ℝ))
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Eventually.of_forall fun n => Nat.le_add_right n 1) tendsto_id
  have hG : Tendsto g atTop (nhds 1) :=
    rationalCriticalFamilyEffectiveCoupling_tendsto_one a b hb
  have hGShift : Tendsto (fun n : ℕ => g (n + 1)) atTop (nhds 1) :=
    hG.comp hShift
  have hDShift : Tendsto (fun n : ℕ => g (n + 1) - 1)
      atTop (nhds 0) := by
    simpa using hGShift.sub (tendsto_const_nhds (x := (1 : ℝ)))
  have hScaled :=
    (rationalCriticalFamilyEffectiveCoupling_scaled_tendsto a b hb).comp
      hShift
  have hAdjusted := hScaled.sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hDShift)
  have hAdjusted' : Tendsto
      (fun n =>
        (((n + 1 : ℕ) : ℝ) + 1) * (g (n + 1) - 1) -
          2 * (g (n + 1) - 1))
      atTop (nhds kappa) := by
    simpa [g, kappa, Function.comp_def] using hAdjusted
  have hLinear : Tendsto
      (fun n : ℕ => (n : ℝ) * (g (n + 1) - 1))
      atTop (nhds kappa) := by
    apply hAdjusted'.congr'
    filter_upwards [] with n
    dsimp [g, kappa]
    push_cast
    ring
  have hLogRaw := Real.tendsto_nat_mul_log_one_add_of_tendsto hLinear
  have hLog : Tendsto
      (fun n : ℕ => (n : ℝ) * Real.log (g (n + 1)))
      atTop (nhds kappa) := by
    simpa [g] using hLogRaw
  exact criticalOneMissingBornToTimidRatio_tendsto_atTop g kappa
    (fun n => by
      dsimp [g, rationalCriticalFamilyEffectiveCoupling]
      change 0 < rationalCriticalFamilyPairCoupling a b n ^ 2
      exact pow_pos (lt_trans zero_lt_one
        (rationalCriticalFamilyPairCoupling_gt_one a b n ha hb)) 2)
    hLog

/-- The same positive-rational family diverges in the physical coherent
unlabeled channel. -/
theorem rationalCriticalFamily_coherentOneMissingBornRatio_tendsto_atTop
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (criticalCoherentOneMissingBornToTimidRatio
        (rationalCriticalFamilyEffectiveCoupling a b))
      atTop atTop := by
  have hSlot := rationalCriticalFamily_oneMissingBornRatio_tendsto_atTop a b ha hb
  refine tendsto_atTop_mono' atTop ?_ hSlot
  filter_upwards [] with n
  have hg : 0 < rationalCriticalFamilyEffectiveCoupling a b (n + 1) := by
    unfold rationalCriticalFamilyEffectiveCoupling
    exact pow_pos (lt_trans zero_lt_one
      (rationalCriticalFamilyPairCoupling_gt_one a b (n + 1) ha hb)) _
  have hden : 0 <
      (rationalCriticalFamilyEffectiveCoupling a b (n + 1)) ^ (2 * n) :=
    pow_pos hg _
  rw [criticalOneMissingBornToTimidRatio,
    criticalCoherentOneMissingBornToTimidRatio,
    div_le_div_iff_of_pos_right hden]
  have hOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith [sq_nonneg ((((n + 1 : ℕ) : ℝ)) - 1)]

/-- Capstone: finite-kappa rational critical running is compatible with exact
quantum dynamics but incompatible with aggregate timid/one-missing balance on
the antichain family. -/
theorem criticalMultiplicityCorrection_capstone
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (rationalCriticalFamilyEffectiveCoupling a b)
        atTop (nhds 1)
      ∧ Tendsto
          (fun n : ℕ => ((n : ℝ) + 1) *
            (rationalCriticalFamilyEffectiveCoupling a b n - 1))
          atTop (nhds (2 * ((a : ℝ) / (b : ℝ))))
      ∧ Tendsto
          (criticalOneMissingBornToTimidRatio
            (rationalCriticalFamilyEffectiveCoupling a b))
          atTop atTop
      ∧ Tendsto
          (criticalCoherentOneMissingBornToTimidRatio
            (rationalCriticalFamilyEffectiveCoupling a b))
          atTop atTop := by
  exact ⟨rationalCriticalFamilyEffectiveCoupling_tendsto_one a b hb,
    rationalCriticalFamilyEffectiveCoupling_scaled_tendsto a b hb,
    rationalCriticalFamily_oneMissingBornRatio_tendsto_atTop a b ha hb,
    rationalCriticalFamily_coherentOneMissingBornRatio_tendsto_atTop a b ha hb⟩

#print axioms antichainOneMissingBornToTimidRatio
#print axioms antichainCoherentOneMissingBornToTimidRatio
#print axioms antichainPrecursorSector_card
#print axioms criticalOneMissingBornToTimidRatio_tendsto_atTop
#print axioms criticalCoherentOneMissingBornToTimidRatio_tendsto_atTop
#print axioms rationalCriticalFamily_oneMissingBornRatio_tendsto_atTop
#print axioms rationalCriticalFamily_coherentOneMissingBornRatio_tendsto_atTop
#print axioms criticalMultiplicityCorrection_capstone

end

end UnifiedTheory.Audit.KFCausalSetCriticalMultiplicity

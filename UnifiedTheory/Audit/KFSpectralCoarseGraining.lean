/-
  Audit/KFSpectralCoarseGraining.lean

  K_F SPECTRAL OBSERVABLE + FINITE COARSE-GRAINING WITNESS

  This file connects the generic determinant-defined K_F operator to the
  order-separation audit and the infrared-flow interface.

  CLOSED HERE:

  1. `Tr(K_F^2)/n^2` is computed exactly on the four preregistered orders.
  2. That single normalized spectral moment separates all four orders.
  3. The moment is invariant under every relabeling of every finite poset.
  4. Two distinct finite layered causal samples admit exact order quotients
     to the same three-event chain.
  5. Their two-step coarse-graining flows are nonconstant and converge to
     the shared normalized spectral value 1.
  6. K_F at every chamber rank is generically invariant under order duality,
     proving that no spectral statistic of this symmetrized operator can
     recover causal-arrow orientation.
  7. The omitted forward-minus-backward determinant channel is skew, changes
     sign under duality, and restores each directed determinant exactly.

  HONEST SCOPE:

  The two samples are explicit finite layered causal orders, not draws from
  a formalized Poisson point process.  The two-step quotient is a minimal
  nonconstant recovery witness, not a renormalization-group construction or
  a continuum universality theorem.
-/

import UnifiedTheory.LayerB.KFFinitePoset
import UnifiedTheory.Audit.OrderSensitiveObservables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFSpectralCoarseGraining

open Filter Topology
open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.LayerB.KFFinitePoset
open UnifiedTheory.Audit.QuantumGeometryStatus
open UnifiedTheory.Audit.OrderSensitiveObservables

/-! ## 1. K_F-augmented order signature -/

/-- The order-derived signature augmented by an exact normalized K_F
spectral moment. -/
structure SpectralOrderSignature where
  orderData : OrderSignature
  normalizedKF2 : ℚ
  deriving DecidableEq, Repr

def spectralOrderSignature (P : FinPoset) : SpectralOrderSignature where
  orderData := orderSignature P
  normalizedKF2 := normalizedKFSecondMoment P

@[simp]
theorem antichainFour_rel_apply (i j : Fin 4) :
    antichainFour.rel i j = decide (i = j) := rfl

@[simp]
theorem twoChainsFour_rel_apply (i j : Fin 4) :
    twoChainsFour.rel i j =
      decide (i = j ∨ (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3)) := rfl

@[simp]
theorem diamondFour_rel_apply (i j : Fin 4) :
    diamondFour.rel i j = decide (
      i = j
        ∨ (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3))
        ∨ ((i = 1 ∨ i = 2) ∧ j = 3)) := rfl

@[simp]
theorem chainFour_rel_apply (i j : Fin 4) :
    chainFour.rel i j = decide (i.val ≤ j.val) := rfl

theorem antichainFour_normalizedKF2 :
    normalizedKFSecondMoment antichainFour = 1 / 4 := by
  change ((∑ i : Fin 4, ∑ j : Fin 4,
    kFSizeOne antichainFour i j * kFSizeOne antichainFour j i) / 16) = 1 / 4
  simp_rw [Finset.sum_fin_eq_sum_range]
  simp only [kFSizeOne, orderKernel, antichainFour_rel_apply]
  norm_num [Finset.sum_range_succ, Fin.ext_iff]

theorem twoChainsFour_normalizedKF2 :
    normalizedKFSecondMoment twoChainsFour = 1 / 2 := by
  change ((∑ i : Fin 4, ∑ j : Fin 4,
    kFSizeOne twoChainsFour i j * kFSizeOne twoChainsFour j i) / 16) = 1 / 2
  simp_rw [Finset.sum_fin_eq_sum_range]
  simp only [kFSizeOne, orderKernel, twoChainsFour_rel_apply]
  norm_num [Finset.sum_range_succ, Fin.ext_iff]

theorem diamondFour_normalizedKF2 :
    normalizedKFSecondMoment diamondFour = 7 / 8 := by
  change ((∑ i : Fin 4, ∑ j : Fin 4,
    kFSizeOne diamondFour i j * kFSizeOne diamondFour j i) / 16) = 7 / 8
  simp_rw [Finset.sum_fin_eq_sum_range]
  simp only [kFSizeOne, orderKernel, diamondFour_rel_apply]
  norm_num [Finset.sum_range_succ, Fin.ext_iff]

theorem chainFour_normalizedKF2 :
    normalizedKFSecondMoment chainFour = 1 := by
  change ((∑ i : Fin 4, ∑ j : Fin 4,
    kFSizeOne chainFour i j * kFSizeOne chainFour j i) / 16) = 1
  simp_rw [Finset.sum_fin_eq_sum_range]
  simp only [kFSizeOne, orderKernel, chainFour_rel_apply]
  norm_num [Finset.sum_range_succ, Fin.ext_iff]

/-- The normalized K_F second moment alone separates the four benchmark
orders; the non-spectral fields are not needed for this finite gate. -/
def NormalizedKF2SeparatesBenchmarks : Prop :=
    normalizedKFSecondMoment antichainFour ≠ normalizedKFSecondMoment twoChainsFour
    ∧ normalizedKFSecondMoment antichainFour ≠ normalizedKFSecondMoment diamondFour
    ∧ normalizedKFSecondMoment antichainFour ≠ normalizedKFSecondMoment chainFour
    ∧ normalizedKFSecondMoment twoChainsFour ≠ normalizedKFSecondMoment diamondFour
    ∧ normalizedKFSecondMoment twoChainsFour ≠ normalizedKFSecondMoment chainFour
    ∧ normalizedKFSecondMoment diamondFour ≠ normalizedKFSecondMoment chainFour

theorem normalizedKF2_separates_benchmarks :
    NormalizedKF2SeparatesBenchmarks := by
  unfold NormalizedKF2SeparatesBenchmarks
  rw [antichainFour_normalizedKF2, twoChainsFour_normalizedKF2,
    diamondFour_normalizedKF2, chainFour_normalizedKF2]
  norm_num

/-! ## 2. Generic relabeling invariance -/

@[simp]
theorem kFSizeOne_relabel_apply (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) (i j : Fin P.n) :
    kFSizeOne (relabel P σ) (σ i) (σ j) = kFSizeOne P i j := by
  simp [kFSizeOne, orderKernel, relabel]

theorem kFSecondMoment_relabel (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) :
    kFSecondMoment (relabel P σ) = kFSecondMoment P := by
  let f : Fin P.n → Fin P.n → ℚ := fun i j =>
    kFSizeOne (relabel P σ) i j * kFSizeOne (relabel P σ) j i
  have hReindex :
      (∑ i, ∑ j, f (σ i) (σ j)) = ∑ i, ∑ j, f i j := by
    calc
      (∑ i, ∑ j, f (σ i) (σ j)) = ∑ i, ∑ j, f (σ i) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => f (σ i) j)
      _ = ∑ i, ∑ j, f i j :=
        Equiv.sum_comp σ (fun i => ∑ j, f i j)
  simp only [kFSecondMoment, Matrix.trace]
  change (∑ i, ∑ j,
      kFSizeOne (relabel P σ) i j * kFSizeOne (relabel P σ) j i) =
    ∑ i, ∑ j, kFSizeOne P i j * kFSizeOne P j i
  calc
    _ = ∑ i, ∑ j,
        kFSizeOne (relabel P σ) (σ i) (σ j) *
          kFSizeOne (relabel P σ) (σ j) (σ i) := hReindex.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [kFSizeOne_relabel_apply, kFSizeOne_relabel_apply]

theorem normalizedKFSecondMoment_relabel (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) :
    normalizedKFSecondMoment (relabel P σ) = normalizedKFSecondMoment P := by
  unfold normalizedKFSecondMoment
  rw [kFSecondMoment_relabel P σ]
  rfl

theorem spectralOrderSignature_relabel (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) :
    spectralOrderSignature (relabel P σ) = spectralOrderSignature P := by
  simp only [spectralOrderSignature]
  rw [orderSignature_relabel P σ, normalizedKFSecondMoment_relabel P σ]

/-! ### An exact limitation of the full all-rank operator -/

/-- Reverse every causal arrow of a finite poset. -/
def orderDual (P : FinPoset) : FinPoset where
  n := P.n
  hn := P.hn
  rel := fun i j => P.rel j i
  refl := P.refl
  antisymm := by
    intro i j hij hji
    exact P.antisymm i j hji hij
  trans := by
    intro i j k hij hjk
    exact P.trans k j i hjk hij

/-- Under order duality, each zeta block is the transpose of the block with
its two chambers exchanged. -/
theorem zetaBlock_orderDual (P : FinPoset) {r : ℕ} (A B : Chamber P r) :
    zetaBlock (orderDual P) A B = (zetaBlock P B A).transpose := by
  rfl

/-- The symmetrized determinant formula is exactly invariant under reversing
every causal arrow, at every chamber rank. -/
theorem kFAtRank_orderDual (P : FinPoset) (r : ℕ) :
    kFAtRank (orderDual P) r = kFAtRank P r := by
  ext A B
  simp only [kFAtRank]
  rw [zetaBlock_orderDual, zetaBlock_orderDual,
    Matrix.det_transpose, Matrix.det_transpose]
  ring

/-- The complementary forward-minus-backward channel behaves exactly as an
orientation observable should: order duality negates it at every rank. -/
theorem kFOrientationAtRank_orderDual (P : FinPoset) (r : ℕ) :
    kFOrientationAtRank (orderDual P) r = -kFOrientationAtRank P r := by
  ext A B
  simp only [kFOrientationAtRank]
  rw [zetaBlock_orderDual, zetaBlock_orderDual,
    Matrix.det_transpose, Matrix.det_transpose]
  change (zetaBlock P B A).det - (zetaBlock P A B).det =
    -((zetaBlock P A B).det - (zetaBlock P B A).det)
  ring

/-- Consequently every normalized second spectral moment of this operator is
dual-invariant, including all higher chamber ranks. -/
theorem normalizedKFSecondMomentAtRank_orderDual (P : FinPoset) (r : ℕ) :
    normalizedKFSecondMomentAtRank (orderDual P) r =
      normalizedKFSecondMomentAtRank P r := by
  unfold normalizedKFSecondMomentAtRank kFSecondMomentAtRank
    chamberNormalization chamberCount
  rw [kFAtRank_orderDual]
  rfl

/-- The rank-one specialization sees only the undirected comparability graph. -/
theorem kFSizeOne_orderDual (P : FinPoset) :
    kFSizeOne (orderDual P) = kFSizeOne P := by
  ext i j
  simp [kFSizeOne, orderKernel, orderDual, add_comm]

/-- Consequently the normalized rank-one spectral moment is generically blind
to causal orientation, not merely degenerate on one chosen example. -/
theorem normalizedKFSecondMoment_orderDual (P : FinPoset) :
    normalizedKFSecondMoment (orderDual P) =
      normalizedKFSecondMoment P := by
  unfold normalizedKFSecondMoment kFSecondMoment
  rw [kFSizeOne_orderDual]
  rfl

/-- Reverse every causal arrow in the diamond. -/
def dualDiamondFour : FinPoset := orderDual diamondFour

/-- The diamond and its dual disagree on an oriented causal question. -/
theorem diamond_dual_orientation_differs :
    diamondFour.rel (0 : Fin 4) (1 : Fin 4) ≠
      dualDiamondFour.rel (0 : Fin 4) (1 : Fin 4) := by
  decide

/-- The generic duality no-go specializes to the diamond.  Higher chamber
rank does not repair it; an operator that breaks the forward/backward
symmetrization or other explicitly oriented data is required. -/
theorem kFSizeOne_dualDiamond_eq :
    kFSizeOne dualDiamondFour = kFSizeOne diamondFour := by
  exact kFSizeOne_orderDual diamondFour

theorem normalizedKF2_dualDiamond_eq :
    normalizedKFSecondMoment dualDiamondFour =
      normalizedKFSecondMoment diamondFour := by
  exact normalizedKFSecondMoment_orderDual diamondFour

/-- The exact no-go package: the full operator is dual-invariant at every rank
even though dualization can reverse an observable causal arrow. -/
theorem allRanks_orientation_no_go :
    (∀ (P : FinPoset) (r : ℕ),
      kFAtRank (orderDual P) r = kFAtRank P r)
    ∧ diamondFour.rel (0 : Fin 4) (1 : Fin 4) ≠
      dualDiamondFour.rel (0 : Fin 4) (1 : Fin 4) :=
  ⟨kFAtRank_orderDual, diamond_dual_orientation_differs⟩

/-- The obstruction and its minimal algebraic repair: the symmetric channel
is dual-blind, while the omitted skew channel changes sign and, together with
`K_F`, reconstructs every directed determinant block. -/
theorem allRanks_orientation_loss_and_repair :
    (∀ (P : FinPoset) (r : ℕ),
      kFAtRank (orderDual P) r = kFAtRank P r)
    ∧ (∀ (P : FinPoset) (r : ℕ),
      kFOrientationAtRank (orderDual P) r = -kFOrientationAtRank P r)
    ∧ (∀ (P : FinPoset) (r : ℕ) (A B : Chamber P r),
      (zetaBlock P A B).det =
        (kFAtRank P r A B + (if A = B then 1 else 0) +
          kFOrientationAtRank P r A B) / 2) :=
  ⟨kFAtRank_orderDual, kFOrientationAtRank_orderDual,
    forwardDet_from_symmetric_and_orientation⟩

/-! ## 3. Explicit finite causal samples and quotient certificates -/

/-- Three totally ordered coarse events. -/
def chainThree : FinPoset where
  n := 3
  hn := by decide
  rel := fun i j => decide (i.val ≤ j.val)
  refl := by decide
  antisymm := by decide
  trans := by decide

/-- A five-event, three-layer causal sample with layer occupancies `(2,2,1)`.
Events in the same layer are incomparable; every earlier-layer event
precedes every later-layer event. -/
def layeredFive : FinPoset where
  n := 5
  hn := by decide
  rel := fun i j => decide (
    i = j
      ∨ ((i = 0 ∨ i = 1) ∧ (j = 2 ∨ j = 3 ∨ j = 4))
      ∨ ((i = 2 ∨ i = 3) ∧ j = 4))
  refl := by decide
  antisymm := by decide
  trans := by decide

@[simp]
theorem chainThree_rel_apply (i j : Fin 3) :
    chainThree.rel i j = decide (i.val ≤ j.val) := rfl

@[simp]
theorem layeredFive_rel_apply (i j : Fin 5) :
    layeredFive.rel i j = decide (
      i = j
        ∨ ((i = 0 ∨ i = 1) ∧ (j = 2 ∨ j = 3 ∨ j = 4))
        ∨ ((i = 2 ∨ i = 3) ∧ j = 4)) := rfl

/-- An exact order quotient: coarse events are nonempty blocks of fine
events, and the coarse relation is precisely the existential image of the
fine relation. -/
structure OrderCoarseGraining where
  fine : FinPoset
  coarse : FinPoset
  block : Fin fine.n → Fin coarse.n
  block_surjective : Function.Surjective block
  relation_iff : ∀ a b,
    coarse.rel a b = true ↔
      ∃ i j, block i = a ∧ block j = b ∧ fine.rel i j = true

def diamondBlock : Fin 4 → Fin 3 := ![0, 1, 1, 2]

def layeredFiveBlock : Fin 5 → Fin 3 := ![0, 0, 1, 1, 2]

/-- The diamond becomes a three-chain when its two middle events are
identified as one coarse event. -/
def diamondToChainThree : OrderCoarseGraining where
  fine := diamondFour
  coarse := chainThree
  block := diamondBlock
  block_surjective := by decide
  relation_iff := by decide

/-- The `(2,2,1)` layered sample becomes the same three-chain when events
within each layer are identified. -/
def layeredFiveToChainThree : OrderCoarseGraining where
  fine := layeredFive
  coarse := chainThree
  block := layeredFiveBlock
  block_surjective := by decide
  relation_iff := by decide

theorem chainThree_normalizedKF2 :
    normalizedKFSecondMoment chainThree = 1 := by
  change ((∑ i : Fin 3, ∑ j : Fin 3,
    kFSizeOne chainThree i j * kFSizeOne chainThree j i) / 9) = 1
  simp_rw [Finset.sum_fin_eq_sum_range]
  simp only [kFSizeOne, orderKernel, chainThree_rel_apply]
  norm_num [Finset.sum_range_succ, Fin.ext_iff]

theorem layeredFive_normalizedKF2 :
    normalizedKFSecondMoment layeredFive = 21 / 25 := by
  change ((∑ i : Fin 5, ∑ j : Fin 5,
    kFSizeOne layeredFive i j * kFSizeOne layeredFive j i) / 25) = 21 / 25
  simp_rw [Finset.sum_fin_eq_sum_range]
  simp only [kFSizeOne, orderKernel, layeredFive_rel_apply]
  norm_num [Finset.sum_range_succ, Fin.ext_iff]

theorem microscopic_samples_spectrally_distinct :
    normalizedKFSecondMoment diamondFour ≠
      normalizedKFSecondMoment layeredFive := by
  rw [diamondFour_normalizedKF2, layeredFive_normalizedKF2]
  norm_num

/-! ## 4. Nonconstant flows to a shared finite quotient -/

/-- Minimal scale flow induced by one certified quotient: keep the fine
order at scale zero and use its coarse quotient at every positive scale. -/
def quotientFlow (step : OrderCoarseGraining) : IRObservableFlow FinPoset where
  stateAtScale := fun scale => if scale = 0 then step.fine else step.coarse
  observable := fun P => (normalizedKFSecondMoment P : ℝ)
  targetValue := (normalizedKFSecondMoment step.coarse : ℝ)

theorem quotientFlow_converges (step : OrderCoarseGraining) :
    (quotientFlow step).ConvergesInIR := by
  unfold IRObservableFlow.ConvergesInIR
  apply tendsto_const_nhds.congr'
  refine Filter.eventually_atTop.2 ⟨1, ?_⟩
  intro scale hscale
  have hne : scale ≠ 0 := by omega
  simp [quotientFlow, hne]

theorem diamond_quotient_flow_nontrivial :
    (quotientFlow diamondToChainThree).HasNontrivialScaleDependence := by
  refine ⟨0, 1, ?_⟩
  norm_num [quotientFlow, diamondToChainThree,
    diamondFour_normalizedKF2, chainThree_normalizedKF2]

theorem layeredFive_quotient_flow_nontrivial :
    (quotientFlow layeredFiveToChainThree).HasNontrivialScaleDependence := by
  refine ⟨0, 1, ?_⟩
  norm_num [quotientFlow, layeredFiveToChainThree,
    layeredFive_normalizedKF2, chainThree_normalizedKF2]

theorem two_sample_shared_finite_recovery :
    (quotientFlow diamondToChainThree).IsNontrivialRecoveryWitness
    ∧ (quotientFlow layeredFiveToChainThree).IsNontrivialRecoveryWitness
    ∧ (quotientFlow diamondToChainThree).targetValue = 1
    ∧ (quotientFlow layeredFiveToChainThree).targetValue = 1
    ∧ normalizedKFSecondMoment diamondFour ≠
      normalizedKFSecondMoment layeredFive := by
  refine ⟨⟨quotientFlow_converges _, diamond_quotient_flow_nontrivial⟩,
    ⟨quotientFlow_converges _, layeredFive_quotient_flow_nontrivial⟩, ?_, ?_,
    microscopic_samples_spectrally_distinct⟩
  · norm_num [quotientFlow, diamondToChainThree, chainThree_normalizedKF2]
  · norm_num [quotientFlow, layeredFiveToChainThree, chainThree_normalizedKF2]

/-! ## 5. Master theorem and trust regression -/

theorem kf_spectral_coarse_graining_benchmark_v1 :
    NormalizedKF2SeparatesBenchmarks
    ∧ (∀ (P : FinPoset) (σ : Equiv.Perm (Fin P.n)),
      spectralOrderSignature (relabel P σ) = spectralOrderSignature P)
    ∧ (∀ (P : FinPoset) (r : ℕ),
      kFAtRank (orderDual P) r = kFAtRank P r)
    ∧ diamondFour.rel (0 : Fin 4) (1 : Fin 4) ≠
      dualDiamondFour.rel (0 : Fin 4) (1 : Fin 4)
    ∧ (quotientFlow diamondToChainThree).IsNontrivialRecoveryWitness
    ∧ (quotientFlow layeredFiveToChainThree).IsNontrivialRecoveryWitness
    ∧ (quotientFlow diamondToChainThree).targetValue =
      (quotientFlow layeredFiveToChainThree).targetValue
    ∧ normalizedKFSecondMoment diamondFour ≠
      normalizedKFSecondMoment layeredFive := by
  refine ⟨normalizedKF2_separates_benchmarks, spectralOrderSignature_relabel,
    kFAtRank_orderDual, diamond_dual_orientation_differs,
    two_sample_shared_finite_recovery.1,
    two_sample_shared_finite_recovery.2.1, ?_,
    two_sample_shared_finite_recovery.2.2.2.2⟩
  rw [two_sample_shared_finite_recovery.2.2.1,
    two_sample_shared_finite_recovery.2.2.2.1]

#print axioms normalizedKF2_separates_benchmarks
#print axioms spectralOrderSignature_relabel
#print axioms allRanks_orientation_no_go
#print axioms allRanks_orientation_loss_and_repair
#print axioms two_sample_shared_finite_recovery
#print axioms kf_spectral_coarse_graining_benchmark_v1

end UnifiedTheory.Audit.KFSpectralCoarseGraining

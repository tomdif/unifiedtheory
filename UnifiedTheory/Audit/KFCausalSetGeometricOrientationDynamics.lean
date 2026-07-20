/-
  Audit/KFCausalSetGeometricOrientationDynamics.lean

  ALL-RANK GEOMETRIC ORIENTATION AND THE QUARTER-TURN LIFT

  The number-volume action leaves a trace-free geometric residual.  At rank
  two that residual was reflection odd.  This file constructs the canonical
  extension to every finite causal order.

  Inclusive past and future volume have the same total weight.  Their average
  is an unoriented shape channel and half their difference is an orientation
  channel.  The latter is relabeling covariant, trace-free at every rank, and
  changes sign under reversal of the causal order.  Thus the volume, shape,
  and orientation sectors are separated before complex quantum amplitudes are
  introduced.

  The existing balanced-birth theorem then supplies the quantum lift: a unit
  relative amplitude with balanced complementary Born weights is necessarily
  `+i` or `-i`.  Multiplying the real geometric orientation channel by that
  dynamically forced quarter turn gives the two chiral amplitudes.  Order
  duality and microscopic chirality reflection exchange the two signs, while
  their combined action is invariant.

  Two honest boundaries are proved rather than hidden.  First, a
  reflection-symmetric law cannot choose one member of the chiral pair; an
  absolute sign still requires a reflection-odd boundary/source datum.
  Second, the rank-two geometric parameter is a strict interior point of the
  positivity interval.  Its balanced decoherence kernel therefore genuinely
  requires latent rank two and cannot be produced by scalar path amplitudes.
  Geometry naturally supplies mixed higher-rank data as well as pure chiral
  boundary sectors.
-/

import UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
import UnifiedTheory.Audit.KFCausalSetChiralGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

/-! ## 1. Order duality on fixed-cardinality causal orders -/

/-- Reverse every causal arrow while preserving the event set. -/
def cardinalCausalOrderDual {n : ℕ}
    (parent : CardinalCausalOrder n) : CardinalCausalOrder n where
  rel := fun i j => parent.rel j i
  refl := parent.refl
  antisymm := by
    intro i j hij hji
    exact parent.antisymm i j hji hij
  trans := by
    intro i j k hij hjk
    exact parent.trans k j i hjk hij

@[simp]
theorem cardinalCausalOrderDual_rel {n : ℕ}
    (parent : CardinalCausalOrder n) (i j : Fin n) :
    (cardinalCausalOrderDual parent).rel i j = parent.rel j i :=
  rfl

@[simp]
theorem cardinalCausalOrderDual_dual {n : ℕ}
    (parent : CardinalCausalOrder n) :
    cardinalCausalOrderDual (cardinalCausalOrderDual parent) = parent := by
  apply CardinalCausalOrder.ext
  rfl

/-- Order duality is intrinsic on unlabeled causets: an isomorphism remains an
isomorphism after every arrow is reversed. -/
theorem cardinalCausalOrderDual_isomorphic {n : ℕ}
    {parent parent' : CardinalCausalOrder n}
    (hIso : CardinalCausalOrderIsomorphic parent parent') :
    CardinalCausalOrderIsomorphic
      (cardinalCausalOrderDual parent)
      (cardinalCausalOrderDual parent') := by
  obtain ⟨relabeling, hRel⟩ := hIso
  exact ⟨relabeling, fun i j => hRel j i⟩

/-- Order reversal descended to the quotient of genuine order isomorphisms. -/
def unlabeledCardinalCausalOrderDual {n : ℕ} :
    UnlabeledCardinalCausalOrder n → UnlabeledCardinalCausalOrder n :=
  Quotient.map cardinalCausalOrderDual
    (fun _ _ hIso => cardinalCausalOrderDual_isomorphic hIso)

@[simp]
theorem unlabeledCardinalCausalOrderDual_mk {n : ℕ}
    (parent : CardinalCausalOrder n) :
    unlabeledCardinalCausalOrderDual (Quotient.mk _ parent) =
      Quotient.mk _ (cardinalCausalOrderDual parent) :=
  rfl

@[simp]
theorem unlabeledCardinalCausalOrderDual_dual {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    unlabeledCardinalCausalOrderDual
        (unlabeledCardinalCausalOrderDual parent) = parent := by
  induction parent using Quotient.inductionOn with
  | _ representative =>
      simp

/-! ## 2. Inclusive future volume and exact past/future balance -/

/-- Order-sensitive local future volume: the number of events in the
inclusive causal future of an event. -/
def causalFutureVolumeQ {n : ℕ} (parent : CardinalCausalOrder n)
    (i : Fin n) : ℚ :=
  ∑ j : Fin n, if parent.rel i j = true then 1 else 0

theorem causalFutureVolumeQ_eq_dualPast {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalFutureVolumeQ parent i =
      causalPastVolumeQ (cardinalCausalOrderDual parent) i :=
  rfl

theorem causalPastVolumeQ_dual {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalPastVolumeQ (cardinalCausalOrderDual parent) i =
      causalFutureVolumeQ parent i :=
  rfl

theorem causalFutureVolumeQ_dual {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalFutureVolumeQ (cardinalCausalOrderDual parent) i =
      causalPastVolumeQ parent i :=
  rfl

theorem causalFutureVolumeQ_relabel {n : ℕ}
    (parent parent' : CardinalCausalOrder n)
    (relabeling : Equiv.Perm (Fin n))
    (hRel : ∀ i j,
      parent.rel i j = parent'.rel (relabeling i) (relabeling j))
    (i : Fin n) :
    causalFutureVolumeQ parent' (relabeling i) =
      causalFutureVolumeQ parent i := by
  unfold causalFutureVolumeQ
  rw [← Equiv.sum_comp relabeling
    (fun j => if parent'.rel (relabeling i) j = true then (1 : ℚ) else 0)]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← hRel i j]

/-- Counting the same causal incidences by their first or second endpoint
gives identical total past and future volume. -/
theorem totalCausalFutureVolumeQ_eq_totalCausalPastVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) :
    (∑ i : Fin n, causalFutureVolumeQ parent i) =
      totalCausalPastVolumeQ parent := by
  unfold causalFutureVolumeQ totalCausalPastVolumeQ causalPastVolumeQ
  rw [Finset.sum_comm]

theorem totalCausalPastVolumeQ_dual {n : ℕ}
    (parent : CardinalCausalOrder n) :
    totalCausalPastVolumeQ (cardinalCausalOrderDual parent) =
      totalCausalPastVolumeQ parent := by
  unfold totalCausalPastVolumeQ
  simp_rw [causalPastVolumeQ_dual]
  exact totalCausalFutureVolumeQ_eq_totalCausalPastVolumeQ parent

/-- Normalize future volume by the same total causal-incidence count used by
the past profile. -/
def normalizedCausalFutureVolumeDensityQ {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) : ℚ :=
  causalFutureVolumeQ parent i / totalCausalPastVolumeQ parent

theorem normalizedCausalFutureVolumeDensityQ_covariant :
    IsCausalOrderRelabelingCovariant
      (@normalizedCausalFutureVolumeDensityQ) := by
  intro n parent parent' relabeling hRel i
  unfold normalizedCausalFutureVolumeDensityQ
  rw [causalFutureVolumeQ_relabel parent parent' relabeling hRel,
    totalCausalPastVolumeQ_relabel parent parent' relabeling hRel]

theorem normalizedCausalFutureVolumeDensityQ_sum_one {n : ℕ}
    (parent : CardinalCausalOrder n)
    (hTotal : totalCausalPastVolumeQ parent ≠ 0) :
    ∑ i, normalizedCausalFutureVolumeDensityQ parent i = 1 := by
  unfold normalizedCausalFutureVolumeDensityQ
  rw [← Finset.sum_div,
    totalCausalFutureVolumeQ_eq_totalCausalPastVolumeQ]
  exact div_self hTotal

theorem normalizedCausalPastVolumeDensityQ_dual {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    normalizedCausalPastVolumeDensityQ
        (cardinalCausalOrderDual parent) i =
      normalizedCausalFutureVolumeDensityQ parent i := by
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  rw [causalPastVolumeQ_dual, totalCausalPastVolumeQ_dual]

theorem normalizedCausalFutureVolumeDensityQ_dual {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    normalizedCausalFutureVolumeDensityQ
        (cardinalCausalOrderDual parent) i =
      normalizedCausalPastVolumeDensityQ parent i := by
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  rw [causalFutureVolumeQ_dual, totalCausalPastVolumeQ_dual]

/-! ## 3. Canonical all-rank shape/orientation splitting -/

/-- The order-dual-even part of normalized causal volume. -/
def causalVolumeShapeDensityQ {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) : ℚ :=
  (normalizedCausalPastVolumeDensityQ parent i +
    normalizedCausalFutureVolumeDensityQ parent i) / 2

/-- The order-dual-odd part of normalized causal volume. -/
def causalOrientationDensityQ {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) : ℚ :=
  (normalizedCausalPastVolumeDensityQ parent i -
    normalizedCausalFutureVolumeDensityQ parent i) / 2

/-- Past volume decomposes exactly into unoriented shape plus orientation. -/
theorem normalizedPast_eq_shape_add_orientation {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    normalizedCausalPastVolumeDensityQ parent i =
      causalVolumeShapeDensityQ parent i +
        causalOrientationDensityQ parent i := by
  unfold causalVolumeShapeDensityQ causalOrientationDensityQ
  ring

/-- Future volume has the same shape and the opposite orientation. -/
theorem normalizedFuture_eq_shape_sub_orientation {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    normalizedCausalFutureVolumeDensityQ parent i =
      causalVolumeShapeDensityQ parent i -
        causalOrientationDensityQ parent i := by
  unfold causalVolumeShapeDensityQ causalOrientationDensityQ
  ring

/-- The split is canonical for this geometric profile.  This is uniqueness of
the dual-even/dual-odd components of the chosen past/future pair; it does not
claim that the full higher-rank space of all odd observables is
one-dimensional. -/
theorem causalVolumeShapeOrientation_split_unique {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n)
    (shape orientation : ℚ)
    (hPast : normalizedCausalPastVolumeDensityQ parent i =
      shape + orientation)
    (hFuture : normalizedCausalFutureVolumeDensityQ parent i =
      shape - orientation) :
    shape = causalVolumeShapeDensityQ parent i ∧
      orientation = causalOrientationDensityQ parent i := by
  unfold causalVolumeShapeDensityQ causalOrientationDensityQ
  constructor <;> linarith

theorem causalVolumeShapeDensityQ_covariant :
    IsCausalOrderRelabelingCovariant (@causalVolumeShapeDensityQ) := by
  intro n parent parent' relabeling hRel i
  unfold causalVolumeShapeDensityQ
  rw [normalizedCausalPastVolumeDensityQ_covariant
      parent parent' relabeling hRel i,
    normalizedCausalFutureVolumeDensityQ_covariant
      parent parent' relabeling hRel i]

theorem causalOrientationDensityQ_covariant :
    IsCausalOrderRelabelingCovariant (@causalOrientationDensityQ) := by
  intro n parent parent' relabeling hRel i
  unfold causalOrientationDensityQ
  rw [normalizedCausalPastVolumeDensityQ_covariant
      parent parent' relabeling hRel i,
    normalizedCausalFutureVolumeDensityQ_covariant
      parent parent' relabeling hRel i]

/-- The shape channel forgets the arrow of time. -/
theorem causalVolumeShapeDensityQ_dual_even {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalVolumeShapeDensityQ (cardinalCausalOrderDual parent) i =
      causalVolumeShapeDensityQ parent i := by
  unfold causalVolumeShapeDensityQ
  rw [normalizedCausalPastVolumeDensityQ_dual,
    normalizedCausalFutureVolumeDensityQ_dual]
  ring

/-- The orientation channel reverses with every causal arrow. -/
theorem causalOrientationDensityQ_dual_odd {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalOrientationDensityQ (cardinalCausalOrderDual parent) i =
      -causalOrientationDensityQ parent i := by
  unfold causalOrientationDensityQ
  rw [normalizedCausalPastVolumeDensityQ_dual,
    normalizedCausalFutureVolumeDensityQ_dual]
  ring

/-- Orientation redistributes causal volume but carries no scalar volume. -/
theorem causalOrientationDensityQ_sum_zero {n : ℕ}
    (parent : CardinalCausalOrder n) :
    ∑ i, causalOrientationDensityQ parent i = 0 := by
  unfold causalOrientationDensityQ
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  unfold normalizedCausalPastVolumeDensityQ
  unfold normalizedCausalFutureVolumeDensityQ
  rw [← Finset.sum_div, ← Finset.sum_div,
    totalCausalFutureVolumeQ_eq_totalCausalPastVolumeQ]
  change ((totalCausalPastVolumeQ parent /
        totalCausalPastVolumeQ parent -
      totalCausalPastVolumeQ parent /
        totalCausalPastVolumeQ parent) / 2) = 0
  ring

/-- Inclusive past volume is strictly positive at every event because the
causal order is reflexive. -/
theorem causalPastVolumeQ_pos {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    0 < causalPastVolumeQ parent i := by
  unfold causalPastVolumeQ
  have hNonnegative : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (if parent.rel j i = true then (1 : ℚ) else 0) := by
    intro j _hj
    split <;> norm_num
  have hTermLe := Finset.single_le_sum hNonnegative (Finset.mem_univ i)
  simp only [parent.refl i, if_true] at hTermLe
  exact lt_of_lt_of_le (by norm_num) hTermLe

/-- Inclusive future volume is strictly positive for the same reason. -/
theorem causalFutureVolumeQ_pos {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    0 < causalFutureVolumeQ parent i := by
  rw [causalFutureVolumeQ_eq_dualPast]
  exact causalPastVolumeQ_pos (cardinalCausalOrderDual parent) i

theorem causalPastVolumeQ_le_total {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalPastVolumeQ parent i ≤ totalCausalPastVolumeQ parent := by
  unfold totalCausalPastVolumeQ
  exact Finset.single_le_sum
    (fun j _hj => le_of_lt (causalPastVolumeQ_pos parent j))
    (Finset.mem_univ i)

theorem causalFutureVolumeQ_le_total {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    causalFutureVolumeQ parent i ≤ totalCausalPastVolumeQ parent := by
  rw [← totalCausalFutureVolumeQ_eq_totalCausalPastVolumeQ]
  exact Finset.single_le_sum
    (fun j _hj => le_of_lt (causalFutureVolumeQ_pos parent j))
    (Finset.mem_univ i)

theorem totalCausalPastVolumeQ_pos {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    0 < totalCausalPastVolumeQ parent :=
  (causalPastVolumeQ_pos parent i).trans_le
    (causalPastVolumeQ_le_total parent i)

theorem normalizedCausalPastVolumeDensityQ_pos_le_one {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    0 < normalizedCausalPastVolumeDensityQ parent i ∧
      normalizedCausalPastVolumeDensityQ parent i ≤ 1 := by
  have hTotal := totalCausalPastVolumeQ_pos parent i
  unfold normalizedCausalPastVolumeDensityQ
  exact ⟨div_pos (causalPastVolumeQ_pos parent i) hTotal,
    (div_le_one hTotal).2 (causalPastVolumeQ_le_total parent i)⟩

theorem normalizedCausalFutureVolumeDensityQ_pos_le_one {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    0 < normalizedCausalFutureVolumeDensityQ parent i ∧
      normalizedCausalFutureVolumeDensityQ parent i ≤ 1 := by
  have hTotal := totalCausalPastVolumeQ_pos parent i
  unfold normalizedCausalFutureVolumeDensityQ
  exact ⟨div_pos (causalFutureVolumeQ_pos parent i) hTotal,
    (div_le_one hTotal).2 (causalFutureVolumeQ_le_total parent i)⟩

/-- At every event of every nonempty finite causet, the geometric orientation
parameter is strictly interior to the strong-positivity interval.  Inclusive
reflexivity prevents either normalized past or future weight from vanishing,
so pure endpoints cannot arise from this scalar volume profile alone. -/
theorem causalOrientationDensityQ_strictInterior {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    |causalOrientationDensityQ parent i| < (1 : ℚ) / 2 := by
  have hPast := normalizedCausalPastVolumeDensityQ_pos_le_one parent i
  have hFuture := normalizedCausalFutureVolumeDensityQ_pos_le_one parent i
  rw [abs_lt]
  unfold causalOrientationDensityQ
  constructor <;> linarith

theorem causalOrientationDensityR_strictInterior {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    |((causalOrientationDensityQ parent i : ℚ) : ℝ)| < 1 / 2 := by
  have hPastQ := normalizedCausalPastVolumeDensityQ_pos_le_one parent i
  have hFutureQ := normalizedCausalFutureVolumeDensityQ_pos_le_one parent i
  have hPastPos : (0 : ℝ) <
      (normalizedCausalPastVolumeDensityQ parent i : ℝ) := by
    exact_mod_cast hPastQ.1
  have hPastLe :
      (normalizedCausalPastVolumeDensityQ parent i : ℝ) ≤ 1 := by
    exact_mod_cast hPastQ.2
  have hFuturePos : (0 : ℝ) <
      (normalizedCausalFutureVolumeDensityQ parent i : ℝ) := by
    exact_mod_cast hFutureQ.1
  have hFutureLe :
      (normalizedCausalFutureVolumeDensityQ parent i : ℝ) ≤ 1 := by
    exact_mod_cast hFutureQ.2
  rw [abs_lt]
  constructor <;>
    norm_num [causalOrientationDensityQ] <;>
    linarith

/-- Consequently every local geometric orientation parameter defines a
strongly positive two-component kernel and no scalar-amplitude kernel.  Mixed
higher-rank decoherence is generic for this inclusive volume channel. -/
theorem geometry_requires_higher_rank_decoherence {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    IsTwoComponentAmplitudeKernel
        (balancedHistoryKernel
          ((causalOrientationDensityQ parent i : ℚ) : ℝ))
      ∧ ¬ IsScalarAmplitudeKernel
        (balancedHistoryKernel
          ((causalOrientationDensityQ parent i : ℚ) : ℝ)) := by
  have hInterior := causalOrientationDensityR_strictInterior parent i
  exact ⟨balancedHistoryKernel_isTwoComponent (le_of_lt hInterior),
    strictInterior_not_scalarAmplitudeKernel hInterior⟩

/-! ## 4. The rank-two residual is exactly the universal odd channel -/

theorem chainTwo_causalFutureVolumeQ_zero :
    causalFutureVolumeQ cardinalCausalChainTwo (0 : Fin 2) = 2 := by
  simp only [causalFutureVolumeQ, Fin.sum_univ_two]
  norm_num [cardinalCausalChainTwo]

theorem chainTwo_causalFutureVolumeQ_one :
    causalFutureVolumeQ cardinalCausalChainTwo (1 : Fin 2) = 1 := by
  simp only [causalFutureVolumeQ, Fin.sum_univ_two]
  norm_num [cardinalCausalChainTwo]

theorem chainTwo_normalizedCausalFutureVolumeDensityQ_zero :
    normalizedCausalFutureVolumeDensityQ
        cardinalCausalChainTwo (0 : Fin 2) = (2 : ℚ) / 3 := by
  unfold normalizedCausalFutureVolumeDensityQ
  rw [chainTwo_causalFutureVolumeQ_zero,
    chainTwo_totalCausalPastVolumeQ]

theorem chainTwo_normalizedCausalFutureVolumeDensityQ_one :
    normalizedCausalFutureVolumeDensityQ
        cardinalCausalChainTwo (1 : Fin 2) = (1 : ℚ) / 3 := by
  unfold normalizedCausalFutureVolumeDensityQ
  rw [chainTwo_causalFutureVolumeQ_one,
    chainTwo_totalCausalPastVolumeQ]

theorem chainTwo_causalVolumeShapeDensityQ (i : Fin 2) :
    causalVolumeShapeDensityQ cardinalCausalChainTwo i = (1 : ℚ) / 2 := by
  fin_cases i <;>
    norm_num [causalVolumeShapeDensityQ,
      chainTwo_normalizedCausalPastVolumeDensityQ_zero,
      chainTwo_normalizedCausalPastVolumeDensityQ_one,
      chainTwo_normalizedCausalFutureVolumeDensityQ_zero,
      chainTwo_normalizedCausalFutureVolumeDensityQ_one]

/-- The previously discovered centered curvature residual is not merely
reflection odd at rank two: it is exactly the restriction of the canonical
all-rank past-minus-future orientation channel. -/
theorem chainTwo_causalOrientationDensityQ_eq_curvatureResidual
    (i : Fin 2) :
    causalOrientationDensityQ cardinalCausalChainTwo i =
      chainTwoGeometricCurvatureResidualQ i := by
  fin_cases i
  · norm_num [causalOrientationDensityQ,
      chainTwo_normalizedCausalPastVolumeDensityQ_zero,
      chainTwo_normalizedCausalFutureVolumeDensityQ_zero,
      chainTwoGeometricCurvatureResidualQ_zero]
  · norm_num [causalOrientationDensityQ,
      chainTwo_normalizedCausalPastVolumeDensityQ_one,
      chainTwo_normalizedCausalFutureVolumeDensityQ_one,
      chainTwoGeometricCurvatureResidualQ_one]

/-! ## 4b. Reflection oddness alone is not a uniqueness principle -/

/-- Endpoint reversal on four ordered event slots. -/
def chainFourReflection (i : Fin 4) : Fin 4 :=
  ⟨3 - i.val, by omega⟩

@[simp]
theorem chainFourReflection_involution (i : Fin 4) :
    chainFourReflection (chainFourReflection i) = i := by
  fin_cases i <;> rfl

def IsChainFourReflectionOdd (profile : Fin 4 → ℚ) : Prop :=
  ∀ i, profile (chainFourReflection i) = -profile i

/-- An odd mode supported on the outer reflected pair. -/
def chainFourOuterOddProfile : Fin 4 → ℚ :=
  ![-1, 0, 0, 1]

/-- An independent odd mode supported on the inner reflected pair. -/
def chainFourInnerOddProfile : Fin 4 → ℚ :=
  ![0, -1, 1, 0]

theorem chainFourOuterOddProfile_odd :
    IsChainFourReflectionOdd chainFourOuterOddProfile := by
  intro i
  fin_cases i <;>
    norm_num [chainFourReflection, chainFourOuterOddProfile]

theorem chainFourInnerOddProfile_odd :
    IsChainFourReflectionOdd chainFourInnerOddProfile := by
  intro i
  fin_cases i <;>
    norm_num [chainFourReflection, chainFourInnerOddProfile]

/-- The rank-four odd profile sector is not one-dimensional: the inner mode is
not a scalar multiple of the outer mode.  Therefore dual oddness by itself
cannot select a unique higher-rank orientation observable. -/
theorem chainFour_reflectionOdd_sector_not_oneDimensional :
    IsChainFourReflectionOdd chainFourOuterOddProfile
      ∧ IsChainFourReflectionOdd chainFourInnerOddProfile
      ∧ ¬ ∃ coefficient : ℚ, ∀ i,
        chainFourInnerOddProfile i =
          coefficient * chainFourOuterOddProfile i := by
  refine ⟨chainFourOuterOddProfile_odd,
    chainFourInnerOddProfile_odd, ?_⟩
  rintro ⟨coefficient, hMultiple⟩
  have hAtInner := hMultiple (1 : Fin 4)
  norm_num [chainFourInnerOddProfile,
    chainFourOuterOddProfile] at hAtInner

/-! ## 5. Balanced quantum dynamics forces the chiral quarter turn -/

/-- Couple a real geometric orientation profile to one relative quantum
amplitude. -/
def geometricOrientationAmplitude {n : ℕ} (phase : ℂ)
    (parent : CardinalCausalOrder n) (i : Fin n) : ℂ :=
  phase * (causalOrientationDensityQ parent i : ℂ)

/-- The two dynamically admissible lifts written in the existing microscopic
chirality convention. -/
def chiralGeometricOrientationAmplitude {n : ℕ} (chirality : Fin 2)
    (parent : CardinalCausalOrder n) (i : Fin n) : ℂ :=
  geometricOrientationAmplitude
    (chiralMaximalEventPhase chirality) parent i

/-- A unit elementary amplitude with a balanced complementary birth is forced
to one of the two chiral geometric lifts. -/
theorem balanced_birth_derives_chiral_geometric_lift
    (phase : ℂ)
    (hUnit : Complex.normSq phase = 1)
    (hBalancedSum : Complex.normSq (1 + phase) = 2) :
    ∃ chirality : Fin 2,
      phase = chiralMaximalEventPhase chirality ∧
      ∀ {n : ℕ} (parent : CardinalCausalOrder n) (i : Fin n),
        geometricOrientationAmplitude phase parent i =
          chiralGeometricOrientationAmplitude chirality parent i := by
  rcases unit_and_balanced_sum_forces_quarter_turn
      phase hUnit hBalancedSum with hPositive | hNegative
  · refine ⟨0, ?_, ?_⟩
    · simpa [chiralMaximalEventPhase] using hPositive
    · intro n parent i
      simp [chiralGeometricOrientationAmplitude,
        geometricOrientationAmplitude, hPositive,
        chiralMaximalEventPhase]
  · refine ⟨1, ?_, ?_⟩
    · simpa [chiralMaximalEventPhase] using hNegative
    · intro n parent i
      simp [chiralGeometricOrientationAmplitude,
        geometricOrientationAmplitude, hNegative,
        chiralMaximalEventPhase]

theorem chiralMaximalEventPhase_reflected (chirality : Fin 2) :
    chiralMaximalEventPhase
        (reflectedMicroscopicChirality chirality) =
      -chiralMaximalEventPhase chirality := by
  fin_cases chirality <;>
    norm_num [chiralMaximalEventPhase, reflectedMicroscopicChirality]

/-- Reversing causal order with chirality held fixed reverses the orientation
amplitude. -/
theorem chiralGeometricOrientationAmplitude_dual_odd {n : ℕ}
    (chirality : Fin 2) (parent : CardinalCausalOrder n) (i : Fin n) :
    chiralGeometricOrientationAmplitude chirality
        (cardinalCausalOrderDual parent) i =
      -chiralGeometricOrientationAmplitude chirality parent i := by
  unfold chiralGeometricOrientationAmplitude geometricOrientationAmplitude
  rw [causalOrientationDensityQ_dual_odd]
  push_cast
  ring

/-- Microscopic chirality reflection alone also reverses the amplitude. -/
theorem chiralGeometricOrientationAmplitude_chirality_odd {n : ℕ}
    (chirality : Fin 2) (parent : CardinalCausalOrder n) (i : Fin n) :
    chiralGeometricOrientationAmplitude
        (reflectedMicroscopicChirality chirality) parent i =
      -chiralGeometricOrientationAmplitude chirality parent i := by
  unfold chiralGeometricOrientationAmplitude geometricOrientationAmplitude
  rw [chiralMaximalEventPhase_reflected]
  ring

/-- Reversing both spacetime orientation and microscopic chirality is an exact
symmetry of the lifted amplitude. -/
theorem chiralGeometricOrientationAmplitude_combined_reflection {n : ℕ}
    (chirality : Fin 2) (parent : CardinalCausalOrder n) (i : Fin n) :
    chiralGeometricOrientationAmplitude
        (reflectedMicroscopicChirality chirality)
        (cardinalCausalOrderDual parent) i =
      chiralGeometricOrientationAmplitude chirality parent i := by
  rw [chiralGeometricOrientationAmplitude_chirality_odd,
    chiralGeometricOrientationAmplitude_dual_odd]
  ring

/-! ## 6. What the construction can and cannot select -/

/-- Reflection has no fixed microscopic chirality. -/
theorem reflectedMicroscopicChirality_ne_self (chirality : Fin 2) :
    reflectedMicroscopicChirality chirality ≠ chirality := by
  fin_cases chirality <;>
    norm_num [reflectedMicroscopicChirality]

/-- A reflection-fixed complex phase cannot be either chiral quarter turn.
Thus balance selects the pair `±i`, but reflection-symmetric data cannot select
one absolute sign. -/
theorem reflection_symmetric_phase_cannot_be_chiral (phase : ℂ)
    (hReflection : star phase = phase)
    (hChiral : phase = Complex.I ∨ phase = -Complex.I) : False := by
  rcases hChiral with rfl | rfl
  · have hImaginary := congrArg Complex.im hReflection
    norm_num at hImaginary
  · have hImaginary := congrArg Complex.im hReflection
    norm_num at hImaginary

/-- The geometric two-chain orientation parameter lies strictly inside the
strong-positivity interval at both events. -/
theorem chainTwo_geometricOrientation_strictInterior (i : Fin 2) :
    |((causalOrientationDensityQ cardinalCausalChainTwo i : ℚ) : ℝ)| <
      1 / 2 := by
  fin_cases i
  · norm_num [chainTwo_causalOrientationDensityQ_eq_curvatureResidual,
      chainTwoGeometricCurvatureResidualQ_zero]
  · norm_num [chainTwo_causalOrientationDensityQ_eq_curvatureResidual,
      chainTwoGeometricCurvatureResidualQ_one]

/-- Geometry therefore produces a genuinely mixed balanced decoherence kernel
on the two-chain: latent rank two is sufficient and scalar path amplitudes are
impossible. -/
theorem chainTwo_geometry_requires_higher_rank_decoherence (i : Fin 2) :
    IsTwoComponentAmplitudeKernel
        (balancedHistoryKernel
          ((causalOrientationDensityQ cardinalCausalChainTwo i : ℚ) : ℝ))
      ∧ ¬ IsScalarAmplitudeKernel
        (balancedHistoryKernel
          ((causalOrientationDensityQ cardinalCausalChainTwo i : ℚ) : ℝ)) := by
  exact geometry_requires_higher_rank_decoherence
    cardinalCausalChainTwo i

/-- Capstone: the all-rank geometric split, the forced chiral quantum lift,
its exact reflection covariance, and the mixed-interior witness. -/
theorem geometric_orientation_dynamics_frontier :
    (∀ {n : ℕ} (parent : CardinalCausalOrder n) (i : Fin n),
      causalVolumeShapeDensityQ (cardinalCausalOrderDual parent) i =
        causalVolumeShapeDensityQ parent i)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n) (i : Fin n),
        causalOrientationDensityQ (cardinalCausalOrderDual parent) i =
          -causalOrientationDensityQ parent i)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n),
        ∑ i, causalOrientationDensityQ parent i = 0)
      ∧ (∀ (chirality : Fin 2) {n : ℕ}
          (parent : CardinalCausalOrder n) (i : Fin n),
        chiralGeometricOrientationAmplitude
            (reflectedMicroscopicChirality chirality)
            (cardinalCausalOrderDual parent) i =
          chiralGeometricOrientationAmplitude chirality parent i)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n) (i : Fin n),
        ¬ IsScalarAmplitudeKernel
          (balancedHistoryKernel
            ((causalOrientationDensityQ parent i : ℚ) : ℝ))) := by
  exact ⟨causalVolumeShapeDensityQ_dual_even,
    causalOrientationDensityQ_dual_odd,
    causalOrientationDensityQ_sum_zero,
    (by
      intro chirality n parent i
      exact chiralGeometricOrientationAmplitude_combined_reflection
        chirality parent i),
    fun parent i => (geometry_requires_higher_rank_decoherence parent i).2⟩

#print axioms unlabeledCardinalCausalOrderDual_dual
#print axioms causalOrientationDensityQ_sum_zero
#print axioms causalVolumeShapeOrientation_split_unique
#print axioms causalOrientationDensityQ_strictInterior
#print axioms geometry_requires_higher_rank_decoherence
#print axioms chainTwo_causalOrientationDensityQ_eq_curvatureResidual
#print axioms chainFour_reflectionOdd_sector_not_oneDimensional
#print axioms balanced_birth_derives_chiral_geometric_lift
#print axioms chiralGeometricOrientationAmplitude_combined_reflection
#print axioms reflection_symmetric_phase_cannot_be_chiral
#print axioms chainTwo_geometry_requires_higher_rank_decoherence
#print axioms geometric_orientation_dynamics_frontier

end

end UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics

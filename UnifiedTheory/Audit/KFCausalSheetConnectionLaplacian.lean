/-
  Audit/KFCausalSheetConnectionLaplacian.lean

  THE CAUSAL SHEET CONNECTION LAPLACIAN

  A finite reversible Markov law with permutation transport on the intrinsic
  three-sheet carrier defines a twisted transfer operator and connection
  Laplacian. This file proves its exact Dirichlet-energy identity.

  The result turns sheet holonomy into spectral data without assuming a
  preferred eigenvector. A simple ground eigenspace would select an eigenline;
  when degeneracy remains, the honest canonical object is its projector.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalDiamondDirectionCover
import UnifiedTheory.Audit.KFCubicSheetFrameRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier
open UnifiedTheory.Audit.KFCubicTwistedTransfer

universe u

abbrev SheetCarrier := ZeroSumCarrier (Fin 3)

/-- A finite reversible Markov connection on the three-sheet carrier.
The permutation at p,q transports a carrier vector at q back to p. -/
structure ReversibleSheetConnection (State : Type u) [Fintype State] where
  stationary : State → ℝ
  transition : State → State → ℝ
  sheetTransport : State → State → Equiv.Perm (Fin 3)
  stationary_pos : ∀ state, 0 < stationary state
  transition_nonneg : ∀ first second, 0 ≤ transition first second
  row_stochastic : ∀ first, ∑ second, transition first second = 1
  detailed_balance : ∀ first second,
    stationary first * transition first second =
      stationary second * transition second first
  transport_refl : ∀ state, sheetTransport state state = Equiv.refl (Fin 3)
  transport_reverse : ∀ first second,
    sheetTransport second first = (sheetTransport first second).symm

variable {State : Type u} [Fintype State]

/-- Squared norm of a carrier vector, written coordinatewise so the finite
energy calculation is completely explicit. -/
def carrierNormSq (state : SheetCarrier) : ℝ :=
  ∑ sheet, Complex.normSq (state.1 sheet)

/-- Real part of the intrinsic carrier Gram pairing. -/
def carrierRealInner (first second : SheetCarrier) : ℝ :=
  (zeroSumCarrierInner first second).re

theorem carrierNormSq_eq_realInner_self (state : SheetCarrier) :
    carrierNormSq state = carrierRealInner state state := by
  unfold carrierNormSq carrierRealInner zeroSumCarrierInner
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro sheet _hSheet
  simp [Complex.normSq_apply, Complex.mul_re]

theorem carrierNormSq_nonneg (state : SheetCarrier) :
    0 ≤ carrierNormSq state := by
  unfold carrierNormSq
  exact Finset.sum_nonneg fun sheet _hSheet =>
    Complex.normSq_nonneg (state.1 sheet)

theorem carrierNormSq_eq_zero_iff (state : SheetCarrier) :
    carrierNormSq state = 0 ↔ state = 0 := by
  constructor
  · intro hZero
    apply Subtype.ext
    funext sheet
    have hCoordinate :
        Complex.normSq (state.1 sheet) = 0 := by
      have hNonneg :
          ∀ other ∈ (Finset.univ : Finset (Fin 3)),
            0 ≤ Complex.normSq (state.1 other) :=
        fun other _ => Complex.normSq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg hNonneg).mp hZero sheet
        (Finset.mem_univ sheet)
    exact Complex.normSq_eq_zero.mp hCoordinate
  · rintro rfl
    simp [carrierNormSq]

theorem carrierNormSq_transport (relabeling : Equiv.Perm (Fin 3))
    (state : SheetCarrier) :
    carrierNormSq (transportZeroSumCarrier relabeling state) =
      carrierNormSq state := by
  rw [carrierNormSq_eq_realInner_self, carrierNormSq_eq_realInner_self]
  exact congrArg Complex.re
    (zeroSumCarrierInner_transport relabeling state state)

theorem carrierRealInner_sub_right
    (first second third : SheetCarrier) :
    carrierRealInner first (second - third) =
      carrierRealInner first second - carrierRealInner first third := by
  unfold carrierRealInner zeroSumCarrierInner
  simp_rw [Submodule.coe_sub, Pi.sub_apply, star_sub, mul_sub]
  rw [Finset.sum_sub_distrib, Complex.sub_re]

theorem carrierNormSq_sub (first second : SheetCarrier) :
    carrierNormSq (first - second) =
      carrierNormSq first + carrierNormSq second -
        2 * carrierRealInner first second := by
  unfold carrierNormSq carrierRealInner zeroSumCarrierInner
  simp_rw [Submodule.coe_sub, Pi.sub_apply, Complex.normSq_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rfl

/-- Sheet-twisted Markov transfer. -/
def twistedMarkov (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) (state : State) : SheetCarrier :=
  ∑ next,
    (law.transition state next : ℂ) •
      transportZeroSumCarrier (law.sheetTransport state next) (field next)

/-- Connection Laplacian I minus T_W. -/
def connectionLaplacian (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) (state : State) : SheetCarrier :=
  field state - twistedMarkov law field state

/-- Weighted real quadratic form of the connection Laplacian. -/
def connectionLaplacianEnergy (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) : ℝ :=
  ∑ state, law.stationary state *
    carrierRealInner (field state) (connectionLaplacian law field state)

/-- Manifestly nonnegative oriented-edge Dirichlet energy. -/
def connectionDirichletEnergy (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) : ℝ :=
  (1 / 2 : ℝ) * ∑ first, ∑ second,
    law.stationary first * law.transition first second *
      carrierNormSq
        (field first -
          transportZeroSumCarrier (law.sheetTransport first second)
            (field second))

theorem carrierRealInner_twistedMarkov
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) (state : State) :
    carrierRealInner (field state) (twistedMarkov law field state) =
      ∑ next, law.transition state next *
        carrierRealInner (field state)
          (transportZeroSumCarrier (law.sheetTransport state next)
            (field next)) := by
  unfold carrierRealInner twistedMarkov zeroSumCarrierInner
  simp only [Finset.sum_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
  rw [Complex.re_sum]
  simp_rw [star_sum, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro next _hNext
  calc
    (∑ sheet,
        ((field state).1 sheet *
          star ((law.transition state next : ℂ) *
            (transportZeroSumCarrier (law.sheetTransport state next)
              (field next)).1 sheet)).re) =
        ∑ sheet, law.transition state next *
          ((field state).1 sheet *
            star ((transportZeroSumCarrier
              (law.sheetTransport state next) (field next)).1 sheet)).re := by
      apply Finset.sum_congr rfl
      intro sheet _hSheet
      rw [star_mul]
      simp [Complex.mul_re]
      ring
    _ = law.transition state next *
        ∑ sheet,
          ((field state).1 sheet *
            star ((transportZeroSumCarrier
              (law.sheetTransport state next) (field next)).1 sheet)).re := by
      rw [Finset.mul_sum]

theorem connectionLaplacianEnergy_expand
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    connectionLaplacianEnergy law field =
      ∑ state, law.stationary state *
        (carrierNormSq (field state) -
          ∑ next, law.transition state next *
            carrierRealInner (field state)
              (transportZeroSumCarrier (law.sheetTransport state next)
                (field next))) := by
  unfold connectionLaplacianEnergy connectionLaplacian
  apply Finset.sum_congr rfl
  intro state _hState
  rw [carrierRealInner_sub_right, ← carrierNormSq_eq_realInner_self,
    carrierRealInner_twistedMarkov]

/-- Connection-Laplacian energy identity. -/
theorem connectionLaplacian_energy_identity
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    connectionLaplacianEnergy law field =
      connectionDirichletEnergy law field := by
  let normEnergy : ℝ :=
    ∑ state, law.stationary state * carrierNormSq (field state)
  let crossEnergy : ℝ :=
    ∑ first, ∑ second,
      law.stationary first * law.transition first second *
        carrierRealInner (field first)
          (transportZeroSumCarrier (law.sheetTransport first second)
            (field second))
  let firstEdgeNorm : ℝ :=
    ∑ first, ∑ second,
      law.stationary first * law.transition first second *
        carrierNormSq (field first)
  let secondEdgeNorm : ℝ :=
    ∑ first, ∑ second,
      law.stationary first * law.transition first second *
        carrierNormSq (field second)
  let twiceCrossEnergy : ℝ :=
    ∑ first, ∑ second,
      law.stationary first * law.transition first second *
        (2 * carrierRealInner (field first)
          (transportZeroSumCarrier (law.sheetTransport first second)
            (field second)))
  have hLaplacian :
      connectionLaplacianEnergy law field = normEnergy - crossEnergy := by
    rw [connectionLaplacianEnergy_expand]
    simp_rw [mul_sub, Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    unfold normEnergy crossEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro first _hFirst
    apply Finset.sum_congr rfl
    intro second _hSecond
    ring
  have hDirichlet :
      connectionDirichletEnergy law field =
        (1 / 2 : ℝ) *
          (firstEdgeNorm + secondEdgeNorm - twiceCrossEnergy) := by
    unfold connectionDirichletEnergy
    simp_rw [carrierNormSq_sub, carrierNormSq_transport]
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    unfold firstEdgeNorm secondEdgeNorm twiceCrossEnergy
    ring
  have hTwiceCross : twiceCrossEnergy = 2 * crossEnergy := by
    unfold twiceCrossEnergy crossEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _hFirst
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _hSecond
    ring
  have hFirstNorm :
      firstEdgeNorm = normEnergy := by
    unfold firstEdgeNorm normEnergy
    apply Finset.sum_congr rfl
    intro first _hFirst
    rw [← Finset.sum_mul]
    rw [← Finset.mul_sum, law.row_stochastic]
    ring
  have hSecondNorm :
      secondEdgeNorm = normEnergy := by
    unfold secondEdgeNorm normEnergy
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro second _hSecond
    have hBalance (first : State) :
        law.stationary first * law.transition first second *
            carrierNormSq (field second) =
          law.stationary second * law.transition second first *
            carrierNormSq (field second) := by
      rw [law.detailed_balance first second]
    rw [Finset.sum_congr rfl (fun first _ => hBalance first)]
    rw [← Finset.sum_mul]
    rw [← Finset.mul_sum, law.row_stochastic]
    ring
  rw [hLaplacian, hDirichlet, hFirstNorm, hSecondNorm, hTwiceCross]
  ring

theorem connectionDirichletEnergy_nonneg
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    0 ≤ connectionDirichletEnergy law field := by
  unfold connectionDirichletEnergy
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro first _hFirst
    apply Finset.sum_nonneg
    intro second _hSecond
    exact mul_nonneg
      (mul_nonneg (le_of_lt (law.stationary_pos first))
        (law.transition_nonneg first second))
      (carrierNormSq_nonneg _)

theorem connectionLaplacianEnergy_nonneg
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    0 ≤ connectionLaplacianEnergy law field := by
  rw [connectionLaplacian_energy_identity]
  exact connectionDirichletEnergy_nonneg law field

/-- Parallel sections agree with sheet transport on every positive-weight
transition. -/
def IsParallelSheetSection (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) : Prop :=
  ∀ first second, 0 < law.transition first second →
    field first =
      transportZeroSumCarrier (law.sheetTransport first second)
        (field second)

theorem connectionDirichletEnergy_eq_zero_iff_parallel
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    connectionDirichletEnergy law field = 0 ↔
      IsParallelSheetSection law field := by
  constructor
  · intro hEnergy
    unfold connectionDirichletEnergy at hEnergy
    have hDoubleSum :
        (∑ first, ∑ second,
          law.stationary first * law.transition first second *
            carrierNormSq
              (field first -
                transportZeroSumCarrier
                  (law.sheetTransport first second) (field second))) = 0 := by
      have hHalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hEnergy).resolve_left hHalf
    intro first second hTransition
    have hOuterNonneg :
        ∀ state ∈ (Finset.univ : Finset State),
          0 ≤ ∑ next,
            law.stationary state * law.transition state next *
              carrierNormSq
                (field state -
                  transportZeroSumCarrier
                    (law.sheetTransport state next) (field next)) := by
      intro state _hState
      apply Finset.sum_nonneg
      intro next _hNext
      exact mul_nonneg
        (mul_nonneg (le_of_lt (law.stationary_pos state))
          (law.transition_nonneg state next))
        (carrierNormSq_nonneg _)
    have hOuterZero :=
      (Finset.sum_eq_zero_iff_of_nonneg hOuterNonneg).mp hDoubleSum first
        (Finset.mem_univ first)
    have hInnerNonneg :
        ∀ next ∈ (Finset.univ : Finset State),
          0 ≤ law.stationary first * law.transition first next *
            carrierNormSq
              (field first -
                transportZeroSumCarrier
                  (law.sheetTransport first next) (field next)) := by
      intro next _hNext
      exact mul_nonneg
        (mul_nonneg (le_of_lt (law.stationary_pos first))
          (law.transition_nonneg first next))
        (carrierNormSq_nonneg _)
    have hTermZero :=
      (Finset.sum_eq_zero_iff_of_nonneg hInnerNonneg).mp hOuterZero second
        (Finset.mem_univ second)
    have hCoefficient :
        law.stationary first * law.transition first second ≠ 0 :=
      mul_ne_zero (ne_of_gt (law.stationary_pos first))
        (ne_of_gt hTransition)
    have hNormZero :
        carrierNormSq
          (field first -
            transportZeroSumCarrier
              (law.sheetTransport first second) (field second)) = 0 :=
      (mul_eq_zero.mp hTermZero).resolve_left hCoefficient
    exact sub_eq_zero.mp ((carrierNormSq_eq_zero_iff _).mp hNormZero)
  · intro hParallel
    unfold connectionDirichletEnergy
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro first _hFirst
    apply Finset.sum_eq_zero
    intro second _hSecond
    rcases (law.transition_nonneg first second).eq_or_lt with
      hZero | hPositive
    · rw [← hZero]
      simp
    · rw [hParallel first second hPositive]
      simp [carrierNormSq]

theorem connectionLaplacianEnergy_eq_zero_iff_parallel
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    connectionLaplacianEnergy law field = 0 ↔
      IsParallelSheetSection law field := by
  rw [connectionLaplacian_energy_identity,
    connectionDirichletEnergy_eq_zero_iff_parallel]

theorem parallel_twistedMarkov_eq
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier)
    (hParallel : IsParallelSheetSection law field) (state : State) :
    twistedMarkov law field state = field state := by
  unfold twistedMarkov
  calc
    (∑ next,
        (law.transition state next : ℂ) •
          transportZeroSumCarrier (law.sheetTransport state next)
            (field next)) =
        ∑ next, (law.transition state next : ℂ) • field state := by
      apply Finset.sum_congr rfl
      intro next _hNext
      rcases (law.transition_nonneg state next).eq_or_lt with
        hZero | hPositive
      · rw [← hZero]
        simp
      · rw [← hParallel state next hPositive]
    _ = ((∑ next, law.transition state next : ℝ) : ℂ) • field state := by
      rw [← Finset.sum_smul, Complex.ofReal_sum]
    _ = field state := by
      rw [law.row_stochastic]
      exact one_smul ℂ (field state)

/-- The connection-Laplacian kernel is exactly the space of parallel carrier
sections. -/
theorem connectionLaplacian_eq_zero_iff_parallel
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier) :
    (∀ state, connectionLaplacian law field state = 0) ↔
      IsParallelSheetSection law field := by
  constructor
  · intro hKernel
    rw [← connectionLaplacianEnergy_eq_zero_iff_parallel]
    unfold connectionLaplacianEnergy
    apply Finset.sum_eq_zero
    intro state _hState
    rw [hKernel state]
    simp [carrierRealInner, zeroSumCarrierInner]
  · intro hParallel state
    unfold connectionLaplacian
    rw [parallel_twistedMarkov_eq law field hParallel state]
    exact sub_self _

/-! ## Path holonomy and removal of the parallel zero mode -/

/-- A path using only positive-weight transitions of the reversible law. -/
inductive PositiveConnectionPath (law : ReversibleSheetConnection State) :
    State → State → Type u
  | nil (state : State) : PositiveConnectionPath law state state
  | cons (start next : State) {finish : State}
      (hPositive : 0 < law.transition start next)
      (tail : PositiveConnectionPath law next finish) :
      PositiveConnectionPath law start finish

/-- Sheet permutation transported from the endpoint back to the start of a
positive connection path. -/
def positivePathSheetTransport (law : ReversibleSheetConnection State)
    {start finish : State} :
    PositiveConnectionPath law start finish → Equiv.Perm (Fin 3)
  | .nil _ => Equiv.refl (Fin 3)
  | .cons start next _ tail =>
      (positivePathSheetTransport law tail).trans
        (law.sheetTransport start next)

theorem parallelSection_path_transport
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier)
    (hParallel : IsParallelSheetSection law field)
    {start finish : State}
    (path : PositiveConnectionPath law start finish) :
    field start =
      transportZeroSumCarrier (positivePathSheetTransport law path)
        (field finish) := by
  induction path with
  | nil state =>
      rw [positivePathSheetTransport, transportZeroSumCarrier_refl]
  | @cons start next finish hPositive tail ih =>
      calc
        field start =
            transportZeroSumCarrier (law.sheetTransport start next)
              (field next) :=
          hParallel start next hPositive
        _ = transportZeroSumCarrier (law.sheetTransport start next)
              (transportZeroSumCarrier
                (positivePathSheetTransport law tail) (field finish)) := by
          rw [ih]
        _ = transportZeroSumCarrier
              ((positivePathSheetTransport law tail).trans
                (law.sheetTransport start next)) (field finish) := by
          exact transportZeroSumCarrier_trans
            (positivePathSheetTransport law tail)
            (law.sheetTransport start next) (field finish)
        _ = transportZeroSumCarrier
              (positivePathSheetTransport law
                (.cons start next hPositive tail)) (field finish) := rfl

/-- Every sheet permutation occurs as a positive closed-path holonomy at the
base state. -/
def HasFullS3Holonomy (law : ReversibleSheetConnection State)
    (base : State) : Prop :=
  ∀ relabeling : Equiv.Perm (Fin 3),
    ∃ path : PositiveConnectionPath law base base,
      positivePathSheetTransport law path = relabeling

/-- Every state is reachable from the base through positive transitions. -/
def PositiveConnectedFrom (law : ReversibleSheetConnection State)
    (base : State) : Prop :=
  ∀ state, Nonempty (PositiveConnectionPath law base state)

theorem fullS3Holonomy_parallel_base_eq_zero
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier)
    (hParallel : IsParallelSheetSection law field)
    (base : State) (hFull : HasFullS3Holonomy law base) :
    field base = 0 := by
  apply fixed_by_all_sheet_permutations_eq_zero (S := Fin 3) (by decide)
  intro relabeling
  obtain ⟨path, hPath⟩ := hFull relabeling
  have hTransport :=
    (parallelSection_path_transport law field hParallel path).symm
  simpa [hPath] using hTransport

/-- Full S3 holonomy plus positive connectivity leaves no nonzero parallel
carrier section. This is the exact finite form of
kernel(Delta_W) = carrier fixed by holonomy. -/
theorem fullS3Holonomy_parallel_section_eq_zero
    (law : ReversibleSheetConnection State)
    (field : State → SheetCarrier)
    (hParallel : IsParallelSheetSection law field)
    (base : State) (hFull : HasFullS3Holonomy law base)
    (hConnected : PositiveConnectedFrom law base) :
    field = 0 := by
  funext state
  obtain ⟨path⟩ := hConnected state
  have hPath :=
    parallelSection_path_transport law field hParallel path
  have hBase := fullS3Holonomy_parallel_base_eq_zero
    law field hParallel base hFull
  have hTransportZero :
      transportZeroSumCarrier (positivePathSheetTransport law path)
          (field state) = 0 := by
    rw [← hPath, hBase]
  apply (transportZeroSumCarrier
    (positivePathSheetTransport law path)).injective
  simpa using hTransportZero

/-- **Holonomy spectral capstone.** Under full S3 holonomy and positive
connectivity, the connection Laplacian has trivial kernel. -/
theorem fullS3Holonomy_connectionLaplacian_kernel_trivial
    (law : ReversibleSheetConnection State)
    (base : State) (hFull : HasFullS3Holonomy law base)
    (hConnected : PositiveConnectedFrom law base)
    (field : State → SheetCarrier)
    (hKernel : ∀ state, connectionLaplacian law field state = 0) :
    field = 0 := by
  apply fullS3Holonomy_parallel_section_eq_zero law field
    ((connectionLaplacian_eq_zero_iff_parallel law field).mp hKernel)
    base hFull hConnected

/-- Equivalently, every nonzero carrier field has strictly positive twisted
Dirichlet energy when the holonomy is full and the positive graph connected.
This is a qualitative finite spectral gap statement; no numerical lower bound
is asserted. -/
theorem fullS3Holonomy_nonzero_energy_pos
    (law : ReversibleSheetConnection State)
    (base : State) (hFull : HasFullS3Holonomy law base)
    (hConnected : PositiveConnectedFrom law base)
    (field : State → SheetCarrier) (hField : field ≠ 0) :
    0 < connectionLaplacianEnergy law field := by
  have hNonnegative := connectionLaplacianEnergy_nonneg law field
  apply lt_of_le_of_ne hNonnegative
  intro hZeroReverse
  have hParallel :=
    (connectionLaplacianEnergy_eq_zero_iff_parallel law field).mp
      hZeroReverse.symm
  exact hField
    (fullS3Holonomy_parallel_section_eq_zero law field hParallel
      base hFull hConnected)

#print axioms connectionLaplacian_energy_identity
#print axioms connectionLaplacianEnergy_nonneg
#print axioms connectionLaplacian_eq_zero_iff_parallel
#print axioms fullS3Holonomy_connectionLaplacian_kernel_trivial
#print axioms fullS3Holonomy_nonzero_energy_pos

end

end UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian

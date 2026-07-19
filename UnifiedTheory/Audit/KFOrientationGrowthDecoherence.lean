/-
  Audit/KFOrientationGrowthDecoherence.lean

  NORMALIZED STRONGLY POSITIVE DECOHERENCE ON UNLABELED GROWTH ROUTES

  The preceding frontier file constructed an associative serial composition of
  unlabeled finite causal orders and an exact CPTP orientation channel.  This
  file supplies the next missing quantum-history object.

  A complete growth trajectory is a binary refinement tree.  Its leaves are
  unlabeled causal histories and every internal node retains an intermediate
  refinement, so the object records the whole finite growth route rather than
  only its final order.  The two associator routes

      ((h then k) then l),       (h then (k then l))

  are distinct complete trajectories with the same unlabeled final history.

  Their amplitudes have equal magnitude and relative phase determined by the
  multiplicative orientation sign of that final history.  The resulting Gram
  kernel is Hermitian, normalized, and strongly positive on every finite family
  of routes.  Its exact two-route restriction is the previously classified
  extremal history kernel, and that kernel is exactly the output of the proved
  CPTP refinement channel.

  This is a finite quantum sequential-growth model for the associator sector.
  It is not yet a measure on every causal-set extension or an infinite-cylinder
  completion.
-/

import UnifiedTheory.Audit.KFOrientationUnlabeledRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationGrowthDecoherence

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHistoryRefinementChannel
open UnifiedTheory.Audit.KFOrientationUnlabeledRefinement

/-! ## 1. Complete unlabeled growth trajectories -/

/-- A complete finite growth trajectory is a binary refinement tree.  Unlike
its realized endpoint, the tree retains every intermediate refinement and its
parenthesization. -/
inductive CompleteUnlabeledGrowthTrajectory where
  | atom (history : UnlabeledOrientationHistory)
  | refine (left right : CompleteUnlabeledGrowthTrajectory)

/-- Realize every internal node using the concrete covariant ordinal
refinement on unlabeled histories. -/
def CompleteUnlabeledGrowthTrajectory.realize :
    CompleteUnlabeledGrowthTrajectory → UnlabeledOrientationHistory
  | .atom history => history
  | .refine left right =>
      ordinalCausalRefinement.descend left.realize right.realize

/-- Number of atomic growth blocks retained by a complete trajectory. -/
def CompleteUnlabeledGrowthTrajectory.atomCount :
    CompleteUnlabeledGrowthTrajectory → ℕ
  | .atom _ => 1
  | .refine left right => left.atomCount + right.atomCount

@[simp]
theorem CompleteUnlabeledGrowthTrajectory.realize_atom
    (h : UnlabeledOrientationHistory) :
    (CompleteUnlabeledGrowthTrajectory.atom h).realize = h := rfl

@[simp]
theorem CompleteUnlabeledGrowthTrajectory.realize_refine
    (left right : CompleteUnlabeledGrowthTrajectory) :
    (CompleteUnlabeledGrowthTrajectory.refine left right).realize =
      ordinalCausalRefinement.descend left.realize right.realize := rfl

/-- Orientation is multiplicative at every internal growth node. -/
theorem CompleteUnlabeledGrowthTrajectory.realize_refine_sign
    (left right : CompleteUnlabeledGrowthTrajectory) :
    unlabeledOrientationSign
        (CompleteUnlabeledGrowthTrajectory.refine left right).realize =
      unlabeledOrientationSign left.realize *
        unlabeledOrientationSign right.realize := by
  exact unlabeledOrientationSign_mul left.realize right.realize

/-- The left-associated complete three-block growth route. -/
def associatorLeftTrajectory (h k l : UnlabeledOrientationHistory) :
    CompleteUnlabeledGrowthTrajectory :=
  .refine (.refine (.atom h) (.atom k)) (.atom l)

/-- The right-associated complete three-block growth route. -/
def associatorRightTrajectory (h k l : UnlabeledOrientationHistory) :
    CompleteUnlabeledGrowthTrajectory :=
  .refine (.atom h) (.refine (.atom k) (.atom l))

/-- Route `0` is left-associated and route `1` is right-associated. -/
def associatorTrajectory (h k l : UnlabeledOrientationHistory) (route : Fin 2) :
    CompleteUnlabeledGrowthTrajectory :=
  if route = 0 then associatorLeftTrajectory h k l
  else associatorRightTrajectory h k l

/-- The common unlabeled final history of the two complete associator routes. -/
def associatorFinalHistory (h k l : UnlabeledOrientationHistory) :
    UnlabeledOrientationHistory :=
  ordinalCausalRefinement.descend
    (ordinalCausalRefinement.descend h k) l

theorem associatorLeftTrajectory_realize
    (h k l : UnlabeledOrientationHistory) :
    (associatorLeftTrajectory h k l).realize =
      associatorFinalHistory h k l := rfl

theorem associatorRightTrajectory_realize
    (h k l : UnlabeledOrientationHistory) :
    (associatorRightTrajectory h k l).realize =
      associatorFinalHistory h k l := by
  exact (ordinalCausalRefinement_descend_assoc h k l).symm

/-- Both complete routes end at exactly the same unlabeled causal history. -/
theorem associatorTrajectory_realize
    (h k l : UnlabeledOrientationHistory) (route : Fin 2) :
    (associatorTrajectory h k l route).realize =
      associatorFinalHistory h k l := by
  fin_cases route
  · exact associatorLeftTrajectory_realize h k l
  · exact associatorRightTrajectory_realize h k l

theorem associatorTrajectory_atomCount
    (h k l : UnlabeledOrientationHistory) (route : Fin 2) :
    (associatorTrajectory h k l route).atomCount = 3 := by
  fin_cases route <;>
    norm_num [associatorTrajectory, associatorLeftTrajectory,
      associatorRightTrajectory,
      CompleteUnlabeledGrowthTrajectory.atomCount]

/-- The two route labels represent genuinely distinct complete growth trees,
even though quotient associativity identifies their final unlabeled history. -/
theorem associatorTrajectory_injective
    (h k l : UnlabeledOrientationHistory) :
    Function.Injective (associatorTrajectory h k l) := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;>
    simp [associatorTrajectory, associatorLeftTrajectory,
      associatorRightTrajectory] at hpq ⊢

/-! ## 2. Decoherence-functional contracts -/

/-- A complex decoherence kernel on a history type. -/
abbrev GrowthDecoherenceFunctional (History : Type*) :=
  History → History → ℂ

/-- Hermiticity of a history kernel. -/
def IsHermitianGrowthFunctional {History : Type*}
    (D : GrowthDecoherenceFunctional History) : Prop :=
  ∀ h k, D h k = star (D k h)

/-- Strong positivity means that every finite matrix sampled from the history
kernel is positive semidefinite, including samples with repeated histories. -/
def IsStronglyPositiveGrowthFunctional {History : Type*}
    (D : GrowthDecoherenceFunctional History) : Prop :=
  ∀ (n : ℕ) (sample : Fin n → History),
    Matrix.PosSemidef (fun i j => D (sample i) (sample j))

/-- Complex normalization of the total finite history event. -/
def IsNormalizedGrowthFunctional {History : Type*} [Fintype History]
    (D : GrowthDecoherenceFunctional History) : Prop :=
  ∑ h, ∑ k, D h k = 1

/-- A normalized strongly positive decoherence functional on a finite history
experiment. -/
structure NormalizedStronglyPositiveGrowthFunctional (History : Type*)
    [Fintype History] where
  kernel : GrowthDecoherenceFunctional History
  hermitian : IsHermitianGrowthFunctional kernel
  stronglyPositive : IsStronglyPositiveGrowthFunctional kernel
  normalized : IsNormalizedGrowthFunctional kernel

/-- Every scalar amplitude law generates its canonical rank-one Gram kernel. -/
def amplitudeDecoherence {History : Type*} (amplitude : History → ℂ) :
    GrowthDecoherenceFunctional History :=
  fun h k => amplitude h * star (amplitude k)

theorem amplitudeDecoherence_hermitian {History : Type*}
    (amplitude : History → ℂ) :
    IsHermitianGrowthFunctional (amplitudeDecoherence amplitude) := by
  intro h k
  simp [amplitudeDecoherence, mul_comm]

/-- Gram construction proves strong positivity simultaneously for every finite
family of histories. -/
theorem amplitudeDecoherence_stronglyPositive {History : Type*}
    (amplitude : History → ℂ) :
    IsStronglyPositiveGrowthFunctional (amplitudeDecoherence amplitude) := by
  intro n sample
  let column : Matrix (Fin n) (Fin 1) ℂ :=
    fun i _ => amplitude (sample i)
  have hPos : (column * column.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose column
  have hEq : (fun i j =>
      amplitudeDecoherence amplitude (sample i) (sample j)) =
      column * column.conjTranspose := by
    ext i j
    simp [column, amplitudeDecoherence, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  rw [hEq]
  exact hPos

/-! ## 2b. Event extension -/

/-- Bilinear extension of an atomic history kernel to finite history events. -/
def growthEventDecoherence {History : Type*}
    (D : GrowthDecoherenceFunctional History)
    (event₁ event₂ : Finset History) : ℂ :=
  ∑ h ∈ event₁, ∑ k ∈ event₂, D h k

@[simp]
theorem growthEventDecoherence_empty_left {History : Type*}
    (D : GrowthDecoherenceFunctional History) (event : Finset History) :
    growthEventDecoherence D ∅ event = 0 := by
  simp [growthEventDecoherence]

@[simp]
theorem growthEventDecoherence_empty_right {History : Type*}
    (D : GrowthDecoherenceFunctional History) (event : Finset History) :
    growthEventDecoherence D event ∅ = 0 := by
  simp [growthEventDecoherence]

/-- Decoherence is finitely additive in its first event argument. -/
theorem growthEventDecoherence_union_left {History : Type*}
    [DecidableEq History]
    (D : GrowthDecoherenceFunctional History)
    (event₁ event₂ event₃ : Finset History)
    (hDisjoint : Disjoint event₁ event₂) :
    growthEventDecoherence D (event₁ ∪ event₂) event₃ =
      growthEventDecoherence D event₁ event₃ +
        growthEventDecoherence D event₂ event₃ := by
  unfold growthEventDecoherence
  rw [Finset.sum_union hDisjoint]

/-- Decoherence is finitely additive in its second event argument. -/
theorem growthEventDecoherence_union_right {History : Type*}
    [DecidableEq History]
    (D : GrowthDecoherenceFunctional History)
    (event₁ event₂ event₃ : Finset History)
    (hDisjoint : Disjoint event₂ event₃) :
    growthEventDecoherence D event₁ (event₂ ∪ event₃) =
      growthEventDecoherence D event₁ event₂ +
        growthEventDecoherence D event₁ event₃ := by
  unfold growthEventDecoherence
  simp_rw [Finset.sum_union hDisjoint]
  rw [Finset.sum_add_distrib]

/-- The quantum measure is the real diagonal of the event decoherence
functional. -/
def growthQuantumMeasure {History : Type*}
    (D : GrowthDecoherenceFunctional History) (event : Finset History) : ℝ :=
  (growthEventDecoherence D event event).re

theorem amplitude_growthEventDecoherence_eq {History : Type*}
    (amplitude : History → ℂ) (event₁ event₂ : Finset History) :
    growthEventDecoherence (amplitudeDecoherence amplitude) event₁ event₂ =
      (∑ h ∈ event₁, amplitude h) *
        star (∑ k ∈ event₂, amplitude k) := by
  unfold growthEventDecoherence amplitudeDecoherence
  calc
    (∑ h ∈ event₁, ∑ k ∈ event₂,
        amplitude h * star (amplitude k)) =
        ∑ h ∈ event₁,
          amplitude h * (∑ k ∈ event₂, star (amplitude k)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
    _ = (∑ h ∈ event₁, amplitude h) *
        (∑ k ∈ event₂, star (amplitude k)) := by
      rw [Finset.sum_mul]
    _ = (∑ h ∈ event₁, amplitude h) *
        star (∑ k ∈ event₂, amplitude k) := by
      rw [star_sum]

theorem amplitude_growthEventDecoherence_hermitian {History : Type*}
    (amplitude : History → ℂ) :
    IsHermitianGrowthFunctional
      (growthEventDecoherence (amplitudeDecoherence amplitude)) := by
  intro event₁ event₂
  rw [amplitude_growthEventDecoherence_eq,
    amplitude_growthEventDecoherence_eq]
  simp [mul_comm]

/-- The Gram construction is strongly positive on arbitrary finite families
of finite events, which is the standard strong-positivity condition for a
decoherence functional. -/
theorem amplitude_growthEventDecoherence_stronglyPositive
    {History : Type*} (amplitude : History → ℂ) :
    IsStronglyPositiveGrowthFunctional
      (growthEventDecoherence (amplitudeDecoherence amplitude)) := by
  have hEq : growthEventDecoherence (amplitudeDecoherence amplitude) =
      amplitudeDecoherence
        (fun event : Finset History => ∑ h ∈ event, amplitude h) := by
    funext event₁ event₂
    exact amplitude_growthEventDecoherence_eq amplitude event₁ event₂
  rw [hEq]
  exact amplitudeDecoherence_stronglyPositive _

/-- Every finite event has nonnegative quantum measure. -/
theorem amplitude_growthQuantumMeasure_nonneg {History : Type*}
    (amplitude : History → ℂ) (event : Finset History) :
    0 ≤ growthQuantumMeasure (amplitudeDecoherence amplitude) event := by
  rw [growthQuantumMeasure,
    amplitude_growthEventDecoherence_eq amplitude event event]
  let z : ℂ := ∑ h ∈ event, amplitude h
  change 0 ≤ (z * star z).re
  have hEq : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    have h := Complex.mul_conj z
    change z * star z = ((Complex.normSq z : ℝ) : ℂ)
    convert h using 1
  rw [hEq]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg z

theorem amplitude_growthQuantumMeasure_eq_normSq {History : Type*}
    (amplitude : History → ℂ) (event : Finset History) :
    growthQuantumMeasure (amplitudeDecoherence amplitude) event =
      Complex.normSq (∑ h ∈ event, amplitude h) := by
  rw [growthQuantumMeasure,
    amplitude_growthEventDecoherence_eq amplitude event event]
  let z : ℂ := ∑ h ∈ event, amplitude h
  change (z * star z).re = Complex.normSq z
  have hEq : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    have h := Complex.mul_conj z
    change z * star z = ((Complex.normSq z : ℝ) : ℂ)
    convert h using 1
  rw [hEq]
  simp only [Complex.ofReal_re]

/-- The induced quantum measure obeys Sorkin's grade-two sum rule on three
pairwise-disjoint finite events. -/
theorem amplitude_growthQuantumMeasure_gradeTwo {History : Type*}
    [DecidableEq History]
    (amplitude : History → ℂ) (event₁ event₂ event₃ : Finset History)
    (h₁₂ : Disjoint event₁ event₂)
    (h₁₃ : Disjoint event₁ event₃)
    (h₂₃ : Disjoint event₂ event₃) :
    growthQuantumMeasure (amplitudeDecoherence amplitude)
        ((event₁ ∪ event₂) ∪ event₃) =
      growthQuantumMeasure (amplitudeDecoherence amplitude) (event₁ ∪ event₂) +
        growthQuantumMeasure (amplitudeDecoherence amplitude) (event₁ ∪ event₃) +
        growthQuantumMeasure (amplitudeDecoherence amplitude) (event₂ ∪ event₃) -
        growthQuantumMeasure (amplitudeDecoherence amplitude) event₁ -
        growthQuantumMeasure (amplitudeDecoherence amplitude) event₂ -
        growthQuantumMeasure (amplitudeDecoherence amplitude) event₃ := by
  have h₁₂₃ : Disjoint (event₁ ∪ event₂) event₃ :=
    Finset.disjoint_union_left.mpr ⟨h₁₃, h₂₃⟩
  simp_rw [amplitude_growthQuantumMeasure_eq_normSq amplitude]
  rw [Finset.sum_union h₁₂₃, Finset.sum_union h₁₂,
    Finset.sum_union h₁₃, Finset.sum_union h₂₃]
  simp only [Complex.normSq_add, add_mul, Complex.add_re]
  ring

theorem normalized_total_event {History : Type*} [Fintype History]
    (D : GrowthDecoherenceFunctional History)
    (hNormalized : IsNormalizedGrowthFunctional D) :
    growthEventDecoherence D Finset.univ Finset.univ = 1 := by
  simpa [growthEventDecoherence, IsNormalizedGrowthFunctional] using
    hNormalized

/-! ## 3. Dynamical associator amplitudes -/

/-- The route amplitude associated with an unlabeled final history.  Route `0`
has real amplitude `1/sqrt(2)`; route `1` acquires the phase
`-i * orientationSign`. -/
def orientationGrowthAmplitude
    (history : UnlabeledOrientationHistory) (route : Fin 2) : ℂ :=
  if route = 0 then ((1 / spinOneSqrtTwo : ℝ) : ℂ)
  else -Complex.I * (unlabeledOrientationSign history : ℂ) *
    ((1 / spinOneSqrtTwo : ℝ) : ℂ)

def orientationGrowthKet
    (history : UnlabeledOrientationHistory) : PathKet :=
  fun route _ => orientationGrowthAmplitude history route

theorem orientationGrowthKet_of_endpoint_zero
    (history : UnlabeledOrientationHistory)
    (hEndpoint : unlabeledEndpoint history = 0) :
    orientationGrowthKet history = positiveHolonomyKet := by
  ext route j
  fin_cases route <;> fin_cases j <;>
    norm_num [orientationGrowthKet, orientationGrowthAmplitude,
      unlabeledOrientationSign, hEndpoint, endpointParameter,
      positiveHolonomyKet, Fin.ext_iff]

theorem orientationGrowthKet_of_endpoint_one
    (history : UnlabeledOrientationHistory)
    (hEndpoint : unlabeledEndpoint history = 1) :
    orientationGrowthKet history = negativeHolonomyKet := by
  ext route j
  fin_cases route <;> fin_cases j <;>
    norm_num [orientationGrowthKet, orientationGrowthAmplitude,
      unlabeledOrientationSign, hEndpoint, endpointParameter,
      negativeHolonomyKet, Fin.ext_iff]

/-! ## 3b. Microscopic generation of the route amplitudes -/

/-- The pure two-endpoint input selected by a pair of unlabeled histories. -/
def endpointPairKet (a b : Fin 2) : PairKet :=
  if a = 0 then
    if b = 0 then positivePositiveKet else positiveNegativeKet
  else if b = 0 then negativePositiveKet else negativeNegativeKet

/-- Orthogonal refinement record associated with endpoint pair
`00, 01, 10, 11`. -/
def endpointPairRecord (a b : Fin 2) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else 1
  else if b = 0 then 2 else 3

@[simp]
theorem recordedOutputKet_at_record
    (out : PathKet) (record : Fin 4) (route : Fin 2) :
    recordedOutputKet out record (route, record) 0 = out route 0 := by
  simp [recordedOutputKet]

/-- The local Stinespring isometry generates the orientation-growth ket of
the refined unlabeled history, while retaining the microscopic endpoint pair
in an orthogonal environment record.  Hence the relative phase in the growth
functional is an output amplitude of the reversible dilation, not merely a
density-matrix ansatz. -/
theorem refinementDilation_derives_orientationGrowthKet
    (h k : UnlabeledOrientationHistory) :
    refinementDilation *
        endpointPairKet (unlabeledEndpoint h) (unlabeledEndpoint k) =
      recordedOutputKet
        (orientationGrowthKet (ordinalCausalRefinement.descend h k))
        (endpointPairRecord (unlabeledEndpoint h) (unlabeledEndpoint k)) := by
  generalize ha : unlabeledEndpoint h = a
  generalize hb : unlabeledEndpoint k = b
  fin_cases a <;> fin_cases b
  · rw [orientationGrowthKet_of_endpoint_one _ (by
      rw [ordinalCausalRefinement.unlabeled_endpoint_parity, ha, hb]
      norm_num [endpointCompose, Fin.ext_iff])]
    simpa [endpointPairKet, endpointPairRecord, ha, hb, Fin.ext_iff] using
      refinementDilation_positivePositive_amplitude
  · rw [orientationGrowthKet_of_endpoint_zero _ (by
      rw [ordinalCausalRefinement.unlabeled_endpoint_parity, ha, hb]
      norm_num [endpointCompose, Fin.ext_iff])]
    simpa [endpointPairKet, endpointPairRecord, ha, hb, Fin.ext_iff] using
      refinementDilation_positiveNegative_amplitude
  · rw [orientationGrowthKet_of_endpoint_zero _ (by
      rw [ordinalCausalRefinement.unlabeled_endpoint_parity, ha, hb]
      norm_num [endpointCompose, Fin.ext_iff])]
    simpa [endpointPairKet, endpointPairRecord, ha, hb, Fin.ext_iff] using
      refinementDilation_negativePositive_amplitude
  · rw [orientationGrowthKet_of_endpoint_one _ (by
      rw [ordinalCausalRefinement.unlabeled_endpoint_parity, ha, hb]
      norm_num [endpointCompose, Fin.ext_iff])]
    simpa [endpointPairKet, endpointPairRecord, ha, hb, Fin.ext_iff] using
      refinementDilation_negativeNegative_amplitude

/-- Density kernel generated by the two complete associator-route amplitudes. -/
def orientationGrowthDecoherence
    (history : UnlabeledOrientationHistory) :
    GrowthDecoherenceFunctional (Fin 2) :=
  amplitudeDecoherence (orientationGrowthAmplitude history)

theorem orientationGrowthDecoherence_matrix_eq_ketDensity
    (history : UnlabeledOrientationHistory) :
    (fun p q => orientationGrowthDecoherence history p q) =
      ketDensity (orientationGrowthKet history) := by
  ext p q
  simp [orientationGrowthDecoherence, amplitudeDecoherence,
    orientationGrowthKet, ketDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- The full growth-route decoherence kernel is exactly the previously
classified extremal history kernel selected by the final causal orientation. -/
theorem orientationGrowthDecoherence_eq_unlabeledHistoryKernel
    (history : UnlabeledOrientationHistory) :
    (fun p q => orientationGrowthDecoherence history p q) =
      unlabeledHistoryKernel history := by
  rw [orientationGrowthDecoherence_matrix_eq_ketDensity]
  generalize hEndpoint : unlabeledEndpoint history = endpoint
  fin_cases endpoint
  · rw [orientationGrowthKet_of_endpoint_zero history hEndpoint]
    rw [positiveKet_density_eq_projector]
    simpa [unlabeledHistoryKernel, hEndpoint, endpointParameter] using
      balancedHistoryKernel_negativeEndpoint.symm
  · rw [orientationGrowthKet_of_endpoint_one history hEndpoint]
    rw [negativeKet_density_eq_projector]
    simpa [unlabeledHistoryKernel, hEndpoint, endpointParameter] using
      balancedHistoryKernel_positiveEndpoint.symm

theorem balancedHistoryKernel_complex_total (y : ℝ) :
    ∑ p : Fin 2, ∑ q : Fin 2, balancedHistoryKernel y p q = 1 := by
  norm_num [balancedHistoryKernel, Fin.sum_univ_succ, Fin.ext_iff]
  ring

theorem orientationGrowthDecoherence_normalized
    (history : UnlabeledOrientationHistory) :
    IsNormalizedGrowthFunctional (orientationGrowthDecoherence history) := by
  unfold IsNormalizedGrowthFunctional
  change ∑ p, ∑ q,
    (fun i j => orientationGrowthDecoherence history i j) p q = 1
  rw [orientationGrowthDecoherence_eq_unlabeledHistoryKernel]
  exact balancedHistoryKernel_complex_total
    (endpointParameter (unlabeledEndpoint history))

theorem orientationGrowthDecoherence_stronglyPositive
    (history : UnlabeledOrientationHistory) :
    IsStronglyPositiveGrowthFunctional
      (orientationGrowthDecoherence history) := by
  exact amplitudeDecoherence_stronglyPositive
    (orientationGrowthAmplitude history)

theorem orientationGrowthDecoherence_hermitian
    (history : UnlabeledOrientationHistory) :
    IsHermitianGrowthFunctional (orientationGrowthDecoherence history) := by
  exact amplitudeDecoherence_hermitian
    (orientationGrowthAmplitude history)

/-- Strong positivity at event level: arbitrary finite families of finite
route-events have a positive-semidefinite decoherence matrix. -/
theorem orientationGrowthEventDecoherence_stronglyPositive
    (history : UnlabeledOrientationHistory) :
    IsStronglyPositiveGrowthFunctional
      (growthEventDecoherence (orientationGrowthDecoherence history)) := by
  exact amplitude_growthEventDecoherence_stronglyPositive
    (orientationGrowthAmplitude history)

theorem orientationGrowthEventDecoherence_hermitian
    (history : UnlabeledOrientationHistory) :
    IsHermitianGrowthFunctional
      (growthEventDecoherence (orientationGrowthDecoherence history)) := by
  exact amplitude_growthEventDecoherence_hermitian
    (orientationGrowthAmplitude history)

/-- Every route-event has a nonnegative quantum measure. -/
theorem orientationGrowthQuantumMeasure_nonneg
    (history : UnlabeledOrientationHistory) (event : Finset (Fin 2)) :
    0 ≤ growthQuantumMeasure (orientationGrowthDecoherence history) event := by
  exact amplitude_growthQuantumMeasure_nonneg
    (orientationGrowthAmplitude history) event

/-- The orientation quantum measure has no irreducible third-order
interference: it obeys the grade-two sum rule on pairwise-disjoint events. -/
theorem orientationGrowthQuantumMeasure_gradeTwo
    (history : UnlabeledOrientationHistory)
    (event₁ event₂ event₃ : Finset (Fin 2))
    (h₁₂ : Disjoint event₁ event₂)
    (h₁₃ : Disjoint event₁ event₃)
    (h₂₃ : Disjoint event₂ event₃) :
    growthQuantumMeasure (orientationGrowthDecoherence history)
        ((event₁ ∪ event₂) ∪ event₃) =
      growthQuantumMeasure (orientationGrowthDecoherence history)
          (event₁ ∪ event₂) +
        growthQuantumMeasure (orientationGrowthDecoherence history)
          (event₁ ∪ event₃) +
        growthQuantumMeasure (orientationGrowthDecoherence history)
          (event₂ ∪ event₃) -
        growthQuantumMeasure (orientationGrowthDecoherence history) event₁ -
        growthQuantumMeasure (orientationGrowthDecoherence history) event₂ -
        growthQuantumMeasure (orientationGrowthDecoherence history) event₃ := by
  exact amplitude_growthQuantumMeasure_gradeTwo
    (orientationGrowthAmplitude history) event₁ event₂ event₃ h₁₂ h₁₃ h₂₃

/-- The event containing all complete associator routes has unit
decoherence weight. -/
theorem orientationGrowthTotalEvent_normalized
    (history : UnlabeledOrientationHistory) :
    growthEventDecoherence (orientationGrowthDecoherence history)
        Finset.univ Finset.univ = 1 := by
  exact normalized_total_event _
    (orientationGrowthDecoherence_normalized history)

/-- The normalized strongly positive functional carried by the two complete
associator growth trajectories. -/
def associatorGrowthDecoherenceFunctional
    (h k l : UnlabeledOrientationHistory) :
    NormalizedStronglyPositiveGrowthFunctional (Fin 2) where
  kernel := orientationGrowthDecoherence (associatorFinalHistory h k l)
  hermitian := orientationGrowthDecoherence_hermitian _
  stronglyPositive := orientationGrowthDecoherence_stronglyPositive _
  normalized := orientationGrowthDecoherence_normalized _

/-! ## 4. Exact derivation of the finite channel model -/

/-- The final sign is computed dynamically as the product of the three input
orientation signs. -/
theorem associatorFinalHistory_sign
    (h k l : UnlabeledOrientationHistory) :
    unlabeledOrientationSign (associatorFinalHistory h k l) =
      unlabeledOrientationSign h * unlabeledOrientationSign k *
        unlabeledOrientationSign l := by
  unfold associatorFinalHistory
  rw [unlabeledOrientationSign_mul, unlabeledOrientationSign_mul]

/-- Restricting the complete growth functional to its two routes gives exactly
the endpoint kernel of their common unlabeled final history. -/
theorem associatorGrowthDecoherence_restriction
    (h k l : UnlabeledOrientationHistory) :
    (fun p q =>
      (associatorGrowthDecoherenceFunctional h k l).kernel p q) =
        unlabeledHistoryKernel (associatorFinalHistory h k l) := by
  exact orientationGrowthDecoherence_eq_unlabeledHistoryKernel _

/-- The same kernel is the exact output of the already proved CPTP refinement
channel.  Thus the channel is derived as the reduced dynamics of the complete
two-route growth functional, rather than postulated independently. -/
theorem associatorGrowthDecoherence_derives_refinementChannel
    (h k l : UnlabeledOrientationHistory) :
    (fun p q =>
      (associatorGrowthDecoherenceFunctional h k l).kernel p q) =
      orientationRefinementKraus.apply
        (historyKernelTensor
          (unlabeledHistoryKernel
            (ordinalCausalRefinement.descend h k))
          (unlabeledHistoryKernel l)) := by
  rw [associatorGrowthDecoherence_restriction]
  exact (ordinalCausalRefinement.channel_descends
    (ordinalCausalRefinement.descend h k) l).symm

/-- The final associator-route amplitudes are generated one refinement step
earlier by the explicit reversible microscopic dilation. -/
theorem associatorGrowthAmplitude_microscopic_derivation
    (h k l : UnlabeledOrientationHistory) :
    refinementDilation * endpointPairKet
        (unlabeledEndpoint (ordinalCausalRefinement.descend h k))
        (unlabeledEndpoint l) =
      recordedOutputKet
        (orientationGrowthKet (associatorFinalHistory h k l))
        (endpointPairRecord
          (unlabeledEndpoint (ordinalCausalRefinement.descend h k))
          (unlabeledEndpoint l)) := by
  exact refinementDilation_derives_orientationGrowthKet
    (ordinalCausalRefinement.descend h k) l

/-- **Finite quantum-growth promotion theorem.**  The two complete unlabeled
associator trajectories:

* have the same unlabeled final causal history;
* carry a Hermitian, normalized decoherence functional;
* are strongly positive on histories and on arbitrary finite route-events;
* give nonnegative quantum measure to every event and unit weight to the total;
* acquire the orientation phase from the multiplicative final sign;
* arise as output amplitudes of the explicit reversible dilation;
* reproduce exactly the extremal history kernel and CPTP refinement channel.

This closes the finite associator-sector promotion contract. -/
theorem finite_unlabeled_growth_decoherence_promotion
    (h k l : UnlabeledOrientationHistory) :
    Function.Injective (associatorTrajectory h k l)
      ∧ (∀ route : Fin 2,
      (associatorTrajectory h k l route).realize =
        associatorFinalHistory h k l)
      ∧ IsHermitianGrowthFunctional
        (associatorGrowthDecoherenceFunctional h k l).kernel
      ∧ IsNormalizedGrowthFunctional
        (associatorGrowthDecoherenceFunctional h k l).kernel
      ∧ IsStronglyPositiveGrowthFunctional
        (associatorGrowthDecoherenceFunctional h k l).kernel
      ∧ IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence
          (associatorGrowthDecoherenceFunctional h k l).kernel)
      ∧ (∀ event : Finset (Fin 2),
        0 ≤ growthQuantumMeasure
          (associatorGrowthDecoherenceFunctional h k l).kernel event)
      ∧ growthEventDecoherence
          (associatorGrowthDecoherenceFunctional h k l).kernel
          Finset.univ Finset.univ = 1
      ∧ unlabeledOrientationSign (associatorFinalHistory h k l) =
        unlabeledOrientationSign h * unlabeledOrientationSign k *
          unlabeledOrientationSign l
      ∧ refinementDilation * endpointPairKet
          (unlabeledEndpoint (ordinalCausalRefinement.descend h k))
          (unlabeledEndpoint l) =
        recordedOutputKet
          (orientationGrowthKet (associatorFinalHistory h k l))
          (endpointPairRecord
            (unlabeledEndpoint (ordinalCausalRefinement.descend h k))
            (unlabeledEndpoint l))
      ∧ (fun p q =>
        (associatorGrowthDecoherenceFunctional h k l).kernel p q) =
          unlabeledHistoryKernel (associatorFinalHistory h k l)
      ∧ (fun p q =>
        (associatorGrowthDecoherenceFunctional h k l).kernel p q) =
          orientationRefinementKraus.apply
            (historyKernelTensor
              (unlabeledHistoryKernel
                (ordinalCausalRefinement.descend h k))
              (unlabeledHistoryKernel l)) := by
  exact ⟨associatorTrajectory_injective h k l,
    associatorTrajectory_realize h k l,
    (associatorGrowthDecoherenceFunctional h k l).hermitian,
    (associatorGrowthDecoherenceFunctional h k l).normalized,
    (associatorGrowthDecoherenceFunctional h k l).stronglyPositive,
    orientationGrowthEventDecoherence_stronglyPositive _,
    orientationGrowthQuantumMeasure_nonneg _,
    orientationGrowthTotalEvent_normalized _,
    associatorFinalHistory_sign h k l,
    associatorGrowthAmplitude_microscopic_derivation h k l,
    associatorGrowthDecoherence_restriction h k l,
    associatorGrowthDecoherence_derives_refinementChannel h k l⟩

#print axioms CompleteUnlabeledGrowthTrajectory.realize_refine_sign
#print axioms associatorTrajectory_realize
#print axioms amplitudeDecoherence_stronglyPositive
#print axioms amplitude_growthEventDecoherence_stronglyPositive
#print axioms amplitude_growthEventDecoherence_hermitian
#print axioms refinementDilation_derives_orientationGrowthKet
#print axioms orientationGrowthDecoherence_eq_unlabeledHistoryKernel
#print axioms orientationGrowthDecoherence_normalized
#print axioms orientationGrowthEventDecoherence_stronglyPositive
#print axioms orientationGrowthEventDecoherence_hermitian
#print axioms orientationGrowthQuantumMeasure_gradeTwo
#print axioms associatorGrowthDecoherence_derives_refinementChannel
#print axioms associatorGrowthAmplitude_microscopic_derivation
#print axioms finite_unlabeled_growth_decoherence_promotion

end

end UnifiedTheory.Audit.KFOrientationGrowthDecoherence

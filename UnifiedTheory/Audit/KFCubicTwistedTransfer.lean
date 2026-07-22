/-
  Audit/KFCubicTwistedTransfer.lean

  ABSTRACT TWISTED TRANSFER BRIDGE FOR THE THREE-SHEET CARRIER

  This file isolates the exact junction between causal transition data and the
  intrinsic rank-two sheet carrier.  A transition system supplies:

  * a finite outgoing edge type at each state;
  * a complex scalar weight on every edge;
  * a three-sheet fiber at every state;
  * a sheet bijection from the child fiber back to the parent fiber.

  These data define a carrier-valued twisted transfer operator.  A nonzero
  eigen-section automatically satisfies the normalized atomic fiber-sum law,
  and hence supplies a normalized strongly positive one-step event kernel.
  Fiberwise sheet relabelings conjugate the transfer operator and leave the
  induced Gram kernel unchanged.

  This is an interface theorem, not a causal dynamics.  In particular, it
  does not derive the three-sheet fibers, their S3-valued edge transports, the
  complex edge weights, or an eigen-section from causal growth.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCubicSheetFrameRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCubicTwistedTransfer

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCubicSheetIntrinsicCarrier

universe u v w x

/-! ## 1. State-dependent sheet transport -/

/-- Finite causal-transition data twisted by a sheet local system.  The sheet
transport is contravariant because a refined child amplitude is pulled back
to the parent carrier before outgoing alternatives are summed. -/
structure TwistedSheetTransferData
    (State : Type u) (Sheet : State → Type v) (Edge : State → Type w)
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)] where
  target : ∀ state, Edge state → State
  weight : ∀ state, Edge state → ℂ
  sheetTransport : ∀ state (edge : Edge state),
    Sheet (target state edge) ≃ Sheet state

/-- A section of the state-dependent intrinsic carrier bundle. -/
abbrev CarrierSection {State : Type u} (Sheet : State → Type v)
    [∀ state, Fintype (Sheet state)] :=
  ∀ state, ZeroSumCarrier (Sheet state)

/-- Transport respects composition of sheet bijections. -/
theorem transportZeroSumCarrier_trans
    {First : Type u} {Second : Type v} {Third : Type w}
    [Fintype First] [Fintype Second] [Fintype Third]
    (first : First ≃ Second) (second : Second ≃ Third)
    (state : ZeroSumCarrier First) :
    transportZeroSumCarrier second
        (transportZeroSumCarrier first state) =
      transportZeroSumCarrier (first.trans second) state := by
  apply Subtype.ext
  funext coordinate
  rfl

@[simp]
theorem transportZeroSumCarrier_refl
    {S : Type u} [Fintype S] (state : ZeroSumCarrier S) :
    transportZeroSumCarrier (Equiv.refl S) state = state := by
  apply Subtype.ext
  funext coordinate
  rfl

/-- Conjugating an edge relabeling by coordinate gauges commutes with carrier
transport. -/
theorem transportZeroSumCarrier_gauge_conjugate
    {Child : Type u} {Parent : Type v}
    {GaugeChild : Type w} {GaugeParent : Type x}
    [Fintype Child] [Fintype Parent]
    [Fintype GaugeChild] [Fintype GaugeParent]
    (edgeTransport : Child ≃ Parent)
    (childGauge : Child ≃ GaugeChild)
    (parentGauge : Parent ≃ GaugeParent)
    (state : ZeroSumCarrier Child) :
    transportZeroSumCarrier
        ((childGauge.symm.trans edgeTransport).trans parentGauge)
        (transportZeroSumCarrier childGauge state) =
      transportZeroSumCarrier parentGauge
        (transportZeroSumCarrier edgeTransport state) := by
  apply Subtype.ext
  funext coordinate
  simp [transportZeroSumCarrier]

/-! ## 2. The twisted transfer and its eigen-section law -/

/-- Carrier-valued transfer operator obtained by weighting and pulling every
child section value into the parent sheet fiber. -/
def twistedSheetTransfer
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (state : State) :
    ZeroSumCarrier (Sheet state) :=
  ∑ edge : Edge state, law.weight state edge •
    transportZeroSumCarrier (law.sheetTransport state edge)
      (field (law.target state edge))

/-- Eigen-section equation for the twisted transfer operator. -/
def IsTwistedTransferEigenSection
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ) : Prop :=
  ∀ state, twistedSheetTransfer law field state = eigenvalue • field state

/-- Contribution of one child branch after division by a nonzero transfer
eigenvalue. -/
def normalizedTwistedBranchAmplitude
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (state : State) (edge : Edge state) : ZeroSumCarrier (Sheet state) :=
  (eigenvalue⁻¹ * law.weight state edge) •
    transportZeroSumCarrier (law.sheetTransport state edge)
      (field (law.target state edge))

/-- **Transfer-to-projectivity bridge.**  The eigen-section equation is
exactly the transported atomic fiber-sum law after division by the nonzero
eigenvalue. -/
theorem eigenSection_sum_normalizedTwistedBranchAmplitude
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection law field eigenvalue)
    (hEigenvalue : eigenvalue ≠ 0) (state : State) :
    ∑ edge : Edge state,
      normalizedTwistedBranchAmplitude law field eigenvalue state edge =
        field state := by
  unfold normalizedTwistedBranchAmplitude
  calc
    (∑ edge : Edge state,
        (eigenvalue⁻¹ * law.weight state edge) •
          transportZeroSumCarrier (law.sheetTransport state edge)
            (field (law.target state edge))) =
        eigenvalue⁻¹ • twistedSheetTransfer law field state := by
      change (∑ edge : Edge state,
        (eigenvalue⁻¹ * law.weight state edge) •
          transportZeroSumCarrier (law.sheetTransport state edge)
            (field (law.target state edge))) =
        eigenvalue⁻¹ • (∑ edge : Edge state, law.weight state edge •
          transportZeroSumCarrier (law.sheetTransport state edge)
            (field (law.target state edge)))
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro edge _hEdge
      rw [smul_smul]
    _ = eigenvalue⁻¹ • (eigenvalue • field state) := by
      rw [hEigen state]
    _ = field state := by
      rw [smul_smul, inv_mul_cancel₀ hEigenvalue, one_smul]

/-- Exhaustive carrier amplitude after a fixed number of future refinement
steps.  This recursively sums all branch amplitudes without choosing a global
sheet marking. -/
def iteratedNormalizedTwistedBranchSum
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ) :
    ℕ → ∀ state, ZeroSumCarrier (Sheet state)
  | 0, state => field state
  | depth + 1, state =>
      ∑ edge : Edge state, (eigenvalue⁻¹ * law.weight state edge) •
        transportZeroSumCarrier (law.sheetTransport state edge)
          (iteratedNormalizedTwistedBranchSum law field eigenvalue depth
            (law.target state edge))

/-- The eigen-section equation gives exact exhaustive consistency at every
finite refinement depth, not only one step. -/
theorem eigenSection_iteratedBranchSum_eq_field
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection law field eigenvalue)
    (hEigenvalue : eigenvalue ≠ 0) :
    ∀ depth state,
      iteratedNormalizedTwistedBranchSum law field eigenvalue depth state =
        field state := by
  intro depth
  induction depth with
  | zero => intro state; rfl
  | succ depth ih =>
      intro state
      unfold iteratedNormalizedTwistedBranchSum
      simp_rw [ih]
      exact eigenSection_sum_normalizedTwistedBranchAmplitude
        law field eigenvalue hEigen hEigenvalue state

/-! ## 3. The induced one-step decoherence functional -/

/-- Coordinate representative of the transported branch amplitude in the
parent sheet fiber. -/
def normalizedTwistedBranchCoordinates
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (state : State) : Edge state → Sheet state → ℂ :=
  fun edge =>
    (normalizedTwistedBranchAmplitude law field eigenvalue state edge).1

theorem normalizedTwistedBranchEventAmplitude_univ
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection law field eigenvalue)
    (hEigenvalue : eigenvalue ≠ 0) (state : State) :
    vectorEventAmplitude
        (normalizedTwistedBranchCoordinates law field eigenvalue state)
        Finset.univ = (field state).1 := by
  classical
  funext coordinate
  have hSum := congrArg
    (fun value : ZeroSumCarrier (Sheet state) => value.1 coordinate)
    (eigenSection_sum_normalizedTwistedBranchAmplitude
      law field eigenvalue hEigen hEigenvalue state)
  simpa [vectorEventAmplitude, normalizedTwistedBranchCoordinates,
    Finset.sum_apply] using hSum

/-- Every twisted eigen-section produces a Hermitian, strongly positive
one-step kernel on outgoing causal branches. -/
theorem normalizedTwistedBranchKernel_hermitian_stronglyPositive
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ) (state : State) :
    IsHermitianGrowthFunctional
        (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates law field eigenvalue state))
      ∧ IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates law field eigenvalue state))) := by
  exact ⟨vectorAmplitudeKernel_hermitian _,
    vectorEventDecoherence_stronglyPositive _⟩

/-- Unit norm of the parent eigen-section value normalizes the outgoing branch
decoherence functional. -/
theorem normalizedTwistedBranchKernel_normalized
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection law field eigenvalue)
    (hEigenvalue : eigenvalue ≠ 0) (state : State)
    (hUnit : zeroSumCarrierInner (field state) (field state) = 1) :
    IsNormalizedGrowthFunctional
      (vectorAmplitudeKernel
        (normalizedTwistedBranchCoordinates law field eigenvalue state)) := by
  classical
  rw [vectorAmplitudeKernel_normalized_iff]
  rw [normalizedTwistedBranchEventAmplitude_univ
    law field eigenvalue hEigen hEigenvalue state]
  exact hUnit

/-! ## 4. Gauge covariance under fiberwise sheet relabeling -/

/-- Conjugate all edge transports by an arbitrary relabeling of every sheet
fiber. -/
def gaugeConjugateTwistedSheetTransfer
    {State : Type u} {Sheet : State → Type v}
    {GaugeSheet : State → Type w} {Edge : State → Type u}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (GaugeSheet state)]
    [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (gauge : ∀ state, Sheet state ≃ GaugeSheet state) :
    TwistedSheetTransferData State GaugeSheet Edge where
  target := law.target
  weight := law.weight
  sheetTransport state edge :=
    ((gauge (law.target state edge)).symm.trans
      (law.sheetTransport state edge)).trans (gauge state)

/-- Gauge-transform a carrier section. -/
def gaugeCarrierSection
    {State : Type u} {Sheet : State → Type v}
    {GaugeSheet : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (GaugeSheet state)]
    (gauge : ∀ state, Sheet state ≃ GaugeSheet state)
    (field : CarrierSection Sheet) : CarrierSection GaugeSheet :=
  fun state => transportZeroSumCarrier (gauge state) (field state)

/-- The twisted transfer is gauge-covariant: fiber relabeling conjugates the
operator rather than changing its intrinsic action. -/
theorem twistedSheetTransfer_gauge_covariant
    {State : Type u} {Sheet : State → Type v}
    {GaugeSheet : State → Type w} {Edge : State → Type u}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (GaugeSheet state)]
    [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (gauge : ∀ state, Sheet state ≃ GaugeSheet state)
    (field : CarrierSection Sheet) (state : State) :
    twistedSheetTransfer (gaugeConjugateTwistedSheetTransfer law gauge)
        (gaugeCarrierSection gauge field) state =
      transportZeroSumCarrier (gauge state)
        (twistedSheetTransfer law field state) := by
  unfold twistedSheetTransfer gaugeConjugateTwistedSheetTransfer
    gaugeCarrierSection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro edge _hEdge
  rw [map_smul]
  congr 1
  exact transportZeroSumCarrier_gauge_conjugate
    (law.sheetTransport state edge)
    (gauge (law.target state edge)) (gauge state)
    (field (law.target state edge))

/-- Gauge conjugation carries every eigen-section to an eigen-section with the
same eigenvalue. -/
theorem eigenSection_gauge_covariant
    {State : Type u} {Sheet : State → Type v}
    {GaugeSheet : State → Type w} {Edge : State → Type u}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (GaugeSheet state)]
    [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (gauge : ∀ state, Sheet state ≃ GaugeSheet state)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection law field eigenvalue) :
    IsTwistedTransferEigenSection
      (gaugeConjugateTwistedSheetTransfer law gauge)
      (gaugeCarrierSection gauge field) eigenvalue := by
  intro state
  rw [twistedSheetTransfer_gauge_covariant, hEigen state]
  exact (transportZeroSumCarrier (gauge state)).map_smul eigenvalue (field state)

/-- Branch amplitudes themselves transform equivariantly. -/
theorem normalizedTwistedBranchAmplitude_gauge
    {State : Type u} {Sheet : State → Type v}
    {GaugeSheet : State → Type w} {Edge : State → Type u}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (GaugeSheet state)]
    [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (gauge : ∀ state, Sheet state ≃ GaugeSheet state)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (state : State) (edge : Edge state) :
    normalizedTwistedBranchAmplitude
        (gaugeConjugateTwistedSheetTransfer law gauge)
        (gaugeCarrierSection gauge field) eigenvalue state edge =
      transportZeroSumCarrier (gauge state)
        (normalizedTwistedBranchAmplitude law field eigenvalue state edge) := by
  unfold normalizedTwistedBranchAmplitude gaugeConjugateTwistedSheetTransfer
    gaugeCarrierSection
  rw [map_smul]
  congr 1
  exact transportZeroSumCarrier_gauge_conjugate
    (law.sheetTransport state edge)
    (gauge (law.target state edge)) (gauge state)
    (field (law.target state edge))

/-- The one-step branch Gram kernel is independent of every local sheet
coordinate choice. -/
theorem normalizedTwistedBranchKernel_gauge_invariant
    {State : Type u} {Sheet : State → Type v}
    {GaugeSheet : State → Type w} {Edge : State → Type u}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (GaugeSheet state)]
    [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (gauge : ∀ state, Sheet state ≃ GaugeSheet state)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (state : State) (first second : Edge state) :
    vectorAmplitudeKernel
        (normalizedTwistedBranchCoordinates
          (gaugeConjugateTwistedSheetTransfer law gauge)
          (gaugeCarrierSection gauge field) eigenvalue state) first second =
      vectorAmplitudeKernel
        (normalizedTwistedBranchCoordinates law field eigenvalue state)
        first second := by
  unfold vectorAmplitudeKernel finiteVectorInner
    normalizedTwistedBranchCoordinates
  rw [normalizedTwistedBranchAmplitude_gauge,
    normalizedTwistedBranchAmplitude_gauge]
  exact zeroSumCarrierInner_transport (gauge state) _ _

/-! ## 5. Capstone and honest frontier -/

/-- At any parent whose eigen-section vector has unit norm, the twisted
transfer construction yields a normalized Hermitian strongly positive branch
functional, and this functional is invariant under sheet gauge relabeling. -/
theorem twistedTransferEigenSection_induces_branchQuantumFunctional
    {State : Type u} {Sheet : State → Type v} {Edge : State → Type w}
    [∀ state, Fintype (Sheet state)] [∀ state, Fintype (Edge state)]
    (law : TwistedSheetTransferData State Sheet Edge)
    (field : CarrierSection Sheet) (eigenvalue : ℂ)
    (hEigen : IsTwistedTransferEigenSection law field eigenvalue)
    (hEigenvalue : eigenvalue ≠ 0) (state : State)
    (hUnit : zeroSumCarrierInner (field state) (field state) = 1) :
    IsHermitianGrowthFunctional
        (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates law field eigenvalue state))
      ∧ IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates law field eigenvalue state)))
      ∧ IsNormalizedGrowthFunctional
        (vectorAmplitudeKernel
          (normalizedTwistedBranchCoordinates law field eigenvalue state)) := by
  classical
  exact ⟨(normalizedTwistedBranchKernel_hermitian_stronglyPositive
      law field eigenvalue state).1,
    (normalizedTwistedBranchKernel_hermitian_stronglyPositive
      law field eigenvalue state).2,
    normalizedTwistedBranchKernel_normalized law field eigenvalue
      hEigen hEigenvalue state hUnit⟩

#print axioms eigenSection_sum_normalizedTwistedBranchAmplitude
#print axioms eigenSection_iteratedBranchSum_eq_field
#print axioms normalizedTwistedBranchKernel_normalized
#print axioms twistedSheetTransfer_gauge_covariant
#print axioms normalizedTwistedBranchKernel_gauge_invariant
#print axioms twistedTransferEigenSection_induces_branchQuantumFunctional

end

end UnifiedTheory.Audit.KFCubicTwistedTransfer

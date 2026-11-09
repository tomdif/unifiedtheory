/- The physical meaning of the form derivative's range condition: it is
exactly the domain of the already constructed growing Hamiltonian.  This
does not assert that the full nonautonomous propagator preserves that domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge
import UnifiedTheory.Audit.KFCausalMassFormOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingDerivativeDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity (growingMap referenceFormDerivative)
open KFCausalBoundedFormCurve (gram)

private theorem gram_pairing_iff
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (B : X →L[ℂ] Z) (u : X) (y : Y) :
    (∀ v : X, inner ℂ (B u) (B v)=inner ℂ y (J v)) ↔ gram B u=J.adjoint y := by
  constructor
  · intro hp
    apply ext_inner_right ℂ
    intro v
    change inner ℂ (B.adjoint (B u)) v=inner ℂ (J.adjoint y) v
    rw [B.adjoint_inner_left,J.adjoint_inner_left]
    exact hp v
  · intro he v
    have hi := congrArg (fun z => inner ℂ z v) he
    change inner ℂ (B.adjoint (B u)) v=inner ℂ (J.adjoint y) v at hi
    simpa only [ContinuousLinearMap.adjoint_inner_left] using hi

private theorem scaled_adjoint_iff
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (J : X →L[ℂ] Y) (A : X →L[ℂ] X) (c : ℝ) (hc : c ≠ 0) (u : X) (y : Y) :
    c • A u=J.adjoint y ↔ A u=J.adjoint (c⁻¹ • y) := by
  rw [ContinuousLinearMap.map_smul_of_tower]
  constructor
  · intro he
    have hi := congrArg (fun z : X => c⁻¹ • z) he
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi
  · intro he
    rw [he,smul_smul,mul_inv_cancel₀ hc,one_smul]

private theorem scaled_range_iff
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (J : X →L[ℂ] Y) (A : X →L[ℂ] X) (T : Y →ₗ.[ℂ] Y)
    (c : ℝ) (hc : c ≠ 0) (u : X)
    (hgraph : ∀ y : Y, c • A u=J.adjoint y ↔ (J u,c⁻¹ • y) ∈ T.graph) :
    c • A u ∈ Set.range J.adjoint ↔ J u ∈ T.domain := by
  constructor
  · rintro ⟨y,hy⟩
    exact LinearPMap.mem_domain_of_mem_graph ((hgraph y).mp hy.symm)
  · intro hu
    refine ⟨c • T ⟨J u,hu⟩,?_⟩
    apply Eq.symm
    apply (hgraph _).mpr
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using T.mem_graph ⟨J u,hu⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V" => FormSpace ε hε h hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε h hh hb mass2 quartic vacuum 0
local notation "B" => growingMap ε hε h hh hb mass2 quartic vacuum
local notation "D" => referenceFormDerivative ε hε h hh hb mass2 quartic vacuum
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb mass2 quartic vacuum

theorem growing_graph_adjoint (u : V) (y : Hilbert) :
    (J u,y) ∈ (G).graph ↔ gram B u=(J).adjoint y :=
  (KFCausalMassFormOperator.graph_domain_iff G (J u) y).trans
    ((KFCausalClockFloorGrowingHamiltonian.reference_domain_characterization
      ε hε h hh hb mass2 quartic vacuum u y).trans (gram_pairing_iff J B u y))

theorem derivative_graph_iff (t : ℝ) (u : V) (y : Hilbert) :
    D t u=(J).adjoint y ↔
      (J u,(2*Real.exp (2*t))⁻¹ • y) ∈ (G).graph :=
  (scaled_adjoint_iff J (gram B) (2*Real.exp (2*t)) (ne_of_gt (by positivity)) u y).trans
    (growing_graph_adjoint ε hε h hh hb mass2 quartic vacuum u
      ((2*Real.exp (2*t))⁻¹ • y)).symm

theorem derivative_range_iff (t : ℝ) (u : V) :
    D t u ∈ Set.range (J).adjoint ↔ J u ∈ (G).domain :=
  scaled_range_iff J (gram B) G (2*Real.exp (2*t)) (ne_of_gt (by positivity)) u
    (derivative_graph_iff ε hε h hh hb mass2 quartic vacuum t u)

#print axioms growing_graph_adjoint
#print axioms derivative_graph_iff
#print axioms derivative_range_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingDerivativeDomain

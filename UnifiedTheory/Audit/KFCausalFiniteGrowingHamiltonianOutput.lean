/- The actual growing self-adjoint Hamiltonian acts on every original
finite sourced state.  Its output is one half of the already constructed
physical time derivative at zero, and lies in every full Hamiltonian domain.
This identifies initial vectors, not preservation by the full propagator. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingDerivativeDomain
import UnifiedTheory.Audit.KFCausalFiniteHamiltonianTimeDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteGrowingHamiltonianOutput
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalFiniteHamiltonianSquare (firstOutput)
open KFCausalFiniteHamiltonianTimeDerivative (outputDerivative)

private theorem differentiate_pairing
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (J : X →L[ℂ] Y) (u : X) (Q : ℝ → X →L[ℂ] X) (F : ℝ → Y)
    (s : ℝ) (D : X →L[ℂ] X) (y : Y)
    (hQ : HasDerivAt Q D s) (hF : HasDerivAt F y s)
    (hp : ∀ t v, inner ℂ u (Q t v)=inner ℂ (F t) (J v)) (v : X) :
    inner ℂ u (D v)=inner ℂ y (J v) := by
  have hv : HasDerivAt (fun t => Q t v) (D v) s :=
    ((ContinuousLinearMap.apply ℂ X v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hQ
  have hl := (hasDerivAt_const s u).inner ℂ hv
  have hr := hF.inner ℂ (hasDerivAt_const s (J v))
  have he : (fun t => inner ℂ u (Q t v)) = fun t => inner ℂ (F t) (J v) :=
    funext (fun t => hp t v)
  simp only [add_zero,inner_zero_left,inner_zero_right,zero_add] at hl hr
  rw [he] at hl
  exact hl.unique hr

private theorem scaled_gram_adjoint
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (B : X →L[ℂ] Z) (c : ℝ) (u : X) (y : Y)
    (hp : ∀ v, inner ℂ u (c • B.adjoint (B v))=inner ℂ y (J v)) :
    c • B.adjoint (B u)=J.adjoint y := by
  apply ext_inner_right ℂ
  intro v
  rw [J.adjoint_inner_left]
  calc
    inner ℂ (c • B.adjoint (B u)) v = inner ℂ u (c • B.adjoint (B v)) := by
      rw [inner_smul_left_eq_smul,inner_smul_right_eq_smul,
        B.adjoint_inner_left,B.adjoint_inner_right]
    _ = _ := hp v

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum : ℝ)
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "F" => firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "F'" => outputDerivative n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum
local notation "V" => FormSpace ε hε h hh hb₀ mass2 quartic vacuum 0
local notation "J" => embedding ε hε h hh hb₀ mass2 quartic vacuum 0
local notation "Q" => referenceFormOperator ε hε h hh hb₀ mass2 quartic vacuum
local notation "D" => referenceFormDerivative ε hε h hh hb₀ mass2 quartic vacuum
local notation "B" => growingMap ε hε h hh hb₀ mass2 quartic vacuum

def referenceVector : V :=
  KFCausalClockFloorAveragedHamiltonianBridge.referenceLift
    ε hε h hh hb₀ mass2 quartic vacuum 0
    ⟨ψ,LinearPMap.mem_domain_of_mem_graph
      (KFCausalFiniteHamiltonianSquare.first_graph
        n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum 0)⟩

local notation "v₀" => referenceVector n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum

theorem referenceVector_embedding : J v₀=ψ :=
  KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift
    ε hε h hh hb₀ mass2 quartic vacuum 0 _

theorem output_pairing (s : ℝ) (v : V) :
    inner ℂ v₀ (Q s v)=inner ℂ (F s) (J v) := by
  apply (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain
    ε hε h hh hb₀ mass2 quartic vacuum s v₀ (F s)).mp ?_ v
  apply (KFCausalMassFormOperator.graph_domain_iff (H s) _ _).mp
  rw [referenceVector_embedding]
  exact KFCausalFiniteHamiltonianSquare.first_graph
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s

private theorem derivative_pairing (s : ℝ) (v : V) :
    inner ℂ v₀ (D s v)=inner ℂ (F' s) (J v) :=
  differentiate_pairing J v₀ Q F s (D s) (F' s)
    (referenceForm_derivative ε hε h hh hb₀ mass2 quartic vacuum s)
    (KFCausalFiniteHamiltonianTimeDerivative.output_derivative
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s)
    (output_pairing n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum) v

theorem derivative_adjoint (s : ℝ) : D s v₀=(J).adjoint (F' s) :=
  scaled_gram_adjoint J B (2*Real.exp (2*s)) v₀ (F' s)
    (derivative_pairing n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s)

def growingOutput : Hilbert := (2:ℝ)⁻¹ • F' 0

theorem growing_graph :
    (ψ,growingOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum) ∈ (G).graph := by
  have hg := (KFCausalClockFloorGrowingDerivativeDomain.derivative_graph_iff
    ε hε h hh hb₀ mass2 quartic vacuum 0 v₀ (F' 0)).mp
      (derivative_adjoint n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum 0)
  simpa only [growingOutput,mul_zero,Real.exp_zero,mul_one,referenceVector_embedding] using hg

theorem growing_domain : ψ ∈ (G).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (growing_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)

theorem growing_output_domain (s : ℝ) :
    growingOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum ∈ (H s).domain :=
  ((H s).domain.restrictScalars ℝ).smul_mem _
    (KFCausalFiniteHamiltonianTimeDerivative.derivative_cross_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum 0 s)

#print axioms referenceVector_embedding
#print axioms output_pairing
#print axioms derivative_adjoint
#print axioms growing_graph
#print axioms growing_domain
#print axioms growing_output_domain
end
end UnifiedTheory.Audit.KFCausalFiniteGrowingHamiltonianOutput

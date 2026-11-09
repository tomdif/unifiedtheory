/- The full regulated propagator has its strong initial Schrodinger
 derivative on exactly the actual Hamiltonian domain. Domain propagation
 along a trajectory is a separate obligation. -/
import UnifiedTheory.Audit.KFCausalFormDomainInitialDerivative
import UnifiedTheory.Audit.KFCausalClockFloorGeneratorIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorDomainSchrodinger
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry (embedding_dense)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge
open UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative (mass_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorGeneratorIdentification

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem form_initial (s : ℝ) (w : V) (z : Hilbert)
    (hw : ∀ y, inner ℂ w (Q s y) = inner ℂ z (J y)) :
    HasDerivAt (fun t => U s t (J w)) (c • z) s := by
  have hd := KFCausalFormDomainInitialDerivative.initial_derivative
    («V» := V) («H» := Hilbert) (G := KFCausalAveragedOutputRescaling.EnergyOutputSpace)
    J (embedding_dense ε hε h hne hh m g k 0)
    (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k)
    (1/h) s (fun t => F s t w) z
    (formFlow_continuous ε hε h hne hh m g k s w)
    (fun t => (formFlow_physical_norm ε hε h hne hh m g k s t w).trans
      (formFlow_physical_norm ε hε h hne hh m g k s s w).symm)
    (fun t => mass_derivative ε hε h hne hh m g k s t w)
    (fun y => (congrArg (fun v : V => inner ℂ v (Q s y))
      (formFlow_initial ε hε h hne hh m g k s w)).trans (hw y))
  have he : (fun t => U s t (J w)) = fun t => J (F s t w) :=
    funext (fun t => evolution_embedding ε hε h hne hh m g k s t w)
  exact (congrArg (fun f : ℝ → Hilbert => HasDerivAt f (c • z) s) he).mpr hd

theorem hamiltonian_initial (s : ℝ) (x : (H s).domain) :
    HasDerivAt (fun t => U s t (x:Hilbert)) (c • H s x) s := by
  have hd := form_initial ε hε h hne hh m g k s
    (referenceLift ε hε h hne hh m g k s x) (H s x)
    (hamiltonian_reference_pairing ε hε h hne hh m g k s x)
  exact (congrArg (fun f : Hilbert => HasDerivAt (fun t => U s t f) (c • H s x) s)
    (embedding_referenceLift ε hε h hne hh m g k s x)).mp hd

theorem initial_generator_graph_eq (s : ℝ) :
    generatorGraph ε hε h hne hh m g k s = ((H s).graph : Set (Hilbert × Hilbert)) := by
  apply Subset.antisymm (initial_derivative_graph_subset ε hε h hne hh m g k s)
  intro p hp
  obtain ⟨x,rfl⟩ := ((H s).mem_graph_iff').mp hp
  exact hamiltonian_initial ε hε h hne hh m g k s x

theorem initial_derivative_iff (s : ℝ) (f z : Hilbert) :
    HasDerivAt (fun t => U s t f) (c • z) s ↔
      ∃ hf : f ∈ (H s).domain, H s ⟨f,hf⟩ = z := by
  change (f,z) ∈ generatorGraph ε hε h hne hh m g k s ↔ _
  rw [initial_generator_graph_eq]
  constructor
  · intro hp
    obtain ⟨x,hx,hz⟩ := ((H s).mem_graph_iff).mp hp
    change (x:Hilbert) = f at hx
    change H s x = z at hz
    subst f
    exact ⟨x.property,hz⟩
  · rintro ⟨hf,hz⟩
    exact ((H s).mem_graph_iff).mpr ⟨⟨f,hf⟩,rfl,hz⟩

theorem initial_differentiable_iff (s : ℝ) (f : Hilbert) :
    DifferentiableAt ℝ (fun t => U s t f) s ↔ f ∈ (H s).domain := by
  constructor
  · intro hf
    have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hne))
    have hd : HasDerivAt (fun t => U s t f)
        (c • (c⁻¹ • deriv (fun t => U s t f) s)) s := by
      simpa only [smul_smul,mul_inv_cancel₀ hc,one_smul] using hf.hasDerivAt
    exact ((initial_derivative_iff ε hε h hne hh m g k s f _).mp hd).choose
  · intro hf
    exact (hamiltonian_initial ε hε h hne hh m g k s ⟨f,hf⟩).differentiableAt

#print axioms form_initial
#print axioms hamiltonian_initial
#print axioms initial_generator_graph_eq
#print axioms initial_derivative_iff
#print axioms initial_differentiable_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorDomainSchrodinger

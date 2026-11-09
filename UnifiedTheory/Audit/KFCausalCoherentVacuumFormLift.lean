/- The actual averaged vacuum graph form contains both f and B f for
every coherent-span f. Its cross pairing has the proved nonnegative
weak-response sign. This is the vacuum factor only: no full Hamiltonian
form-domain invariance or Ehrenfest time identity is asserted. -/
import UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionL2
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentVacuumFormLift
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan coherentSpan_dense)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action group action_strong_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbit orbitState_coe)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "T" => orderedExponential ε hε h

include hh hb in
theorem ordered_domain_dense : Dense ((T).domain : Set Hilbert) := by
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε 1 h hε zero_lt_one hh)
  have he : coherentSpan ε 1 h hε zero_lt_one hh ≤ (T).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨k,rfl⟩
    exact KFCausalClockFloorCoherentSpectral.state_ordered_domain ε 1 h hε zero_lt_one hh hb k
  exact hd.mono he

def formData : KFCausalClosedGraphForm.Data Hilbert Hilbert where
  operator := T
  closed := KFCausalClockFloorBoundedInverse.orderedExponential_closed ε hε h
  dense := ordered_domain_dense ε h hε hh hb

local notation "D" => formData ε h hε hh hb
local notation "Base" => KFCausalClosedGraphForm.FormSpace D
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "A" => KFCausalClosedGraphForm.energyOutput D
abbrev FormSpace := KFCausalAveragedFormSpace.FormSpace (group h hh) (2*Real.pi) J

def embedding : FormSpace ε h hε hh hb →L[ℂ] Hilbert :=
  KFCausalAveragedFormSpace.embedding (group h hh) (2*Real.pi) J
def energyOutput : FormSpace ε h hε hh hb →L[ℂ] Lp Hilbert 2 angleMeasure :=
  KFCausalAveragedFormProjection.averagedOutput (group h hh) (2*Real.pi) J A
def pairing (u v : FormSpace ε h hε hh hb) : ℂ :=
  inner ℂ (energyOutput ε h hε hh hb u) (energyOutput ε h hε hh hb v)

theorem embedding_injective : Function.Injective (embedding ε h hε hh hb) :=
  KFCausalAveragedFormSpace.embedding_injective (group h hh) (2*Real.pi) J
    (KFCausalClosedGraphForm.embedding_injective D)

def orbitVector (f : Hilbert) (g : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) (θ : ℝ) : Base :=
  ⟨WithLp.toLp 2 (action h hh (2*Real.pi*θ) f,g θ),hg θ⟩

theorem orbitVector_continuous (f : Hilbert) (g : ℝ → Hilbert) (hc : Continuous g)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) :
    Continuous (orbitVector ε h hε hh hb f g hg) := by
  apply Continuous.subtype_mk
  exact (WithLp.prod_continuous_toLp 2 Hilbert Hilbert).comp
    (((action_strong_continuous h hh f).comp (continuous_const.mul continuous_id)).prodMk hc)

def orbitLift (f : Hilbert) (g : ℝ → Hilbert) (hc : Continuous g)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) : Lp Base 2 angleMeasure :=
  (continuous_angle_memLp _ (orbitVector_continuous ε h hε hh hb f g hc hg)).toLp
    (orbitVector ε h hε hh hb f g hg)

theorem orbitLift_compatibility (f : Hilbert) (g : ℝ → Hilbert) (hc : Continuous g)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) :
    (J).compLp (orbitLift ε h hε hh hb f g hc hg) = orbit (group h hh) (2*Real.pi) f := by
  apply Lp.ext
  filter_upwards [(J).coeFn_compLp (orbitLift ε h hε hh hb f g hc hg),
    (continuous_angle_memLp _ (orbitVector_continuous ε h hε hh hb f g hc hg)).coeFn_toLp,
    orbitState_coe (group h hh) (2*Real.pi) f] with θ hJ hv ho
  change orbitLift ε h hε hh hb f g hc hg θ = _ at hv
  rw [hJ,hv]
  exact ho.symm

def lift (f : Hilbert) (g : ℝ → Hilbert) (hc : Continuous g)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) : FormSpace ε h hε hh hb :=
  ⟨WithLp.toLp 2 (f,orbitLift ε h hε hh hb f g hc hg),by
    change (J).compLp (orbitLift ε h hε hh hb f g hc hg)-orbit (group h hh) (2*Real.pi) f = 0
    exact sub_eq_zero.mpr (orbitLift_compatibility ε h hε hh hb f g hc hg)⟩

theorem lift_embedding (f : Hilbert) (g : ℝ → Hilbert) (hc : Continuous g)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) :
    embedding ε h hε hh hb (lift ε h hε hh hb f g hc hg) = f := rfl

theorem lift_output_coe (f : Hilbert) (g : ℝ → Hilbert) (hc : Continuous g)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph) :
    energyOutput ε h hε hh hb (lift ε h hε hh hb f g hc hg) =ᵐ[angleMeasure] g := by
  filter_upwards [(A).coeFn_compLp (orbitLift ε h hε hh hb f g hc hg),
    (continuous_angle_memLp _ (orbitVector_continuous ε h hε hh hb f g hc hg)).coeFn_toLp] with θ hA hv
  change orbitLift ε h hε hh hb f g hc hg θ = _ at hv
  change (A).compLp (orbitLift ε h hε hh hb f g hc hg) θ = _
  rw [hA,hv]
  rfl

theorem lift_pairing (f b : Hilbert) (g v : ℝ → Hilbert) (hc : Continuous g) (hd : Continuous v)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph)
    (hv : ∀ θ, (action h hh (2*Real.pi*θ) b,v θ) ∈ (T).graph) :
    pairing ε h hε hh hb (lift ε h hε hh hb f g hc hg) (lift ε h hε hh hb b v hd hv) =
      ∫ θ, inner ℂ (g θ) (v θ) ∂angleMeasure := by
  apply (L2.inner_def (𝕜 := ℂ) _ _).trans
  apply integral_congr_ae
  filter_upwards [lift_output_coe ε h hε hh hb f g hc hg,lift_output_coe ε h hε hh hb b v hd hv]
    with θ hθ hθ'
  exact congrArg₂ (inner ℂ) hθ hθ'

theorem coherent_momentum_lifts (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b : Hilbert) (u v : FormSpace ε h hε hh hb), (f,b) ∈ (pureMomentum ε hε h).graph ∧
      embedding ε h hε hh hb u = f ∧ embedding ε h hε hh hb v = b ∧
      0 ≤ (-2/h)*(pairing ε h hε hh hb u v).im := by
  exact (KFCausalCoherentVacuumCompositionL2.exists_actual_L2_response ε a h hε ha hh hb f hf).elim
    fun b h₁ => h₁.elim fun g h₂ => h₂.elim fun j h₃ => h₃.elim fun tb h₄ => h₄.elim fun bg hr => by
      have hB := hr.1
      have hg := hr.2.1
      have hc := hr.2.2.1.1
      have ht := hr.2.2.1.2.2.1
      have hi := hr.2.2.2.2.1
      have hpos := hr.2.2.2.2.2
      have he : (∫ θ, KFCausalCoherentVacuumWeakForce.weakResponse h g tb θ ∂angleMeasure) =
          (-2/h)*(∫ θ, inner ℂ (g θ) (tb θ) ∂angleMeasure).im :=
        (integral_const_mul (-2/h) _).trans
          (congrArg (fun r : ℝ => (-2/h)*r) (integral_im hi))
      have hp := (congrArg (fun r : ℝ => 0 ≤ r) he).mp hpos
      refine ⟨b,lift ε h hε hh hb f g hc (fun θ => (hg θ).1),
        lift ε h hε hh hb b tb ht (fun θ => (hg θ).2.2.1),hB,rfl,rfl,?_⟩
      exact (congrArg (fun z : ℂ => 0 ≤ (-2/h)*z.im)
        (lift_pairing ε h hε hh hb f b g tb hc ht (fun θ => (hg θ).1)
          (fun θ => (hg θ).2.2.1))).mpr hp

theorem actual_form_response_nonnegative (a : ℝ) (ha : 0 < a) (f b : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
    (u v : FormSpace ε h hε hh hb) (hu : embedding ε h hε hh hb u = f)
    (hv : embedding ε h hε hh hb v = b) :
    0 ≤ (-2/h)*(pairing ε h hε hh hb u v).im := by
  exact (coherent_momentum_lifts ε h hε hh hb a ha f hf).elim fun b' h₁ =>
    h₁.elim fun u' h₂ => h₂.elim fun v' hr => by
      have eb : b' = b := (pureMomentum ε hε h).mem_graph_snd_inj' hr.1 hB rfl
      have eu : u' = u := embedding_injective ε h hε hh hb (hr.2.1.trans hu.symm)
      have ev : v' = v := embedding_injective ε h hε hh hb (hr.2.2.1.trans (eb.trans hv.symm))
      exact (congrArg₂ (fun x y : FormSpace ε h hε hh hb =>
        0 ≤ (-2/h)*(pairing ε h hε hh hb x y).im) eu ev).mp hr.2.2.2

#print axioms ordered_domain_dense
#print axioms embedding_injective
#print axioms orbitVector_continuous
#print axioms orbitLift_compatibility
#print axioms lift_embedding
#print axioms lift_output_coe
#print axioms lift_pairing
#print axioms coherent_momentum_lifts
#print axioms actual_form_response_nonnegative
end
end UnifiedTheory.Audit.KFCausalCoherentVacuumFormLift

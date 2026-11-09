/- The actual full quantum propagator has its strong Schrodinger
derivative at the initial time on a derived dense resolvent family.
Invariance of the unbounded Hamiltonian domain is not assumed. -/
import UnifiedTheory.Audit.KFCausalFormInitialStrongDerivative
import UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialSchrodinger
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative (mass_derivative)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k
local notation "L" => resolventFormLift ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem form_initial (s : ℝ) (w v : V) (hw : Q s w = M v) :
    HasDerivAt (fun t => U s t (J w)) (c • J v) s := by
  have hd := KFCausalFormInitialStrongDerivative.initial_strong_derivative
    («V» := V) («H» := Hilbert) (G := KFCausalAveragedOutputRescaling.EnergyOutputSpace)
    J (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k)
    (1/h) s (fun t => F s t w) v
    (formFlow_continuous ε hε h hne hh m g k s w)
    (fun t => (formFlow_physical_norm ε hε h hne hh m g k s t w).trans
      (formFlow_physical_norm ε hε h hne hh m g k s s w).symm)
    (fun t => mass_derivative ε hε h hne hh m g k s t w)
    ((congrArg (Q s) (formFlow_initial ε hε h hne hh m g k s w)).trans hw)
  have he : (fun t => U s t (J w)) = fun t => J (F s t w) :=
    funext (fun t => evolution_embedding ε hε h hne hh m g k s t w)
  exact (congrArg (fun f : ℝ → Hilbert => HasDerivAt f (c • J v) s) he).mpr hd

theorem hamiltonian_form_identity (s : ℝ) (x : (H s).domain) (v : V)
    (hv : H s x = J v) :
    Q s (referenceLift ε hε h hne hh m g k s x) = M v := by
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (KFCausalBoundedFormCurve.formOperator
    (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) s
    (referenceLift ε hε h hne hh m g k s x)) y = inner ℂ (M v) y
  rw [KFCausalShiftedForm.formOperator_inner_symm]
  exact (hamiltonian_reference_pairing ε hε h hne hh m g k s x y).trans
    ((congrArg (fun z : Hilbert => inner ℂ z (J y)) hv).trans
      (mass_left_pairing ε hε h hne hh m g k v y).symm)

theorem hamiltonian_initial (s : ℝ) (x : (H s).domain) (v : V)
    (hv : H s x = J v) :
    HasDerivAt (fun t => U s t (x:Hilbert)) (c • H s x) s := by
  have hd := form_initial ε hε h hne hh m g k s
    (referenceLift ε hε h hne hh m g k s x) v
    (hamiltonian_form_identity ε hε h hne hh m g k s x v hv)
  exact (congrArg₂ (fun f z : Hilbert => HasDerivAt (fun t => U s t f) (c • z) s)
    (embedding_referenceLift ε hε h hne hh m g k s x) hv.symm).mp hd

theorem double_resolvent_initial (a s : ℝ) (ha : 0 < a) (f : Hilbert) :
    HasDerivAt (fun t => U s t (R a s (R a s f)))
      (c • (R a s f-a • R a s (R a s f))) s := by
  let x := resolventVector ε hε h hne hh m g k a s ha (R a s f)
  let v : V := L a s f-a • L a s (R a s f)
  have hv : H s x = J v := by
    calc
      _ = R a s f-a • R a s (R a s f) := hamiltonian_resolvent ε hε h hne hh m g k a s ha _
      _ = J (L a s f)-a • J (L a s (R a s f)) := rfl
      _ = J v := by rw [map_sub,ContinuousLinearMap.map_smul_of_tower]
  have hd := hamiltonian_initial ε hε h hne hh m g k s x v hv
  exact hd.congr_deriv (congrArg (fun z : Hilbert => c • z)
    (hamiltonian_resolvent ε hε h hne hh m g k a s ha (R a s f)))

theorem double_resolvent_dense (a s : ℝ) (ha : 0 < a) :
    DenseRange (fun f : Hilbert => R a s (R a s f)) :=
  (shiftedResolvent_dense ε hε h hne hh m g k a s ha).comp
    (shiftedResolvent_dense ε hε h hne hh m g k a s ha) (R a s).continuous

theorem initial_schrodinger_dense (s : ℝ) :
    Dense {f : Hilbert | ∃ hf : f ∈ (H s).domain,
      HasDerivAt (fun t => U s t f) (c • H s ⟨f,hf⟩) s} := by
  apply (double_resolvent_dense ε hε h hne hh m g k 1 s (by norm_num)).mono
  rintro f ⟨q,rfl⟩
  obtain ⟨hx,hHx⟩ := shiftedResolvent_equation ε hε h hne hh m g k 1 s
    (by norm_num) (R 1 s q)
  exact ⟨hx,(double_resolvent_initial ε hε h hne hh m g k 1 s (by norm_num) q).congr_deriv
    (congrArg (fun z : Hilbert => c • z) hHx.symm)⟩

#print axioms form_initial
#print axioms hamiltonian_form_identity
#print axioms hamiltonian_initial
#print axioms double_resolvent_initial
#print axioms double_resolvent_dense
#print axioms initial_schrodinger_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorInitialSchrodinger

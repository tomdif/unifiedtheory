/- The maximal nonnegative self-adjoint OS Hamiltonian on all positive-time
Schwartz states. The unitary transport now uses only genuine Schwartz density,
so it applies to renormalized hierarchies without a bare L1 bound. -/
import UnifiedTheory.Clay.YangMills.FullSchwartzDynamics
import UnifiedTheory.Clay.YangMills.OSGeneratorDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullSchwartzHamiltonian
noncomputable section
open ContinuumControl PeriodicLattice4 KernelHilbertCompletion
open UnifiedTheory.Audit.KFCausalResolventHamiltonian
open scoped NNReal

abbrev State (W : Hierarchy) (plane : Plane)
    (hfull : FullPositiveTimeReflection.Positive W plane) :=
  Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull)

variable (W : Hierarchy) (plane : Plane)
  (hp : OSPositiveTimeKernel.Positive W plane)
  (hfull : FullPositiveTimeReflection.Positive W plane)
  (D : OSScalarDynamics.Evolution W plane hp)

/-- Exact unitary conjugation of the constructed Laplace resolvent. -/
def resolvent : State W plane hfull →L[ℂ] State W plane hfull :=
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  e.toLinearIsometry.toContinuousLinearMap.comp
    ((OSLaplaceResolvent.resolvent D).comp e.symm.toLinearIsometry.toContinuousLinearMap)

theorem resolvent_apply (x : State W plane hfull) :
    resolvent W plane hp hfull D x =
      FullSchwartzHilbert.equivalence W plane hp hfull
        (OSLaplaceResolvent.resolvent D
          ((FullSchwartzHilbert.equivalence W plane hp hfull).symm x)) := rfl

theorem resolvent_injective : Function.Injective (resolvent W plane hp hfull D) := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  intro x y hxy
  apply e.symm.injective
  apply OSLaplaceResolvent.resolvent_injective D
  have h := congrArg e.symm hxy
  change e.symm (e (OSLaplaceResolvent.resolvent D (e.symm x))) =
    e.symm (e (OSLaplaceResolvent.resolvent D (e.symm y))) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h

theorem resolvent_symmetric (x y : State W plane hfull) :
    inner ℂ (resolvent W plane hp hfull D x) y =
      inner ℂ x (resolvent W plane hp hfull D y) := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  change inner ℂ (e (OSLaplaceResolvent.resolvent D (e.symm x))) y =
    inner ℂ x (e (OSLaplaceResolvent.resolvent D (e.symm y)))
  rw [e.inner_map_eq_flip, OSLaplaceResolvent.resolvent_symmetric]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (e.inner_map_map (e.symm x) (OSLaplaceResolvent.resolvent D (e.symm y))).symm

theorem resolvent_dense : DenseRange (resolvent W plane hp hfull D) :=
  UnifiedTheory.Audit.KFCausalInverseResolventGraph.symmetric_injective_dense
    (resolvent W plane hp hfull D) (resolvent_injective W plane hp hfull D)
    (resolvent_symmetric W plane hp hfull D)

theorem resolvent_firm (x : State W plane hfull) :
    ‖resolvent W plane hp hfull D x‖^2 ≤
      (inner ℂ x (resolvent W plane hp hfull D x)).re := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  have he := e.inner_map_map (e.symm x) (OSLaplaceResolvent.resolvent D (e.symm x))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  change ‖e (OSLaplaceResolvent.resolvent D (e.symm x))‖^2 ≤
    (inner ℂ x (e (OSLaplaceResolvent.resolvent D (e.symm x)))).re
  rw [e.norm_map, he]
  exact OSLaplaceHamiltonian.resolvent_firm D (e.symm x)

/-- Inverse shift on the exact range of the transported resolvent. -/
def hamiltonian : State W plane hfull →ₗ.[ℂ] State W plane hfull :=
  inverseShift (resolvent W plane hp hfull D) (resolvent_injective W plane hp hfull D)

@[simp] theorem domain : (hamiltonian W plane hp hfull D).domain =
    (resolvent W plane hp hfull D).range := rfl

def rangePoint (x : State W plane hfull) : (hamiltonian W plane hp hfull D).domain :=
  rangeVector (resolvent W plane hp hfull D) (resolvent_injective W plane hp hfull D) x

@[simp] theorem rangePoint_value (x : State W plane hfull) :
    (rangePoint W plane hp hfull D x : State W plane hfull) =
      resolvent W plane hp hfull D x := rfl

@[simp] theorem apply_range (x : State W plane hfull) :
    hamiltonian W plane hp hfull D (rangePoint W plane hp hfull D x) =
      x-resolvent W plane hp hfull D x :=
  inverseShift_apply_range (resolvent W plane hp hfull D)
    (resolvent_injective W plane hp hfull D) x

theorem dense_domain :
    Dense ((hamiltonian W plane hp hfull D).domain : Set (State W plane hfull)) :=
  resolvent_dense W plane hp hfull D

theorem selfAdjoint : IsSelfAdjoint (hamiltonian W plane hp hfull D) :=
  inverseShift_selfAdjoint (resolvent W plane hp hfull D)
    (resolvent_injective W plane hp hfull D) (resolvent_dense W plane hp hfull D)
    (resolvent_symmetric W plane hp hfull D)

theorem closed : (hamiltonian W plane hp hfull D).IsClosed :=
  (selfAdjoint W plane hp hfull D).isClosed

theorem nonnegative (x : (hamiltonian W plane hp hfull D).domain) :
    0 ≤ (inner ℂ (x : State W plane hfull) (hamiltonian W plane hp hfull D x)).re := by
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,rfl⟩ := hx
  change 0 ≤ (inner ℂ (resolvent W plane hp hfull D y)
    (hamiltonian W plane hp hfull D (rangePoint W plane hp hfull D y))).re
  rw [apply_range, inner_sub_right, Complex.sub_re, resolvent_symmetric]
  have hs : (inner ℂ (resolvent W plane hp hfull D y)
      (resolvent W plane hp hfull D y)).re =
      ‖resolvent W plane hp hfull D y‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hs]
  exact sub_nonneg.mpr (resolvent_firm W plane hp hfull D y)

theorem graph_iff (x y : State W plane hfull) :
    (x,y) ∈ (hamiltonian W plane hp hfull D).graph ↔
      resolvent W plane hp hfull D (y+x)=x :=
  UnifiedTheory.Audit.KFCausalInverseResolventGraph.inverseShift_graph_iff
    (resolvent W plane hp hfull D) (resolvent_injective W plane hp hfull D) x y

/-- Exact graph transport, not an additional generator-identification premise. -/
theorem graph_transport (x y : State W plane hfull) :
    (x,y) ∈ (hamiltonian W plane hp hfull D).graph ↔
      ((FullSchwartzHilbert.equivalence W plane hp hfull).symm x,
        (FullSchwartzHilbert.equivalence W plane hp hfull).symm y) ∈
        (OSLaplaceHamiltonian.hamiltonian D).graph := by
  rw [graph_iff, OSLaplaceHamiltonian.graph_iff]
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  change e (OSLaplaceResolvent.resolvent D (e.symm (y+x))) = x ↔
    OSLaplaceResolvent.resolvent D (e.symm y+e.symm x) = e.symm x
  rw [← e.symm.injective.eq_iff]
  simp only [LinearIsometryEquiv.symm_apply_apply, map_add]

/-- Right derivatives of the actual transported time evolution are equivalent
under the same continuous linear isometry. -/
theorem derivative_transport (v w : State W plane hfull) :
    HasDerivWithinAt (fun t : ℝ => FullSchwartzDynamics.operator W plane hp hfull D
      t.toNNReal v) w (Set.Ici 0) 0 ↔
    HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal
      ((FullSchwartzHilbert.equivalence W plane hp hfull).symm v))
      ((FullSchwartzHilbert.equivalence W plane hp hfull).symm w) (Set.Ici 0) 0 := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  constructor
  · intro hd
    have hh := (e.symm.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivWithinAt (0 : ℝ) hd
    change HasDerivWithinAt (fun t : ℝ => e.symm (e (D.operator t.toNNReal (e.symm v))))
      (e.symm w) (Set.Ici 0) 0 at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh
  · intro hd
    have hh := (e.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivWithinAt (0 : ℝ) hd
    change HasDerivWithinAt (fun t : ℝ => e (D.operator t.toNNReal (e.symm v)))
      (e (e.symm w)) (Set.Ici 0) 0 at hh
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

/-- The transported Hamiltonian is the negative generator on its FULL right-
derivative domain for all positive-time Schwartz states. -/
theorem derivative_iff_graph (v w : State W plane hfull) :
    HasDerivWithinAt (fun t : ℝ => FullSchwartzDynamics.operator W plane hp hfull D
      t.toNNReal v) w (Set.Ici 0) 0 ↔
      (v,-w) ∈ (hamiltonian W plane hp hfull D).graph := by
  rw [derivative_transport, OSGeneratorDomain.derivative_iff_graph, graph_transport]
  simp only [map_neg]

theorem mem_domain_iff_right_derivative (v : State W plane hfull) :
    v ∈ (hamiltonian W plane hp hfull D).domain ↔
      ∃ w : State W plane hfull,
        HasDerivWithinAt (fun t : ℝ => FullSchwartzDynamics.operator W plane hp hfull D
          t.toNNReal v) w (Set.Ici 0) 0 := by
  constructor
  · intro hv
    refine ⟨-hamiltonian W plane hp hfull D ⟨v,hv⟩,?_⟩
    apply (derivative_iff_graph W plane hp hfull D v _).mpr
    exact (hamiltonian W plane hp hfull D).mem_graph_iff.mpr
      ⟨⟨v,hv⟩,rfl,by simp only [neg_neg]⟩
  · rintro ⟨w,hw⟩
    obtain ⟨x,hx,_⟩ := (hamiltonian W plane hp hfull D).mem_graph_iff.mp
      ((derivative_iff_graph W plane hp hfull D v w).mp hw)
    change (x : State W plane hfull) = v at hx
    rw [← hx]
    exact x.property

end
end UnifiedTheory.Clay.YangMills.FullSchwartzHamiltonian

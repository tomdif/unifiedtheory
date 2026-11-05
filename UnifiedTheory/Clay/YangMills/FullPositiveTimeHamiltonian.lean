/- The actual maximal OS Hamiltonian transported through the proved unitary
identification with unrestricted positive-time Schwartz states. Its exact
operator graph and maximal right-derivative domain are transported as well.
This does not identify renormalized Yang--Mills fields or prove a mass gap. -/
import UnifiedTheory.Clay.YangMills.FullPositiveTimeDynamics
import UnifiedTheory.Clay.YangMills.OSGeneratorDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullPositiveTimeHamiltonian
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
  (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B)
  (D : OSScalarDynamics.Evolution W plane hp)

/-- Exact unitary conjugation of the constructed Laplace resolvent. -/
def resolvent : State W plane hfull →L[ℂ] State W plane hfull :=
  let e := FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
  e.toLinearIsometry.toContinuousLinearMap.comp
    ((OSLaplaceResolvent.resolvent D).comp e.symm.toLinearIsometry.toContinuousLinearMap)

theorem resolvent_apply (x : State W plane hfull) :
    resolvent W plane hp hfull B hb D x =
      FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
        (OSLaplaceResolvent.resolvent D
          ((FullPositiveTimeHilbert.equivalence W plane hp hfull B hb).symm x)) := rfl

theorem resolvent_injective : Function.Injective (resolvent W plane hp hfull B hb D) := by
  let e := FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
  intro x y hxy
  apply e.symm.injective
  apply OSLaplaceResolvent.resolvent_injective D
  have h := congrArg e.symm hxy
  change e.symm (e (OSLaplaceResolvent.resolvent D (e.symm x))) =
    e.symm (e (OSLaplaceResolvent.resolvent D (e.symm y))) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h

theorem resolvent_symmetric (x y : State W plane hfull) :
    inner ℂ (resolvent W plane hp hfull B hb D x) y =
      inner ℂ x (resolvent W plane hp hfull B hb D y) := by
  let e := FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
  change inner ℂ (e (OSLaplaceResolvent.resolvent D (e.symm x))) y =
    inner ℂ x (e (OSLaplaceResolvent.resolvent D (e.symm y)))
  rw [e.inner_map_eq_flip, OSLaplaceResolvent.resolvent_symmetric]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (e.inner_map_map (e.symm x) (OSLaplaceResolvent.resolvent D (e.symm y))).symm

theorem resolvent_dense : DenseRange (resolvent W plane hp hfull B hb D) :=
  UnifiedTheory.Audit.KFCausalInverseResolventGraph.symmetric_injective_dense
    (resolvent W plane hp hfull B hb D) (resolvent_injective W plane hp hfull B hb D)
    (resolvent_symmetric W plane hp hfull B hb D)

theorem resolvent_firm (x : State W plane hfull) :
    ‖resolvent W plane hp hfull B hb D x‖^2 ≤
      (inner ℂ x (resolvent W plane hp hfull B hb D x)).re := by
  let e := FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
  have he := e.inner_map_map (e.symm x) (OSLaplaceResolvent.resolvent D (e.symm x))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  change ‖e (OSLaplaceResolvent.resolvent D (e.symm x))‖^2 ≤
    (inner ℂ x (e (OSLaplaceResolvent.resolvent D (e.symm x)))).re
  rw [e.norm_map, he]
  exact OSLaplaceHamiltonian.resolvent_firm D (e.symm x)

/-- Inverse shift on the exact range of the transported resolvent. -/
def hamiltonian : State W plane hfull →ₗ.[ℂ] State W plane hfull :=
  inverseShift (resolvent W plane hp hfull B hb D) (resolvent_injective W plane hp hfull B hb D)

@[simp] theorem domain : (hamiltonian W plane hp hfull B hb D).domain =
    (resolvent W plane hp hfull B hb D).range := rfl

def rangePoint (x : State W plane hfull) : (hamiltonian W plane hp hfull B hb D).domain :=
  rangeVector (resolvent W plane hp hfull B hb D) (resolvent_injective W plane hp hfull B hb D) x

@[simp] theorem rangePoint_value (x : State W plane hfull) :
    (rangePoint W plane hp hfull B hb D x : State W plane hfull) =
      resolvent W plane hp hfull B hb D x := rfl

@[simp] theorem apply_range (x : State W plane hfull) :
    hamiltonian W plane hp hfull B hb D (rangePoint W plane hp hfull B hb D x) =
      x-resolvent W plane hp hfull B hb D x :=
  inverseShift_apply_range (resolvent W plane hp hfull B hb D)
    (resolvent_injective W plane hp hfull B hb D) x

theorem dense_domain : Dense ((hamiltonian W plane hp hfull B hb D).domain : Set (State W plane hfull)) :=
  resolvent_dense W plane hp hfull B hb D

theorem selfAdjoint : IsSelfAdjoint (hamiltonian W plane hp hfull B hb D) :=
  inverseShift_selfAdjoint (resolvent W plane hp hfull B hb D)
    (resolvent_injective W plane hp hfull B hb D) (resolvent_dense W plane hp hfull B hb D)
    (resolvent_symmetric W plane hp hfull B hb D)

theorem closed : (hamiltonian W plane hp hfull B hb D).IsClosed :=
  (selfAdjoint W plane hp hfull B hb D).isClosed

theorem nonnegative (x : (hamiltonian W plane hp hfull B hb D).domain) :
    0 ≤ (inner ℂ (x : State W plane hfull) (hamiltonian W plane hp hfull B hb D x)).re := by
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,rfl⟩ := hx
  change 0 ≤ (inner ℂ (resolvent W plane hp hfull B hb D y)
    (hamiltonian W plane hp hfull B hb D (rangePoint W plane hp hfull B hb D y))).re
  rw [apply_range, inner_sub_right, Complex.sub_re, resolvent_symmetric]
  have hs : (inner ℂ (resolvent W plane hp hfull B hb D y)
      (resolvent W plane hp hfull B hb D y)).re =
      ‖resolvent W plane hp hfull B hb D y‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hs]
  exact sub_nonneg.mpr (resolvent_firm W plane hp hfull B hb D y)

theorem graph_iff (x y : State W plane hfull) :
    (x,y) ∈ (hamiltonian W plane hp hfull B hb D).graph ↔
      resolvent W plane hp hfull B hb D (y+x)=x :=
  UnifiedTheory.Audit.KFCausalInverseResolventGraph.inverseShift_graph_iff
    (resolvent W plane hp hfull B hb D) (resolvent_injective W plane hp hfull B hb D) x y

/-- Exact graph transport, not an additional generator-identification premise. -/
theorem graph_transport (x y : State W plane hfull) :
    (x,y) ∈ (hamiltonian W plane hp hfull B hb D).graph ↔
      ((FullPositiveTimeHilbert.equivalence W plane hp hfull B hb).symm x,
        (FullPositiveTimeHilbert.equivalence W plane hp hfull B hb).symm y) ∈
        (OSLaplaceHamiltonian.hamiltonian D).graph := by
  rw [graph_iff, OSLaplaceHamiltonian.graph_iff]
  let e := FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
  change e (OSLaplaceResolvent.resolvent D (e.symm (y+x))) = x ↔
    OSLaplaceResolvent.resolvent D (e.symm y+e.symm x) = e.symm x
  rw [← e.symm.injective.eq_iff]
  simp only [LinearIsometryEquiv.symm_apply_apply, map_add]

/-- Right derivatives of the actual transported time evolution are equivalent
under the same continuous linear isometry. -/
theorem derivative_transport (v w : State W plane hfull) :
    HasDerivWithinAt (fun t : ℝ => FullPositiveTimeDynamics.operator W plane hp hfull B hb D
      t.toNNReal v) w (Set.Ici 0) 0 ↔
    HasDerivWithinAt (fun t : ℝ => D.operator t.toNNReal
      ((FullPositiveTimeHilbert.equivalence W plane hp hfull B hb).symm v))
      ((FullPositiveTimeHilbert.equivalence W plane hp hfull B hb).symm w) (Set.Ici 0) 0 := by
  let e := FullPositiveTimeHilbert.equivalence W plane hp hfull B hb
  constructor
  · intro hd
    have hh := (e.symm.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
      (0 : ℝ) hd
    change HasDerivWithinAt (fun t : ℝ => e.symm (e (D.operator t.toNNReal (e.symm v))))
      (e.symm w) (Set.Ici 0) 0 at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh
  · intro hd
    have hh := (e.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
      (0 : ℝ) hd
    change HasDerivWithinAt (fun t : ℝ => e (D.operator t.toNNReal (e.symm v)))
      (e (e.symm w)) (Set.Ici 0) 0 at hh
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

/-- The transported Hamiltonian is the negative generator on its FULL right-
derivative domain for all positive-time Schwartz states. -/
theorem derivative_iff_graph (v w : State W plane hfull) :
    HasDerivWithinAt (fun t : ℝ => FullPositiveTimeDynamics.operator W plane hp hfull B hb D
      t.toNNReal v) w (Set.Ici 0) 0 ↔
      (v,-w) ∈ (hamiltonian W plane hp hfull B hb D).graph := by
  rw [derivative_transport, OSGeneratorDomain.derivative_iff_graph, graph_transport]
  simp only [map_neg]

theorem mem_domain_iff_right_derivative (v : State W plane hfull) :
    v ∈ (hamiltonian W plane hp hfull B hb D).domain ↔
      ∃ w : State W plane hfull,
        HasDerivWithinAt (fun t : ℝ => FullPositiveTimeDynamics.operator W plane hp hfull B hb D
          t.toNNReal v) w (Set.Ici 0) 0 := by
  constructor
  · intro hv
    refine ⟨-hamiltonian W plane hp hfull B hb D ⟨v,hv⟩,?_⟩
    apply (derivative_iff_graph W plane hp hfull B hb D v _).mpr
    exact (hamiltonian W plane hp hfull B hb D).mem_graph_iff.mpr
      ⟨⟨v,hv⟩,rfl,by simp only [neg_neg]⟩
  · rintro ⟨w,hw⟩
    obtain ⟨x,hx,_⟩ := (hamiltonian W plane hp hfull B hb D).mem_graph_iff.mp
      ((derivative_iff_graph W plane hp hfull B hb D v w).mp hw)
    change (x : State W plane hfull) = v at hx
    rw [← hx]
    exact x.property

end
end UnifiedTheory.Clay.YangMills.FullPositiveTimeHamiltonian

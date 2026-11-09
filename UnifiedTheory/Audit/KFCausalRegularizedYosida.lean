/- Concrete bounded approximations to the regularized homogeneous Hamiltonian.
Every resolvent hypothesis is discharged by its constructed inverse.
Strong convergence here is at a fixed time; convergence of evolving
states and existence of the unbounded propagator remain separate tasks. -/
import UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
import UnifiedTheory.Audit.KFCausalYosidaApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedYosida
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedHamiltonian
open UnifiedTheory.Audit.KFCausalRegularizedShiftedResolvent
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
open UnifiedTheory.Audit.KFCausalYosidaApproximation

theorem homogeneous_resolves (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    Resolves (homogeneousHamiltonian ε hε hbar coupling t)
      (shiftedResolvent ε hε hbar coupling a t) a :=
  shiftedResolvent_equation ε hε hbar coupling a t ha

theorem shiftedResolvent_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (shiftedResolvent ε hε hbar coupling a t) :=
  resolvent_selfAdjoint _ _ a (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_selfAdjoint ε hε hbar coupling t)

theorem shiftedResolvent_positive (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (f : Hilbert) : 0 ≤ (inner ℂ (shiftedResolvent ε hε hbar coupling a t f) f).re :=
  resolvent_positive _ _ a ha (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_selfAdjoint ε hε hbar coupling t) (homogeneous_positive ε hε hbar coupling t) f

theorem shiftedResolvent_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    ‖shiftedResolvent ε hε hbar coupling a t‖ ≤ a⁻¹ :=
  resolvent_norm_bound _ _ a ha (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t)

theorem shiftedResolvent_injective (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    Function.Injective (shiftedResolvent ε hε hbar coupling a t) :=
  resolvent_injective _ _ a (homogeneous_resolves ε hε hbar coupling a t ha)

theorem shiftedResolvent_dense (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    DenseRange (shiftedResolvent ε hε hbar coupling a t) :=
  resolvent_dense _ _ a (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_selfAdjoint ε hε hbar coupling t)

theorem homogeneous_approximation_error (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    ‖a • shiftedResolvent ε hε hbar coupling a t (x:Hilbert)-(x:Hilbert)‖ ≤
      a⁻¹*‖homogeneousHamiltonian ε hε hbar coupling t x‖ :=
  approximation_error _ _ a ha (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t) (shiftedResolvent_left ε hε hbar coupling a t ha) x

theorem homogeneous_resolvent_strong_limit (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (f : Hilbert) :
    Tendsto (fun a : ℝ => a • shiftedResolvent ε hε hbar coupling a t f) atTop (𝓝 f) :=
  scaled_resolvent_strong_limit _ _ (homogeneous_dense_domain ε hε hbar coupling t)
    (fun a ha => homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t)
    (fun a ha => shiftedResolvent_left ε hε hbar coupling a t ha) f

def homogeneousYosida (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  yosida (shiftedResolvent ε hε hbar coupling a t) a

theorem homogeneousYosida_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (homogeneousYosida ε hε hbar coupling a t) :=
  yosida_selfAdjoint _ _ a (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_selfAdjoint ε hε hbar coupling t)

theorem homogeneousYosida_positive (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (f : Hilbert) : 0 ≤ (inner ℂ (homogeneousYosida ε hε hbar coupling a t f) f).re :=
  yosida_positive _ _ a ha (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t) f

theorem homogeneousYosida_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a) :
    ‖homogeneousYosida ε hε hbar coupling a t‖ ≤ 2*a :=
  yosida_norm_bound _ _ a ha (homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t)

theorem homogeneousYosida_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling a : ℝ) (ha : 0 < a) :
    Continuous (homogeneousYosida ε hε hbar coupling a) :=
  continuous_const.sub (((shiftedResolvent_continuous ε hε hbar coupling a ha).const_smul a).const_smul a)

theorem homogeneousYosida_on_domain (ε : ℝ) (hε : 0 < ε) (hbar coupling a t : ℝ) (ha : 0 < a)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    homogeneousYosida ε hε hbar coupling a t (x:Hilbert) =
      a • shiftedResolvent ε hε hbar coupling a t (homogeneousHamiltonian ε hε hbar coupling t x) :=
  yosida_on_domain _ _ a (shiftedResolvent_left ε hε hbar coupling a t ha) x

theorem homogeneousYosida_strong_limit (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (x : (homogeneousHamiltonian ε hε hbar coupling t).domain) :
    Tendsto (fun a : ℝ => homogeneousYosida ε hε hbar coupling a t (x:Hilbert)) atTop
      (𝓝 (homogeneousHamiltonian ε hε hbar coupling t x)) :=
  yosida_strong_limit_on_domain _ _ (homogeneous_dense_domain ε hε hbar coupling t)
    (fun a ha => homogeneous_resolves ε hε hbar coupling a t ha)
    (homogeneous_positive ε hε hbar coupling t)
    (fun a ha => shiftedResolvent_left ε hε hbar coupling a t ha) x

#print axioms shiftedResolvent_selfAdjoint
#print axioms shiftedResolvent_positive
#print axioms shiftedResolvent_norm
#print axioms shiftedResolvent_injective
#print axioms shiftedResolvent_dense
#print axioms homogeneous_approximation_error
#print axioms homogeneous_resolvent_strong_limit
#print axioms homogeneousYosida_selfAdjoint
#print axioms homogeneousYosida_positive
#print axioms homogeneousYosida_norm
#print axioms homogeneousYosida_continuous
#print axioms homogeneousYosida_on_domain
#print axioms homogeneousYosida_strong_limit

end
end UnifiedTheory.Audit.KFCausalRegularizedYosida

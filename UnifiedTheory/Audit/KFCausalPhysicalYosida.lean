/- Bounded positive self-adjoint approximations to the actual eight-factor
Hamiltonian. Their strong limit is proved on its operator domain at each
fixed time; convergence of evolving states is a separate statement. -/
import UnifiedTheory.Audit.KFCausalPhysicalShiftedResolvent
import UnifiedTheory.Audit.KFCausalYosidaApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalYosida
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian
open UnifiedTheory.Audit.KFCausalPhysicalShiftedResolvent
open UnifiedTheory.Audit.KFCausalPositiveResolventBounds
open UnifiedTheory.Audit.KFCausalYosidaApproximation

theorem physical_resolves (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    Resolves (hamiltonian ε hε hbar hh mass2 quartic vacuum t)
      (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t) a :=
  shiftedResolvent_equation ε hε hbar hh mass2 quartic vacuum a t ha

theorem shiftedResolvent_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t) :=
  resolvent_selfAdjoint _ _ a (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_selfAdjoint ε hε hbar hh mass2 quartic vacuum t)

theorem shiftedResolvent_positive (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (f : Hilbert) : 0 ≤ (inner ℂ (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f) f).re :=
  resolvent_positive _ _ a ha (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_selfAdjoint ε hε hbar hh mass2 quartic vacuum t) (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t) f

theorem shiftedResolvent_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    ‖shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t‖ ≤ a⁻¹ :=
  resolvent_norm_bound _ _ a ha (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t)

theorem shiftedResolvent_injective (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    Function.Injective (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t) :=
  resolvent_injective _ _ a (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)

theorem shiftedResolvent_dense (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    DenseRange (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t) :=
  resolvent_dense _ _ a (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_selfAdjoint ε hε hbar hh mass2 quartic vacuum t)

theorem physical_approximation_error (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    ‖a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t (x:Hilbert)-(x:Hilbert)‖ ≤
      a⁻¹*‖hamiltonian ε hε hbar hh mass2 quartic vacuum t x‖ :=
  approximation_error _ _ a ha (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t) (shiftedResolvent_left ε hε hbar hh mass2 quartic vacuum a t ha) x

theorem physical_resolvent_strong_limit (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (f : Hilbert) :
    Tendsto (fun a : ℝ => a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t f) atTop (𝓝 f) :=
  scaled_resolvent_strong_limit _ _ (hamiltonian_dense ε hε hbar hh mass2 quartic vacuum t)
    (fun a ha => physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t)
    (fun a ha => shiftedResolvent_left ε hε hbar hh mass2 quartic vacuum a t ha) f

def physicalYosida (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  yosida (shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t) a

theorem physicalYosida_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (physicalYosida ε hε hbar hh mass2 quartic vacuum a t) :=
  yosida_selfAdjoint _ _ a (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_selfAdjoint ε hε hbar hh mass2 quartic vacuum t)

theorem physicalYosida_positive (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (f : Hilbert) : 0 ≤ (inner ℂ (physicalYosida ε hε hbar hh mass2 quartic vacuum a t f) f).re :=
  yosida_positive _ _ a ha (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t) f

theorem physicalYosida_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a) :
    ‖physicalYosida ε hε hbar hh mass2 quartic vacuum a t‖ ≤ 2*a :=
  yosida_norm_bound _ _ a ha (physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t)

theorem physicalYosida_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a) :
    Continuous (physicalYosida ε hε hbar hh mass2 quartic vacuum a) :=
  continuous_const.sub (((shiftedResolvent_continuous ε hε hbar hh mass2 quartic vacuum a ha).const_smul a).const_smul a)

theorem physicalYosida_on_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a t : ℝ) (ha : 0 < a)
    (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    physicalYosida ε hε hbar hh mass2 quartic vacuum a t (x:Hilbert) =
      a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t (hamiltonian ε hε hbar hh mass2 quartic vacuum t x) :=
  yosida_on_domain _ _ a (shiftedResolvent_left ε hε hbar hh mass2 quartic vacuum a t ha) x

theorem physicalYosida_strong_limit (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (x : (hamiltonian ε hε hbar hh mass2 quartic vacuum t).domain) :
    Tendsto (fun a : ℝ => physicalYosida ε hε hbar hh mass2 quartic vacuum a t (x:Hilbert)) atTop
      (𝓝 (hamiltonian ε hε hbar hh mass2 quartic vacuum t x)) :=
  yosida_strong_limit_on_domain _ _ (hamiltonian_dense ε hε hbar hh mass2 quartic vacuum t)
    (fun a ha => physical_resolves ε hε hbar hh mass2 quartic vacuum a t ha)
    (hamiltonian_positive ε hε hbar hh mass2 quartic vacuum t)
    (fun a ha => shiftedResolvent_left ε hε hbar hh mass2 quartic vacuum a t ha) x

#print axioms shiftedResolvent_selfAdjoint
#print axioms shiftedResolvent_positive
#print axioms shiftedResolvent_norm
#print axioms shiftedResolvent_injective
#print axioms shiftedResolvent_dense
#print axioms physical_approximation_error
#print axioms physical_resolvent_strong_limit
#print axioms physicalYosida_selfAdjoint
#print axioms physicalYosida_positive
#print axioms physicalYosida_norm
#print axioms physicalYosida_continuous
#print axioms physicalYosida_on_domain
#print axioms physicalYosida_strong_limit

end
end UnifiedTheory.Audit.KFCausalPhysicalYosida

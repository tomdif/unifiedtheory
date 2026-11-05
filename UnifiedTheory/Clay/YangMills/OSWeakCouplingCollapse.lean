/- The actual Wilson beta-to-infinity limit has only the vacuum in its unscaled
real-character OS sector. This is an obstruction to extracting a nontrivial
Yang--Mills sector from these bare observables without further scaling. -/
import UnifiedTheory.Clay.YangMills.OSFactorizedCollapse
import UnifiedTheory.Clay.YangMills.BareDefectHierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSWeakCouplingCollapse
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSFactorizedCollapse BareDefectHierarchy
open scoped NNReal Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {d : Type*} [Fintype d] [DecidableEq d]
  (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
  (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
  (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop atTop) (W : Hierarchy)
  (hW : WeakConvergence (fun k => unitaryHierarchy (period k) (a k) plane ρ hρ (beta k)) W)
  (hp : Positive W plane)

/-- A concrete scalar realization of the actual Wilson weak limit. -/
def scalarRealization : Hilbert (positiveKernel W plane hp) →ₗᵢ[ℂ] ℂ :=
  OSFactorizedCollapse.scalarRealization W plane (Fintype.card d)
    (weak_limit_eq_constant period a plane ρ hρ beta hbeta W hW) hp

include hbeta hW in
theorem vacuum_norm : ‖canonical (positiveKernel W plane hp) vacuumLabel‖ = 1 :=
  OSFactorizedCollapse.vacuum_norm W plane (Fintype.card d)
    (weak_limit_eq_constant period a plane ρ hρ beta hbeta W hW) hp

theorem every_state_vacuum_multiple (v : Hilbert (positiveKernel W plane hp)) :
    v = (scalarRealization period a plane ρ hρ beta hbeta W hW hp v) •
      canonical (positiveKernel W plane hp) vacuumLabel :=
  OSFactorizedCollapse.every_state_vacuum_multiple W plane (Fintype.card d)
    (weak_limit_eq_constant period a plane ρ hρ beta hbeta W hW) hp v

include hbeta hW in
/-- The vacuum-orthogonal sector is zero for these actual unscaled observables. -/
theorem vacuum_orthogonal_eq_zero (v : Hilbert (positiveKernel W plane hp))
    (hv : inner ℂ (canonical (positiveKernel W plane hp) vacuumLabel) v = 0) : v = 0 :=
  OSFactorizedCollapse.vacuum_orthogonal_eq_zero W plane (Fintype.card d)
    (weak_limit_eq_constant period a plane ρ hρ beta hbeta W hW) hp v hv

include hbeta hW in
/-- In particular, the actual OS evolution constructed from the candidate is
identity on this sector along every beta-to-infinity trajectory. -/
theorem evolution_identity (D : Evolution W plane hp) (t : ℝ≥0)
    (v : Hilbert (positiveKernel W plane hp)) : D.operator t v = v :=
  OSFactorizedCollapse.evolution_identity W plane (Fintype.card d)
    (weak_limit_eq_constant period a plane ρ hρ beta hbeta W hW) hp D t v

end
end UnifiedTheory.Clay.YangMills.OSWeakCouplingCollapse

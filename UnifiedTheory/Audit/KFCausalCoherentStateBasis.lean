/- The actual coherent family is a basis of its algebraic span. Every
seed output therefore has a unique linear extension to that span. This
does not assert boundedness, closability, or a basis of the full Hilbert space. -/
import UnifiedTheory.Audit.KFCausalModulatedLpIndependence
import UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentStateBasis
noncomputable section
open Module
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (dilate dilationEquiv momentumScale momentumScale_ne_zero)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

theorem state_linearIndependent : LinearIndependent ℂ (state ε a h hε ha hh) := by
  apply LinearIndependent.of_comp chargeCoordinates.toLinearEquiv.toLinearMap
  have hi := (KFCausalModulatedLpIndependence.state_linearIndependent (weight ε a h)
    (weight_memLp ε a h hε ha hh) (weight_ne_zero ε a h hε hh)).comp
    (dilate (momentumScale h)) (dilationEquiv _ (momentumScale_ne_zero h hh)).injective
  change LinearIndependent ℂ (fun k => chargeCoordinates (state ε a h hε ha hh k))
  simpa only [Function.comp_def,state_coordinates,mixedState] using hi

def seed (k : Joint 2 4) : coherentSpan ε a h hε ha hh :=
  ⟨state ε a h hε ha hh k,Submodule.subset_span (Set.mem_range_self k)⟩

def basis : Basis (Joint 2 4) ℂ (coherentSpan ε a h hε ha hh) :=
  Basis.span (state_linearIndependent ε a h hε ha hh)

theorem basis_eq_seed (k : Joint 2 4) : basis ε a h hε ha hh k = seed ε a h hε ha hh k :=
  Subtype.ext (Basis.span_apply (state_linearIndependent ε a h hε ha hh) k)

def extend (v : Joint 2 4 → Hilbert) : coherentSpan ε a h hε ha hh →ₗ[ℂ] Hilbert :=
  (basis ε a h hε ha hh).constr ℂ v

theorem extend_seed (v : Joint 2 4 → Hilbert) (k : Joint 2 4) :
    extend ε a h hε ha hh v (seed ε a h hε ha hh k) = v k := by
  rw [← basis_eq_seed]
  exact (basis ε a h hε ha hh).constr_basis ℂ v k

theorem extend_sum (v : Joint 2 4 → Hilbert) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) :
    extend ε a h hε ha hh v (∑ r, z r • seed ε a h hε ha hh (k r)) = ∑ r, z r • v (k r) := by
  simp only [map_sum,map_smul,extend_seed]

theorem extend_of_representation (v : Joint 2 4 → Hilbert) (f : coherentSpan ε a h hε ha hh)
    {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) :
    extend ε a h hε ha hh v f = ∑ r, z r • v (k r) := by
  have he : f = ∑ r, z r • seed ε a h hε ha hh (k r) :=
    Subtype.ext (by simpa only [Submodule.coe_sum,Submodule.coe_smul,seed] using hf)
  rw [he,extend_sum]

theorem representation_independent (v : Joint 2 4 → Hilbert)
    {n m : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ) (p : Fin m → Joint 2 4) (c : Fin m → ℂ)
    (he : (∑ r, z r • state ε a h hε ha hh (k r)) = ∑ r, c r • state ε a h hε ha hh (p r)) :
    (∑ r, z r • v (k r)) = ∑ r, c r • v (p r) := by
  have hs : (∑ r, z r • seed ε a h hε ha hh (k r)) = ∑ r, c r • seed ε a h hε ha hh (p r) :=
    Subtype.ext (by simpa only [Submodule.coe_sum,Submodule.coe_smul,seed] using he)
  have hv := congrArg (extend ε a h hε ha hh v) hs
  simpa only [extend_sum] using hv

theorem extension_unique (v : Joint 2 4 → Hilbert)
    (L : coherentSpan ε a h hε ha hh →ₗ[ℂ] Hilbert)
    (hL : ∀ k, L (seed ε a h hε ha hh k) = v k) : extend ε a h hε ha hh v = L := by
  apply (basis ε a h hε ha hh).ext
  intro k
  rw [basis_eq_seed,extend_seed,hL]

#print axioms state_linearIndependent
#print axioms basis_eq_seed
#print axioms extend_seed
#print axioms extend_sum
#print axioms extend_of_representation
#print axioms representation_independent
#print axioms extension_unique
end
end UnifiedTheory.Audit.KFCausalCoherentStateBasis

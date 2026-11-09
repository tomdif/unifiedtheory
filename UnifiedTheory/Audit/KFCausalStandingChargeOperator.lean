/- The actual generator and zero-sector projection for the constructed
standing-wave circle action. The operator is self-adjoint on its maximal
strong-derivative domain. Its equality to a finite-occupation limit and
compatibility with the Hamiltonian energy domain are not assumed. -/
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction
import UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
import UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalStandingChargeOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction
open UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator

def standingCharge (hbar : ℝ) (hh : hbar ≠ 0) : Hilbert →ₗ.[ℂ] Hilbert :=
  momentum (group hbar hh) 1

theorem standingCharge_selfAdjoint (hbar : ℝ) (hh : hbar ≠ 0) :
    IsSelfAdjoint (standingCharge hbar hh) :=
  momentum_selfAdjoint (group hbar hh) 1 (by norm_num)

theorem standingCharge_closed (hbar : ℝ) (hh : hbar ≠ 0) :
    (standingCharge hbar hh).IsClosed := (standingCharge_selfAdjoint hbar hh).isClosed

theorem standingCharge_dense (hbar : ℝ) (hh : hbar ≠ 0) :
    Dense ((standingCharge hbar hh).domain : Set Hilbert) := momentum_dense (group hbar hh) 1

theorem standingCharge_graph (hbar : ℝ) (hh : hbar ≠ 0) (f g : Hilbert) :
    (f,g) ∈ (standingCharge hbar hh).graph ↔
      HasDerivAt (fun θ => action hbar hh θ f) (Complex.I • g) 0 := by
  simpa only [Complex.ofReal_one, div_one] using momentum_graph_iff (group hbar hh) 1 (by norm_num) f g

theorem standingCharge_orbit_derivative (hbar : ℝ) (hh : hbar ≠ 0)
    (f : (standingCharge hbar hh).domain) (θ : ℝ) :
    HasDerivAt (fun φ => action hbar hh φ (f:Hilbert))
      (Complex.I • action hbar hh θ (standingCharge hbar hh f)) θ := by
  simpa only [Complex.ofReal_one, div_one] using
    momentum_orbit_derivative (group hbar hh) 1 (by norm_num) f θ

def zeroSector (hbar : ℝ) (hh : hbar ≠ 0) : Submodule ℂ Hilbert := fixedSpace (group hbar hh)

theorem zeroSector_closed (hbar : ℝ) (hh : hbar ≠ 0) : IsClosed (zeroSector hbar hh : Set Hilbert) :=
  fixedSpace_closed (group hbar hh)

theorem standingCharge_zero_iff (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    (f,0) ∈ (standingCharge hbar hh).graph ↔ f ∈ zeroSector hbar hh := by
  rw [standingCharge_graph, smul_zero]
  have hg := generator_zero_iff_fixed (group hbar hh) f
  rw [generator_graph_iff] at hg
  exact hg

def zeroProjection (hbar : ℝ) (hh : hbar ≠ 0) : Hilbert →L[ℂ] Hilbert :=
  meanOperator (group hbar hh) (2*Real.pi) (by positivity)

theorem zeroProjection_integral (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    zeroProjection hbar hh f = (2*Real.pi)⁻¹ • ∫ θ in 0..2*Real.pi, action hbar hh θ f := rfl

theorem zeroProjection_mem (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    zeroProjection hbar hh f ∈ zeroSector hbar hh :=
  average_fixed (group hbar hh) (2*Real.pi) (action_full_period hbar hh) f

theorem zeroProjection_fixes (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert)
    (hf : f ∈ zeroSector hbar hh) : zeroProjection hbar hh f = f :=
  average_of_fixed (group hbar hh) (2*Real.pi) (by positivity) f hf

theorem zeroProjection_idempotent (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    zeroProjection hbar hh (zeroProjection hbar hh f) = zeroProjection hbar hh f :=
  zeroProjection_fixes hbar hh _ (zeroProjection_mem hbar hh f)

theorem zeroProjection_selfAdjoint (hbar : ℝ) (hh : hbar ≠ 0) :
    IsSelfAdjoint (zeroProjection hbar hh) :=
  meanOperator_selfAdjoint (group hbar hh) (2*Real.pi) (by positivity) (action_full_period hbar hh)

theorem zeroProjection_norm_le (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    ‖zeroProjection hbar hh f‖ ≤ ‖f‖ := average_norm_le (group hbar hh) (2*Real.pi) (by positivity) f

theorem zeroProjection_range (hbar : ℝ) (hh : hbar ≠ 0) :
    Set.range (zeroProjection hbar hh) = (zeroSector hbar hh : Set Hilbert) := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact zeroProjection_mem hbar hh g
  · intro hf
    exact ⟨f,zeroProjection_fixes hbar hh f hf⟩

theorem standingCharge_projection_zero (hbar : ℝ) (hh : hbar ≠ 0) (f : Hilbert) :
    (zeroProjection hbar hh f,0) ∈ (standingCharge hbar hh).graph :=
  (standingCharge_zero_iff hbar hh _).mpr (zeroProjection_mem hbar hh f)

theorem action_zeroProjection (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    action hbar hh θ (zeroProjection hbar hh f) = zeroProjection hbar hh f :=
  zeroProjection_mem hbar hh f θ

theorem zeroProjection_action (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (f : Hilbert) :
    zeroProjection hbar hh (action hbar hh θ f) = zeroProjection hbar hh f := by
  apply ext_inner_left ℂ
  intro g
  have hs (x y : Hilbert) : inner ℂ (zeroProjection hbar hh x) y =
      inner ℂ x (zeroProjection hbar hh y) :=
    average_symmetric (group hbar hh) (2*Real.pi) (by positivity) (action_full_period hbar hh) x y
  have ht : inner ℂ (zeroProjection hbar hh g) (action hbar hh θ f) =
      inner ℂ (action hbar hh (-θ) (zeroProjection hbar hh g)) f :=
    inner_transport (group hbar hh) f (zeroProjection hbar hh g) θ
  rw [← hs, ht, action_zeroProjection, hs]

#print axioms standingCharge_selfAdjoint
#print axioms standingCharge_closed
#print axioms standingCharge_dense
#print axioms standingCharge_graph
#print axioms standingCharge_orbit_derivative
#print axioms zeroSector_closed
#print axioms standingCharge_zero_iff
#print axioms zeroProjection_integral
#print axioms zeroProjection_mem
#print axioms zeroProjection_fixes
#print axioms zeroProjection_idempotent
#print axioms zeroProjection_selfAdjoint
#print axioms zeroProjection_norm_le
#print axioms zeroProjection_range
#print axioms standingCharge_projection_zero
#print axioms action_zeroProjection
#print axioms zeroProjection_action

end
end UnifiedTheory.Audit.KFCausalStandingChargeOperator

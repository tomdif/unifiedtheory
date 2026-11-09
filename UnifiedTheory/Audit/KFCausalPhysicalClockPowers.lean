/- Actual positive self-adjoint powers of the physical multiplication
clock C=exp(s). Exact graph and composition laws retain their domains. -/
import UnifiedTheory.Audit.KFCausalSpectralExponential
import UnifiedTheory.Audit.KFCausalConfigurationTestSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalClockPowers
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalSpectralExponential

def clockPower (b : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  exponential (LinearIsometryEquiv.refl ℂ Hilbert) (fun z : Configuration => z.1) measurable_fst b

theorem clockPower_selfAdjoint (b : ℝ) : IsSelfAdjoint (clockPower b) :=
  exponential_selfAdjoint _ _ _ _

theorem clockPower_graph (b : ℝ) (f g : Hilbert) :
    (f,g) ∈ (clockPower b).graph ↔ g =ᵐ[volume] fun z => (Real.exp (b*z.1):ℂ)*f z :=
  exponential_graph_iff _ _ _ _ _ _

theorem clockPower_domain (b : ℝ) (f : Hilbert) :
    f ∈ (clockPower b).domain ↔ Integrable (fun z : Configuration => Real.exp (2*b*z.1)*‖f z‖^2) :=
  exponential_domain_iff _ _ _ _ _

theorem clockPower_energy (b : ℝ) (f : (clockPower b).domain) :
    ‖clockPower b f‖^2 = ∫ z : Configuration, Real.exp (2*b*z.1)*‖(f:Hilbert) z‖^2 :=
  exponential_energy _ _ _ _ _

theorem clockPower_positive (b : ℝ) (f : (clockPower b).domain) :
    0 ≤ (inner ℂ (clockPower b f) (f:Hilbert)).re := exponential_positive _ _ _ _ _

theorem clockPower_closed (b : ℝ) : (clockPower b).IsClosed := exponential_closed _ _ _ _

theorem clockPower_dense (b : ℝ) : Dense ((clockPower b).domain : Set Hilbert) :=
  exponential_dense _ _ _ _

theorem clockPower_inverse_graph (b : ℝ) (f g : Hilbert) :
    (f,g) ∈ (clockPower b).graph ↔ (g,f) ∈ (clockPower (-b)).graph :=
  exponential_inverse_graph _ _ _ _ _ _

theorem clockPower_comp_graph (b c : ℝ) (f g h : Hilbert)
    (hf : (f,g) ∈ (clockPower b).graph) (hg : (g,h) ∈ (clockPower c).graph) :
    (f,h) ∈ (clockPower (b+c)).graph := exponential_comp_graph _ _ _ _ _ _ _ _ hf hg

#print axioms clockPower_selfAdjoint
#print axioms clockPower_graph
#print axioms clockPower_domain
#print axioms clockPower_energy
#print axioms clockPower_positive
#print axioms clockPower_closed
#print axioms clockPower_dense
#print axioms clockPower_inverse_graph
#print axioms clockPower_comp_graph

end
end UnifiedTheory.Audit.KFCausalPhysicalClockPowers

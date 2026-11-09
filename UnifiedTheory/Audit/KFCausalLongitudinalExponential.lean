/- The positive exponential of the coupled longitudinal momentum, constructed
in the Fourier representation already proved for that actual generator.
This is a fixed-positive-regulator continuum result, not a cutoff limit. -/
import UnifiedTheory.Audit.KFCausalSpectralExponentialSquare
import UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLongitudinalExponential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
open UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier
open UnifiedTheory.Audit.KFCausalSpectralExponential
open UnifiedTheory.Audit.KFCausalSpectralExponentialSquare

theorem symbol_measurable (hbar : ℝ) : Measurable (symbol hbar) := by
  unfold symbol
  fun_prop

def longitudinalExponential (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  exponential (coupledFourier ε hε) (symbol hbar) (symbol_measurable hbar) a

theorem longitudinal_exponential_selfAdjoint (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) :
    IsSelfAdjoint (longitudinalExponential ε hε hbar a) :=
  exponential_selfAdjoint _ _ _ _

theorem longitudinal_exponential_graph (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε hbar a).graph ↔
      coupledFourier ε hε g =ᵐ[volume]
        fun k => (Real.exp (a*symbol hbar k):ℂ)*(coupledFourier ε hε f) k :=
  exponential_graph_iff _ _ _ _ _ _

theorem longitudinal_exponential_domain (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) (f : Hilbert) :
    f ∈ (longitudinalExponential ε hε hbar a).domain ↔
      Integrable (fun k => Real.exp (2*a*symbol hbar k)*‖(coupledFourier ε hε f) k‖^2) :=
  exponential_domain_iff _ _ _ _ _

theorem longitudinal_exponential_energy (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ)
    (f : (longitudinalExponential ε hε hbar a).domain) :
    ‖longitudinalExponential ε hε hbar a f‖^2 =
      ∫ k, Real.exp (2*a*symbol hbar k)*‖(coupledFourier ε hε (f:Hilbert)) k‖^2 :=
  exponential_energy _ _ _ _ f

theorem longitudinal_exponential_positive (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ)
    (f : (longitudinalExponential ε hε hbar a).domain) :
    0 ≤ (inner ℂ (longitudinalExponential ε hε hbar a f) (f:Hilbert)).re :=
  exponential_positive _ _ _ _ f

theorem longitudinal_exponential_dense (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) :
    Dense ((longitudinalExponential ε hε hbar a).domain : Set Hilbert) :=
  exponential_dense _ _ _ _

theorem longitudinal_exponential_closed (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) :
    (longitudinalExponential ε hε hbar a).IsClosed := exponential_closed _ _ _ _

theorem longitudinal_exponential_inverse (ε : ℝ) (hε : 0 < ε) (hbar a : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε hbar a).graph ↔
      (g,f) ∈ (longitudinalExponential ε hε hbar (-a)).graph :=
  exponential_inverse_graph _ _ _ _ _ _

theorem longitudinal_exponential_comp (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) (f g h : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε hbar a).graph)
    (hgh : (g,h) ∈ (longitudinalExponential ε hε hbar b).graph) :
    (f,h) ∈ (longitudinalExponential ε hε hbar (a+b)).graph :=
  exponential_comp_graph _ _ _ _ _ _ _ _ hfg hgh

theorem half_exponential_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) :
    f ∈ (longitudinalExponential ε hε hbar (1/2)).domain ↔
      Integrable (fun k => Real.exp (symbol hbar k)*‖(coupledFourier ε hε f) k‖^2) := by
  have he : (2:ℝ)*(1/2)=1 := by norm_num
  simpa only [he,one_mul] using longitudinal_exponential_domain ε hε hbar (1/2) f

theorem half_exponential_energy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : (longitudinalExponential ε hε hbar (1/2)).domain) :
    ‖longitudinalExponential ε hε hbar (1/2) f‖^2 =
      ∫ k, Real.exp (symbol hbar k)*‖(coupledFourier ε hε (f:Hilbert)) k‖^2 := by
  have he : (2:ℝ)*(1/2)=1 := by norm_num
  simpa only [he,one_mul] using longitudinal_exponential_energy ε hε hbar (1/2) f

theorem longitudinal_exponential_square (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f h : Hilbert) :
    (f,h) ∈ (longitudinalExponential ε hε hbar 1).graph ↔
      ∃ g : Hilbert, (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph ∧
        (g,h) ∈ (longitudinalExponential ε hε hbar (1/2)).graph := by
  have he : (2:ℝ)*(1/2)=1 := by norm_num
  simpa only [he] using exponential_square_graph (coupledFourier ε hε)
    (symbol hbar) (symbol_measurable hbar) (1/2) f h

#print axioms symbol_measurable
#print axioms longitudinal_exponential_selfAdjoint
#print axioms longitudinal_exponential_graph
#print axioms longitudinal_exponential_domain
#print axioms longitudinal_exponential_energy
#print axioms longitudinal_exponential_positive
#print axioms longitudinal_exponential_dense
#print axioms longitudinal_exponential_closed
#print axioms longitudinal_exponential_inverse
#print axioms longitudinal_exponential_comp
#print axioms half_exponential_domain
#print axioms half_exponential_energy
#print axioms longitudinal_exponential_square

end
end UnifiedTheory.Audit.KFCausalLongitudinalExponential

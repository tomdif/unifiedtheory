/- Strong differentiation of an affine-time squeeze on its actual
maximal generator graph. The coefficient in a moving frame is retained. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator
import UnifiedTheory.Audit.KFCausalNeutralReferencePairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeGroup squeezeMomentum squeeze_graph_derivative)
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator (derivative_at_time)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

theorem affine_time_derivative (h : ℝ) (hne : h ≠ 0) (a t : ℝ) (f z : Hilbert)
    (hfz : (f,z) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun b => transport (a*b) f)
      ((coefficient h*(a:ℂ)) • transport (a*t) z) t := by
  have hd := derivative_at_time squeezeGroup f ((Complex.I/(h:ℂ)) • z)
    ((squeeze_graph_derivative h hne f z).mp hfz) (a*t)
  have hc := hd.scomp t ((hasDerivAt_id t).const_mul a)
  have he : a • ((Complex.I/(h:ℂ)) • transport (a*t) z) =
      ((coefficient h*(a:ℂ)) • transport (a*t) z) := by
    rw [← smul_assoc,Complex.real_smul]
    congr 1
    simp only [coefficient,div_eq_mul_inv,Complex.ofReal_inv,one_mul]
    ring
  simpa only [squeezeGroup,map_smul,id_eq,mul_one,he] using hc

#print axioms affine_time_derivative
end
end UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative

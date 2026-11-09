/- Strong differentiation and the graph of the constructed self-adjoint
momentum. These concern longitudinal group time. -/
import UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : StrongUnitaryGroup H)

theorem inverse_coefficient (hbar : ℝ) (hh : hbar ≠ 0) :
    (Complex.I/(hbar:ℂ))*(-Complex.I*(hbar:ℂ)) = 1 := by
  have hn : (hbar:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp
  ring_nf
  norm_num [Complex.I_sq]

theorem generator_from_momentum (hbar : ℝ) (hh : hbar ≠ 0) (x : (momentum U hbar).domain) :
    (Complex.I/(hbar:ℂ)) • momentum U hbar x = generator U x := by
  rw [momentum_apply,smul_smul,inverse_coefficient hbar hh,one_smul]

theorem momentum_graph_iff (hbar : ℝ) (hh : hbar ≠ 0) (x y : H) :
    (x,y) ∈ (momentum U hbar).graph ↔
      HasDerivAt (fun t => U.action t x) ((Complex.I/(hbar:ℂ)) • y) 0 := by
  constructor
  · intro hp
    obtain ⟨v,hv,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
    have hd := generator_derivative U v
    rw [← generator_from_momentum U hbar hh v,hv,hy] at hd
    exact hd
  · intro hd
    let v : (momentum U hbar).domain := ⟨x,hd.differentiableAt⟩
    refine (LinearPMap.mem_graph_iff _).mpr ⟨v,rfl,?_⟩
    change (-Complex.I*(hbar:ℂ)) • deriv (fun t => U.action t x) 0 = y
    rw [hd.deriv,smul_smul,mul_comm,inverse_coefficient hbar hh,one_smul]

theorem momentum_orbit_derivative (hbar : ℝ) (hh : hbar ≠ 0)
    (x : (momentum U hbar).domain) (t : ℝ) :
    HasDerivAt (fun s => U.action s (x:H))
      ((Complex.I/(hbar:ℂ)) • U.action t (momentum U hbar x)) t := by
  have hd := derivative_at_time U x (generator U x) (generator_derivative U x) t
  rw [← generator_from_momentum U hbar hh x,map_smul] at hd
  exact hd

theorem momentum_commutes (hbar t : ℝ) (x : (momentum U hbar).domain) :
    momentum U hbar (domainAction U t x) = U.action t (momentum U hbar x) := by
  rw [momentum_apply,generator_commutes,momentum_apply,map_smul]

variable [CompleteSpace H]

def averageState (hbar : ℝ) (x : H) (a : ℝ) : (momentum U hbar).domain :=
  ⟨average U x a,(average_derivative U x a).differentiableAt⟩

theorem average_momentum (hbar : ℝ) (x : H) (a : ℝ) :
    momentum U hbar (averageState U hbar x a) =
      (-Complex.I*(hbar:ℂ)) • (a⁻¹ • (U.action a x-x)) := by
  change (-Complex.I*(hbar:ℂ)) • deriv (fun t => U.action t (average U x a)) 0 = _
  rw [(average_derivative U x a).deriv]

#print axioms inverse_coefficient
#print axioms generator_from_momentum
#print axioms momentum_graph_iff
#print axioms momentum_orbit_derivative
#print axioms momentum_commutes
#print axioms average_momentum

end
end UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

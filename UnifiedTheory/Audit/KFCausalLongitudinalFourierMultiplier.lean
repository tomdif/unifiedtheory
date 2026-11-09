/- Exact Fourier multiplier and maximal domain of the actual coupled
longitudinal momentum. The forward inclusion follows from strong/pointwise
derivative comparison; the reverse inclusion uses proved self-adjointness. -/
import UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
import UnifiedTheory.Audit.KFCausalLpDerivativeRepresentative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalCoupledUnitaryTransport
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalMomentum
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
open UnifiedTheory.Audit.KFCausalLpDerivativeRepresentative
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

def symbol (hbar : ℝ) (k : Space) : ℝ := 2*Real.pi*hbar*k 0

theorem clock_phase_derivative (k : Space) (z : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((2*Real.pi*t*k 0:ℝ)*Complex.I)*z)
      ((2*Real.pi*k 0:ℝ)*Complex.I*z) 0 := by
  have hd := (((hasDerivAt_id (0:ℝ)).const_mul (2*Real.pi)).mul_const (k 0)).ofReal_comp.mul_const Complex.I
  have he := hd.cexp.mul_const z
  simpa only [id_eq,mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul,
    mul_one] using he

theorem momentum_fourier_coe (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : (longitudinalMomentum ε hε hbar).domain) :
    coupledFourier ε hε (longitudinalMomentum ε hε hbar f) =ᵐ[volume]
      fun k => (symbol hbar k:ℂ)*(coupledFourier ε hε (f:Hilbert)) k := by
  have hd := longitudinal_strong_derivative ε hε hbar hh f 0
  simp only [transport_initial] at hd
  have hF := ((coupledFourier ε hε : Hilbert →L[ℂ] FrequencyHilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  change HasDerivAt (fun t => coupledFourier ε hε (transport ε hε t (f:Hilbert)))
    (coupledFourier ε hε ((Complex.I/(hbar:ℂ)) • longitudinalMomentum ε hε hbar f)) 0 at hF
  rw [map_smul] at hF
  have hrep := derivative_representative _ _ _ _
    (fun t => coupledFourier_transport_coe ε hε t f) hF
    (fun k => clock_phase_derivative k ((coupledFourier ε hε (f:Hilbert)) k))
  filter_upwards [hrep,Lp.coeFn_smul (Complex.I/(hbar:ℂ))
    (coupledFourier ε hε (longitudinalMomentum ε hε hbar f))] with k hk hs
  rw [hs] at hk
  simp only [Pi.smul_apply,smul_eq_mul] at hk
  have he := congrArg (fun z : ℂ => (-Complex.I*(hbar:ℂ))*z) hk
  dsimp only at he
  have hi : (-Complex.I*(hbar:ℂ))*(Complex.I/(hbar:ℂ)) = 1 := by
    rw [mul_comm,inverse_coefficient hbar hh]
  rw [← mul_assoc,hi,one_mul] at he
  rw [he]
  unfold symbol
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

theorem real_multiplier_inner (w : Space → ℝ) (f f' g g' : FrequencyHilbert)
    (hf : f' =ᵐ[volume] fun k => (w k:ℂ)*f k)
    (hg : g' =ᵐ[volume] fun k => (w k:ℂ)*g k) :
    inner ℂ f' g = inner ℂ f g' := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf,hg] with k hk hl
  rw [hk,hl]
  change inner ℂ ((w k:ℂ) • f k) (g k) = inner ℂ (f k) ((w k:ℂ) • g k)
  simp [mul_assoc,mul_left_comm]

theorem momentum_graph_fourier_iff (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f g : Hilbert) :
    (f,g) ∈ (longitudinalMomentum ε hε hbar).graph ↔
      coupledFourier ε hε g =ᵐ[volume] fun k => (symbol hbar k:ℂ)*(coupledFourier ε hε f) k := by
  constructor
  · intro hp
    obtain ⟨v,hv,hg⟩ := (LinearPMap.mem_graph_iff _).mp hp
    simpa only [hv,hg] using momentum_fourier_coe ε hε hbar hh v
  · intro hfg
    have hp : ∀ y : (longitudinalMomentum ε hε hbar).domain,
        inner ℂ g (y:Hilbert) = inner ℂ f (longitudinalMomentum ε hε hbar y) := by
      intro y
      have he := real_multiplier_inner (symbol hbar)
        (coupledFourier ε hε f) (coupledFourier ε hε g)
        (coupledFourier ε hε (y:Hilbert)) (coupledFourier ε hε (longitudinalMomentum ε hε hbar y))
        hfg (momentum_fourier_coe ε hε hbar hh y)
      simpa only [LinearIsometryEquiv.inner_map_map] using he
    have ha := LinearPMap.mem_adjoint_domain_of_exists (T := longitudinalMomentum ε hε hbar) f ⟨g,hp⟩
    have he := LinearPMap.adjoint_apply_eq (longitudinal_dense ε hε hbar) ⟨f,ha⟩ hp
    have hg := (longitudinalMomentum ε hε hbar).adjoint.mem_graph ⟨f,ha⟩
    rw [he] at hg
    change (f,g) ∈ (longitudinalMomentum ε hε hbar).adjoint.graph at hg
    rw [LinearPMap.isSelfAdjoint_def.mp (longitudinal_selfAdjoint ε hε hbar hh)] at hg
    exact hg

theorem momentum_domain_fourier_iff (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : Hilbert) :
    f ∈ (longitudinalMomentum ε hε hbar).domain ↔
      MemLp (fun k => (symbol hbar k:ℂ)*(coupledFourier ε hε f) k) 2 := by
  constructor
  · intro hf
    exact (Lp.memLp (coupledFourier ε hε (longitudinalMomentum ε hε hbar ⟨f,hf⟩))).ae_eq
      (momentum_fourier_coe ε hε hbar hh ⟨f,hf⟩)
  · intro hm
    let g := (coupledFourier ε hε).symm (hm.toLp _)
    apply LinearPMap.mem_domain_of_mem_graph (y := g)
    apply (momentum_graph_fourier_iff ε hε hbar hh f g).mpr
    change coupledFourier ε hε ((coupledFourier ε hε).symm (hm.toLp _)) =ᵐ[volume] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hm.coeFn_toLp

#print axioms clock_phase_derivative
#print axioms momentum_fourier_coe
#print axioms real_multiplier_inner
#print axioms momentum_graph_fourier_iff
#print axioms momentum_domain_fourier_iff

end
end UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier

/- The canonical clock translation generator has its physical derivative
and Fourier multiplier graph. This clock momentum is not the weighted
transverse momentum carrying a similar name in older energy modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates (fourier_toLp flatten_memLp)

def clockDerivative (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  fderiv ℝ f x ((1,0):Configuration)

theorem clock_graph_fourier (h : ℝ) (hh : h ≠ 0) (f g : Hilbert) :
    (f,g) ∈ (clockMomentum h).graph ↔
      fourierCoordinates g =ᵐ[volume] fun k => (symbol h k:ℂ)*(fourierCoordinates f) k := by
  have he := (KFCausalLongitudinalMomentumConjugacy.momentum_graph_conjugacy
    1 (by norm_num) h hh f g).trans
    (KFCausalLongitudinalFourierMultiplier.momentum_graph_fourier_iff 1 (by norm_num) h hh _ _)
  simpa only [KFCausalNoncompactFourierCoordinates.coupledFourier_coordinates] using he

theorem clock_derivative_fourier (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration))
    (hd : MemLp (clockDerivative f) 2 (volume : Measure Configuration))
    (hs : Differentiable ℝ f) :
    fourierCoordinates (hd.toLp (clockDerivative f)) =ᵐ[volume]
      fun k => (2*Real.pi*Complex.I)*(k 0:ℂ)*(fourierCoordinates (hf.toLp f)) k := by
  have hp (x : Space) : HasLineDerivAt ℝ (f ∘ split) ((clockDerivative f ∘ split) x)
      x clockVector := by
    have he := (hs (split x)).hasFDerivAt.hasLineDerivAt ((1,0):Configuration)
    change HasDerivAt (fun t : ℝ => f (split x+t • ((1,0):Configuration))) _ 0 at he
    change HasDerivAt (fun t : ℝ => f (split (x+t • clockVector))) _ 0
    simpa only [split_clock_add,KFCausalConfigurationTranslation.clockShift_apply,
      Prod.smul_mk,smul_eq_mul,mul_one,smul_zero,Prod.add_def,add_zero,clockDerivative] using he
  rw [fourier_toLp,fourier_toLp]
  have he := KFCausalL2DirectionalDerivative.derivative_fourier _ _ clockVector
    (flatten_memLp f hf) (flatten_memLp (clockDerivative f) hd) hp
  filter_upwards [he] with k hk
  rw [real_inner_comm,clockVector_inner] at hk
  exact hk

theorem clock_derivative_graph (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration))
    (hd : MemLp (clockDerivative f) 2 (volume : Measure Configuration))
    (hs : Differentiable ℝ f) :
    (hf.toLp f,(-Complex.I*(h:ℂ)) • hd.toLp (clockDerivative f)) ∈ (clockMomentum h).graph := by
  apply (clock_graph_fourier h hh _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (fourierCoordinates (hd.toLp (clockDerivative f))),clock_derivative_fourier f hf hd hs]
    with k hk he
  rw [hk]
  simp only [Pi.smul_apply,smul_eq_mul,he,symbol,Complex.ofReal_mul,Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I*Complex.I)*(2*(Real.pi:ℂ)*(h:ℂ)*
      (k 0:ℂ)*(fourierCoordinates (hf.toLp f)) k) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem compact_clock_memLp (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (clockDerivative f) 2 (volume : Measure Configuration) :=
  ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ ((1,0):Configuration))

theorem compact_clock_domain (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (hf.continuous.memLp_of_hasCompactSupport hc).toLp f ∈ (clockMomentum h).domain :=
  LinearPMap.mem_domain_of_mem_graph (clock_derivative_graph h hh f _
    (compact_clock_memLp f hf hc) (hf.differentiable (by norm_num)))

#print axioms clock_graph_fourier
#print axioms clock_derivative_fourier
#print axioms clock_derivative_graph
#print axioms compact_clock_memLp
#print axioms compact_clock_domain

end
end UnifiedTheory.Audit.KFCausalCanonicalClockDerivative

/- A physical L2 differential expression belongs to the actual maximal
longitudinal momentum graph. The proof uses the exact coordinate unitary
and the proved L2 directional Fourier derivative theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative
import UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
import UnifiedTheory.Audit.KFCausalL2DirectionalDerivative
import UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation (clockShift)
open UnifiedTheory.Audit.KFCausalClockFloorFlow
open UnifiedTheory.Audit.KFCausalClockFloorTestPullback (weight weight_ne_zero)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport (inverse_shift_coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier coupledFourier_apply)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol momentum_graph_fourier_iff)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates (fourier_toLp flatten_memLp)

def differential (ε : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  (rate ε x.1:ℂ)*f x+fderiv ℝ f x (coupledVelocity ε x)

theorem inverse_shift (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (t : ℝ)
    (x : Configuration) :
    inverseFunction ε hε f (clockShift t x) =
      (weight ε ((coordinateHomeomorph ε hε).symm x))⁻¹*
        expression ε hε t f ((coordinateHomeomorph ε hε).symm x) := by
  have hi := inverse_shift_coordinates ε hε t ((coordinateHomeomorph ε hε).symm x)
  rw [Homeomorph.apply_symm_apply] at hi
  unfold inverseFunction
  rw [hi]
  simp only [expression,densityRatio,weight,coupledFlow,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
  simp only [← mul_assoc,inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr (KFCausalClockFloorChargeTrialBridge.amplitude_positive ε _ hε).ne'),one_mul]

theorem inverse_clock_derivative (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : Differentiable ℝ f) (x : Configuration) :
    HasDerivAt (fun t => inverseFunction ε hε f (clockShift t x))
      (inverseFunction ε hε (differential ε f) x) 0 := by
  have hd := (expression_derivative ε hε f ((coordinateHomeomorph ε hε).symm x)
    _ (hf _).hasFDerivAt).const_mul (weight ε ((coordinateHomeomorph ε hε).symm x))⁻¹
  simpa only [← inverse_shift,inverseFunction,differential] using hd

theorem differential_fourier (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) (hd : MemLp (differential ε f) 2 (volume : Measure Configuration)) (hs : Differentiable ℝ f) :
    coupledFourier ε hε (hd.toLp (differential ε f)) =ᵐ[volume]
      fun k => (2*Real.pi*Complex.I)*(k 0:ℂ)*(coupledFourier ε hε (hf.toLp f)) k := by
  have hp (x : Space) : HasLineDerivAt ℝ (inverseFunction ε hε f ∘ split)
      ((inverseFunction ε hε (differential ε f) ∘ split) x) x clockVector := by
    change HasDerivAt (fun t : ℝ => inverseFunction ε hε f (split (x+t • clockVector))) _ 0
    simpa only [split_clock_add] using inverse_clock_derivative ε hε f hs (split x)
  simp only [coupledFourier_apply,coordinates_inverse_toLp,fourier_toLp]
  have he := KFCausalL2DirectionalDerivative.derivative_fourier _ _ clockVector
    (flatten_memLp _ (inverse_memLp ε hε f hf))
    (flatten_memLp _ (inverse_memLp ε hε (differential ε f) hd)) hp
  filter_upwards [he] with k hk
  rw [real_inner_comm,clockVector_inner] at hk
  exact hk

theorem differential_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration)) (hd : MemLp (differential ε f) 2 (volume : Measure Configuration))
    (hs : Differentiable ℝ f) :
    (hf.toLp f,(-Complex.I*(h:ℂ)) • hd.toLp (differential ε f)) ∈
      (longitudinalMomentum ε hε h).graph := by
  apply (momentum_graph_fourier_iff ε hε h hh _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (coupledFourier ε hε (hd.toLp (differential ε f))),differential_fourier ε hε f hf hd hs]
    with k hk he
  rw [hk]
  simp only [Pi.smul_apply,smul_eq_mul,he,symbol,Complex.ofReal_mul,Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I*Complex.I)*(2*(Real.pi:ℂ)*(h:ℂ)*
      (k 0:ℂ)*(coupledFourier ε hε (hf.toLp f)) k) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem differential_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration)) (hd : MemLp (differential ε f) 2 (volume : Measure Configuration))
    (hs : Differentiable ℝ f) :
    hf.toLp f ∈ (longitudinalMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (differential_graph ε hε h hh f hf hd hs)

theorem differential_continuous (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (differential ε f) := by
  have hr : Continuous (fun x : Configuration => rate ε x.1) := by
    unfold rate
    fun_prop (disch := intro x; positivity)
  have hv0 : Continuous (fun x : Configuration => KFCausalTransverseDilationFlow.velocity x.2) := by
    apply continuous_pi
    intro i
    unfold KFCausalTransverseDilationFlow.velocity
    split_ifs <;> fun_prop
  have hb : Continuous (fun x : Configuration => (Real.exp x.1+ε)⁻¹) := by
    fun_prop (disch := intro x; positivity)
  have hv : Continuous (coupledVelocity ε) := hb.prodMk (hb.smul hv0)
  exact (Complex.continuous_ofReal.comp hr |>.mul hf.continuous).add
    ((hf.continuous_fderiv (by norm_num)).clm_apply hv)

theorem differential_compact (ε : ℝ) (f : Configuration → ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (differential ε f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp only [differential,hzero,hd,mul_zero,ContinuousLinearMap.zero_apply,add_zero])

theorem compact_differential_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    MemLp (differential ε f) 2 (volume : Measure Configuration) :=
  (differential_continuous ε hε f hf).memLp_of_hasCompactSupport (differential_compact ε f hc)

theorem compact_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (hf.continuous.memLp_of_hasCompactSupport hc).toLp f ∈ (longitudinalMomentum ε hε h).domain :=
  differential_domain ε hε h hh f _ (compact_differential_memLp ε hε f hf hc)
    (hf.differentiable (by norm_num))

#print axioms inverse_shift
#print axioms inverse_clock_derivative
#print axioms differential_fourier
#print axioms differential_graph
#print axioms differential_domain
#print axioms differential_continuous
#print axioms differential_compact
#print axioms compact_differential_memLp
#print axioms compact_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum

/- Physical differential graph of the constructed selfadjoint pure-clock
momentum. L2 hypotheses suffice, and all of them are derived for C1 compact
states. No evolved-state regularity is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
import UnifiedTheory.Audit.KFCausalL2DirectionalDerivative
import UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation (clockShift)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates (fourier_toLp flatten_memLp)

def pureFourier (ε : ℝ) (hε : 0 < ε) : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  (coordinates ε hε).symm.trans fourierCoordinates

theorem pureFourier_apply (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    pureFourier ε hε f = fourierCoordinates ((coordinates ε hε).symm f) := rfl

theorem differential_fourier (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) (hd : MemLp (differential ε f) 2 (volume : Measure Configuration)) (hs : Differentiable ℝ f) :
    pureFourier ε hε (hd.toLp (differential ε f)) =ᵐ[volume]
      fun k => (2*Real.pi*Complex.I)*(k 0:ℂ)*(pureFourier ε hε (hf.toLp f)) k := by
  have hp (x : Space) : HasLineDerivAt ℝ (inverseFunction ε hε f ∘ split)
      ((inverseFunction ε hε (differential ε f) ∘ split) x) x clockVector := by
    change HasDerivAt (fun t : ℝ => inverseFunction ε hε f (split (x+t • clockVector))) _ 0
    simpa only [split_clock_add] using inverse_clock_derivative ε hε f hs (split x)
  simp only [pureFourier_apply,coordinates_inverse_toLp,fourier_toLp]
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
      (pureMomentum ε hε h).graph := by
  apply (graph_fourier ε hε h hh _ _).mpr
  change pureFourier ε hε ((-Complex.I*(h:ℂ)) • hd.toLp (differential ε f)) =ᵐ[volume]
    fun k => (symbol h k:ℂ)*(pureFourier ε hε (hf.toLp f)) k
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (pureFourier ε hε (hd.toLp (differential ε f))),differential_fourier ε hε f hf hd hs]
    with k hk he
  rw [hk]
  simp only [Pi.smul_apply,smul_eq_mul,he,symbol,Complex.ofReal_mul,Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I*Complex.I)*(2*(Real.pi:ℂ)*(h:ℂ)*
      (k 0:ℂ)*(pureFourier ε hε (hf.toLp f)) k) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem differential_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration)) (hd : MemLp (differential ε f) 2 (volume : Measure Configuration))
    (hs : Differentiable ℝ f) :
    hf.toLp f ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (differential_graph ε hε h hh f hf hd hs)

theorem differential_continuous (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (differential ε f) := by
  have hr : Continuous (fun x : Configuration => rate ε x.1) := by
    unfold rate clock
    fun_prop (disch := intro x; positivity)
  have hb : Continuous (fun x : Configuration => (clock ε x.1)⁻¹) := by
    unfold clock
    fun_prop (disch := intro x; positivity)
  simpa only [differential,clockDerivative,Complex.ofReal_inv,Function.comp_def,Pi.mul_apply,Pi.add_apply] using
    (((Complex.continuous_ofReal.comp hb).mul
      ((hf.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : Configuration => ((1,0):Configuration))))).add
        ((Complex.continuous_ofReal.comp hr).mul hf.continuous))

theorem differential_compact (ε : ℝ) (f : Configuration → ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (differential ε f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hd := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp only [differential,clockDerivative,hzero,hd,mul_zero,ContinuousLinearMap.zero_apply,add_zero])

theorem compact_differential_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    MemLp (differential ε f) 2 (volume : Measure Configuration) :=
  (differential_continuous ε hε f hf).memLp_of_hasCompactSupport (differential_compact ε f hc)

theorem compact_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (hf.continuous.memLp_of_hasCompactSupport hc).toLp f ∈ (pureMomentum ε hε h).domain :=
  differential_domain ε hε h hh f _ (compact_differential_memLp ε hε f hf hc)
    (hf.differentiable (by norm_num))

#print axioms differential_fourier
#print axioms differential_graph
#print axioms differential_domain
#print axioms differential_continuous
#print axioms differential_compact
#print axioms compact_differential_memLp
#print axioms compact_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential

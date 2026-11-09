/- The actual maximal canonical and longitudinal momenta have both
compositions on C2 compactly supported states. Their commutator is identified
with bounded response/remainder operators, with a quantitative relative
bound. This does not identify a Hamiltonian exponential-form commutator. -/
import UnifiedTheory.Audit.KFCausalClockFloorDifferentialCommutator
import UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumCommutator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialCommutator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse

theorem compact_composition_graphs (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    let state : Hilbert := (hf.continuous.memLp_of_hasCompactSupport hc).toLp f
    ∃ l p pl lp : Hilbert,
      (state,l) ∈ (longitudinalMomentum ε hε h).graph ∧
      (state,p) ∈ (clockMomentum h).graph ∧
      (l,pl) ∈ (clockMomentum h).graph ∧
      (p,lp) ∈ (longitudinalMomentum ε hε h).graph ∧
      l =ᵐ[volume] (fun x => (-Complex.I*(h:ℂ))*differential ε f x) ∧
      pl =ᵐ[volume] (fun x => (-Complex.I*(h:ℂ))^2*clockDerivative (differential ε f) x) ∧
      lp =ᵐ[volume] (fun x => (-Complex.I*(h:ℂ))^2*differential ε (clockDerivative f) x) := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let hA := compact_differential_memLp ε hε f hf1 hc
  let hP := compact_clock_memLp f hf1 hc
  let hPA := compact_clock_memLp (differential ε f) (differential_contDiff ε hε f hf)
    (differential_compact ε f hc)
  let hAP := compact_differential_memLp ε hε (clockDerivative f) (clockDerivative_contDiff f hf)
    (hc.fderiv_apply ℝ ((1,0):Configuration))
  let c : ℂ := -Complex.I*(h:ℂ)
  let l : Hilbert := c • hA.toLp (differential ε f)
  let p : Hilbert := c • hP.toLp (clockDerivative f)
  let pl : Hilbert := c • (c • hPA.toLp (clockDerivative (differential ε f)))
  let lp : Hilbert := c • (c • hAP.toLp (differential ε (clockDerivative f)))
  have hlg : (hm.toLp f,l) ∈ (longitudinalMomentum ε hε h).graph :=
    differential_graph ε hε h hh f hm hA (hf.differentiable (by norm_num))
  have hpg : (hm.toLp f,p) ∈ (clockMomentum h).graph :=
    clock_derivative_graph h hh f hm hP (hf.differentiable (by norm_num))
  have hplg : (l,pl) ∈ (clockMomentum h).graph :=
    (clockMomentum h).graph.smul_mem c (clock_derivative_graph h hh (differential ε f) hA hPA
      ((differential_contDiff ε hε f hf).differentiable (by norm_num)))
  have hlpg : (p,lp) ∈ (longitudinalMomentum ε hε h).graph :=
    (longitudinalMomentum ε hε h).graph.smul_mem c
      (differential_graph ε hε h hh (clockDerivative f) hP hAP
        ((clockDerivative_contDiff f hf).differentiable (by norm_num)))
  refine ⟨l,p,pl,lp,hlg,hpg,hplg,hlpg,?_,?_,?_⟩
  · filter_upwards [Lp.coeFn_smul c (hA.toLp (differential ε f)),hA.coeFn_toLp] with x hs hx
    change (c • hA.toLp (differential ε f)) x = _
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,c]
  · change c • (c • hPA.toLp (clockDerivative (differential ε f))) =ᵐ[volume] _
    rw [smul_smul]
    filter_upwards [Lp.coeFn_smul (c*c) (hPA.toLp (clockDerivative (differential ε f))),hPA.coeFn_toLp]
      with x hs hx
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,c,pow_two]
  · change c • (c • hAP.toLp (differential ε (clockDerivative f))) =ᵐ[volume] _
    rw [smul_smul]
    filter_upwards [Lp.coeFn_smul (c*c) (hAP.toLp (differential ε (clockDerivative f))),hAP.coeFn_toLp]
      with x hs hx
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul,hx,c,pow_two]

def commutatorValue (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f l : Hilbert) : Hilbert :=
  (Complex.I*(h:ℂ)) • responseOperator ε hε l+((h^2:ℝ):ℂ) • remainderOperator ε hε f

theorem commutatorValue_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f l : Hilbert) :
    ‖commutatorValue ε hε h f l‖ ≤ |h| * ‖l‖+(h^2/(8*ε))*‖f‖ := by
  have hr := mul_le_mul_of_nonneg_left (responseOperator_norm ε hε l) (abs_nonneg h)
  have he := mul_le_mul_of_nonneg_left (remainderOperator_norm ε hε f) (sq_nonneg h)
  unfold commutatorValue
  apply (norm_add_le _ _).trans
  simp only [norm_smul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg h)]
  exact (add_le_add hr he).trans_eq (by ring)

theorem compact_commutator (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    let state : Hilbert := (hf.continuous.memLp_of_hasCompactSupport hc).toLp f
    ∃ l p pl lp rl : Hilbert,
      (state,l) ∈ (longitudinalMomentum ε hε h).graph ∧
      (state,p) ∈ (clockMomentum h).graph ∧
      (l,pl) ∈ (clockMomentum h).graph ∧
      (p,lp) ∈ (longitudinalMomentum ε hε h).graph ∧
      (responseOperator ε hε state,rl) ∈ (longitudinalMomentum ε hε h).graph ∧
      pl-lp = commutatorValue ε hε h state l ∧
      pl-lp = (Complex.I*(h:ℂ)/2) • (responseOperator ε hε l+rl) ∧
      ‖pl-lp‖ ≤ |h| * ‖l‖+(h^2/(8*ε))*‖state‖ := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  let state : Hilbert := hm.toLp f
  obtain ⟨l,p,pl,lp,hlg,hpg,hplg,hlpg,hl,hpl,hlp⟩ := compact_composition_graphs ε hε h hh f hf hc
  let rl := responseOperator ε hε l-(2*Complex.I*(h:ℂ)) • remainderOperator ε hε state
  have hrl : (responseOperator ε hε state,rl) ∈ (longitudinalMomentum ε hε h).graph :=
    response_graph ε hε h state l hlg
  have he : pl-lp = commutatorValue ε hε h state l := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub pl lp,hpl,hlp,
      Lp.coeFn_add ((Complex.I*(h:ℂ)) • responseOperator ε hε l)
        (((h^2:ℝ):ℂ) • remainderOperator ε hε state),
      Lp.coeFn_smul (Complex.I*(h:ℂ)) (responseOperator ε hε l),
      Lp.coeFn_smul ((h^2:ℝ):ℂ) (remainderOperator ε hε state),
      responseOperator_coe ε hε l,remainderOperator_coe ε hε state,hl,hm.coeFn_toLp]
      with x hs hpl' hlp' ha hr he' hR hE hl' hf'
    change (pl-lp) x = ((Complex.I*(h:ℂ)) • responseOperator ε hε l+
      ((h^2:ℝ):ℂ) • remainderOperator ε hε state) x
    rw [hs,ha]
    simp only [Pi.sub_apply,Pi.add_apply,hr,he',Pi.smul_apply,smul_eq_mul,hpl',hlp',hR,hE,hl']
    change state x = f x at hf'
    rw [hf']
    have hd := differential_commutator ε hε f hf x
    push_cast
    linear_combination (norm := ring_nf) -(h:ℂ)^2*hd
    rw [Complex.I_sq]
    ring
  refine ⟨l,p,pl,lp,rl,hlg,hpg,hplg,hlpg,hrl,he,?_,?_⟩
  · rw [he]
    unfold commutatorValue rl
    simp only [smul_add,smul_sub,smul_smul]
    have ha : (Complex.I*(h:ℂ)/2)+(Complex.I*(h:ℂ)/2) = Complex.I*(h:ℂ) := by ring
    have hb : -(Complex.I*(h:ℂ)/2*(2*Complex.I*(h:ℂ))) = ((h^2:ℝ):ℂ) := by
      push_cast
      calc
        _ = -(Complex.I*Complex.I)*(h:ℂ)^2 := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [← add_sub_assoc,← add_smul,ha,sub_eq_add_neg,← neg_smul,hb]
  · rw [he]
    exact commutatorValue_norm ε hε h state l

#print axioms compact_composition_graphs
#print axioms commutatorValue_norm
#print axioms compact_commutator

end
end UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumCommutator

/- All-domain cross-estimate for the time-weighted maximal radial operator
and the residual static-plus-potential Hamiltonian on the full Hamiltonian
domain. Passing the bounded radial Yosida pairing to the strong limit controls
both separate outputs by the full Hamiltonian norm plus the uniform clock-floor
Leibniz defect. -/
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrongLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialCrossEstimate
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorHamiltonianRadialDomination (radial_domain)
open KFCausalClockFloorHamiltonianRadialSum (radialOutput residualOutput residual_graph)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t

theorem radial_pairing (x : (H).domain) :
    Real.exp (2*t)*‖radialOutput ε hε h hh hb m g k t x‖^2 ≤
      (inner ℂ (H x) (radialOutput ε hε h hh hb m g k t x)).re+
        (h^2/ε^2)*‖(x:Hilbert)‖^2 := by
  have ht := KFCausalClockFloorRadialYosidaStrongLimit.domain_tendsto ε hε h
    ⟨(x:Hilbert),radial_domain ε hε h hh hb m g k t x⟩
  have hl : Tendsto (fun n : ℕ =>
      Real.exp (2*t)*‖action ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert)‖^2)
      atTop (𝓝 (Real.exp (2*t)*‖radialOutput ε hε h hh hb m g k t x‖^2)) :=
    (ht.norm.pow 2).const_mul (Real.exp (2*t))
  have hr : Tendsto (fun n : ℕ =>
      (inner ℂ (H x) (action ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert))).re+
        (h^2/ε^2)*‖(x:Hilbert)‖^2)
      atTop (𝓝 ((inner ℂ (H x) (radialOutput ε hε h hh hb m g k t x)).re+
        (h^2/ε^2)*‖(x:Hilbert)‖^2)) :=
    (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner ht)).add_const _
  exact le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun n =>
      KFCausalClockFloorRadialYosidaHamiltonianPairing.hamiltonian_cutoff_pairing
        ε hε h hh hb m g k ((n:ℝ)+1) (by positivity) t x))

theorem residual_radial_pairing (x : (H).domain) :
    -(h^2/ε^2)*‖(x:Hilbert)‖^2 ≤
      (inner ℂ (residualOutput ε hε h hh hb m g k t x)
        (radialOutput ε hε h hh hb m g k t x)).re := by
  have hp := radial_pairing ε hε h hh hb m g k t x
  rw [residualOutput,inner_sub_left,inner_smul_left,Complex.conj_ofReal,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,inner_self_eq_norm_sq_to_K]
  change -(h^2/ε^2)*‖(x:Hilbert)‖^2 ≤
    (inner ℂ (H x) (radialOutput ε hε h hh hb m g k t x)).re-
      Real.exp (2*t)*((‖radialOutput ε hε h hh hb m g k t x‖:ℂ)^2).re
  rw [← Complex.ofReal_pow,Complex.ofReal_re]
  linarith

theorem split_norm_square (x : (H).domain) :
    Real.exp (4*t)*‖radialOutput ε hε h hh hb m g k t x‖^2+
      ‖residualOutput ε hε h hh hb m g k t x‖^2 ≤
        ‖H x‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖(x:Hilbert)‖^2 := by
  have hp := radial_pairing ε hε h hh hb m g k t x
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*Real.exp (2*t) by positivity)
  have he : Real.exp (2*t)^2=Real.exp (4*t) := by
    rw [sq,← Real.exp_add,show 2*t+2*t=4*t by ring]
  have hn : ‖(Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x‖^2=
      Real.exp (4*t)*‖radialOutput ε hε h hh hb m g k t x‖^2 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (2*t)),mul_pow,he]
  have hi : (inner ℂ (H x) ((Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x)).re=
      Real.exp (2*t)*(inner ℂ (H x) (radialOutput ε hε h hh hb m g k t x)).re := by
    rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [residualOutput,norm_sub_sq (𝕜 := ℂ)]
  change Real.exp (4*t)*‖radialOutput ε hε h hh hb m g k t x‖^2+
    (‖H x‖^2-2*(inner ℂ (H x) ((Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x)).re+
      ‖(Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x‖^2) ≤
    ‖H x‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖(x:Hilbert)‖^2
  rw [hn,hi,← he]
  linarith

theorem residual_norm_square (x : (H).domain) :
    ‖residualOutput ε hε h hh hb m g k t x‖^2 ≤
      ‖H x‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖(x:Hilbert)‖^2 := by
  have hs := split_norm_square ε hε h hh hb m g k t x
  have hr : 0 ≤ Real.exp (4*t)*‖radialOutput ε hε h hh hb m g k t x‖^2 := by positivity
  linarith

theorem residual_norm (x : (H).domain) :
    ‖residualOutput ε hε h hh hb m g k t x‖ ≤
      ‖H x‖+Real.sqrt 2*Real.exp t*(|h| /ε)*‖(x:Hilbert)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hs := residual_norm_square ε hε h hh hb m g k t x
  have he : Real.exp t^2=Real.exp (2*t) := by
    rw [sq,← Real.exp_add,show t+t=2*t by ring]
  have h2 : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hd : (|h| /ε)^2=h^2/ε^2 := by rw [div_pow,sq_abs]
  have hsq : (Real.sqrt 2*Real.exp t*(|h| /ε)*‖(x:Hilbert)‖)^2=
      2*Real.exp (2*t)*(h^2/ε^2)*‖(x:Hilbert)‖^2 := by
    rw [mul_pow,mul_pow,mul_pow,h2,he,hd]
  have hcross : 0 ≤ 2*‖H x‖*(Real.sqrt 2*Real.exp t*(|h| /ε)*‖(x:Hilbert)‖) := by positivity
  nlinarith only [hs,hsq,hcross]

theorem graph_radial_pairing (f h_out r_out : Hilbert)
    (hh_g : (f,h_out) ∈ (H).graph) (hr_g : (f,r_out) ∈ (K).graph) :
    Real.exp (2*t)*‖r_out‖^2 ≤ (inner ℂ h_out r_out).re+(h^2/ε^2)*‖f‖^2 := by
  let x : (H).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hh_g⟩
  have hH : H x=h_out := (H).mem_graph_snd_inj' ((H).mem_graph x) hh_g rfl
  have hK : radialOutput ε hε h hh hb m g k t x=r_out :=
    (K).mem_graph_snd_inj' ((K).mem_graph _) hr_g rfl
  have hp := radial_pairing ε hε h hh hb m g k t x
  simpa only [hH,hK] using hp

theorem graph_residual_radial_pairing (f h_out r_out s_out : Hilbert)
    (hh_g : (f,h_out) ∈ (H).graph) (hr_g : (f,r_out) ∈ (K).graph)
    (hs_g : (f,s_out) ∈ (S).graph) :
    -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ s_out r_out).re ∧
      Real.exp (4*t)*‖r_out‖^2+‖s_out‖^2 ≤
        ‖h_out‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  let x : (H).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hh_g⟩
  have hH : H x=h_out := (H).mem_graph_snd_inj' ((H).mem_graph x) hh_g rfl
  have hK : radialOutput ε hε h hh hb m g k t x=r_out :=
    (K).mem_graph_snd_inj' ((K).mem_graph _) hr_g rfl
  have hS : residualOutput ε hε h hh hb m g k t x=s_out :=
    (S).mem_graph_snd_inj' (residual_graph ε hε h hh hb m g k t x) hs_g rfl
  have hp := residual_radial_pairing ε hε h hh hb m g k t x
  have hs := split_norm_square ε hε h hh hb m g k t x
  exact ⟨by simpa only [hK,hS] using hp,by simpa only [hH,hK,hS] using hs⟩

#print axioms radial_pairing
#print axioms residual_radial_pairing
#print axioms split_norm_square
#print axioms residual_norm_square
#print axioms residual_norm
#print axioms graph_radial_pairing
#print axioms graph_residual_radial_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialCrossEstimate

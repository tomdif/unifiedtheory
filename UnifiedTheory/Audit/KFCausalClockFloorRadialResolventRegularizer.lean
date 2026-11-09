/- The complement of the actual radial Yosida multiplier is an ambient
regularizer. It maps every Hilbert vector into the full maximal radial
operator domain, with its genuine output equal to the existing Yosida
action, and converges strongly to the identity. No static or potential
domain, source-core property, or residual reconstruction is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDomain
import UnifiedTheory.Audit.KFCausalDominatedRepresentedL2Limit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRegularizer
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_nonnegative symbol)
open KFCausalClockFloorRadialYosidaDomain (operator symbol_tendsto)

def multiplier (ε h N : ℝ) (x : Joint 2 4) : ℝ := N/(N+radial ε h x)

def action (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N) : Hilbert →L[ℂ] Hilbert :=
  ContinuousLinearMap.id ℂ Hilbert-
    (N⁻¹:ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN

theorem multiplier_complement (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (x : Joint 2 4) : 1-N⁻¹*symbol ε h N x=multiplier ε h N x := by
  have hd : N+radial ε h x ≠ 0 :=
    (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h x)).ne'
  unfold multiplier symbol
  field_simp
  ring

theorem multiplier_nonnegative (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (x : Joint 2 4) : 0≤multiplier ε h N x :=
  div_nonneg hN.le (add_nonneg hN.le (radial_nonnegative ε hε h x))

theorem multiplier_le_one (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (x : Joint 2 4) : multiplier ε h N x≤1 := by
  unfold multiplier
  apply (div_le_one (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h x))).mpr
  linarith [radial_nonnegative ε hε h x]

theorem action_coe (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N) (f : Hilbert) :
    chargeCoordinates (action ε hε h N hN f)=ᵐ[volume]
      fun x=>(multiplier ε h N x:ℂ)*(chargeCoordinates f) x := by
  have he : chargeCoordinates (action ε hε h N hN f)=
      chargeCoordinates f-(N⁻¹:ℂ) • chargeCoordinates
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) := by
    simp only [action,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply,map_sub,map_smul]
  rw [he]
  filter_upwards [Lp.coeFn_sub (chargeCoordinates f) ((N⁻¹:ℂ) • chargeCoordinates
      (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f)),
    Lp.coeFn_smul (N⁻¹:ℂ) (chargeCoordinates
      (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f)),
    KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN f]
    with x hs hm hy
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hm]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hy,←multiplier_complement ε hε h N hN x]
  simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_inv]
  ring

theorem action_norm (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N) (f : Hilbert) :
    ‖action ε hε h N hN f‖≤‖f‖ := by
  have hn : ‖chargeCoordinates (action ε hε h N hN f)‖≤1*‖chargeCoordinates f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [action_coe ε hε h N hN f] with x hx
    rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (multiplier_nonnegative ε hε h N hN x)]
    exact mul_le_mul_of_nonneg_right (multiplier_le_one ε hε h N hN x) (norm_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map,one_mul] using hn

theorem radial_graph (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N) (f : Hilbert) :
    (action ε hε h N hN f,KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) ∈
      (operator ε hε h).graph := by
  apply (KFCausalUnitaryRealMultiplier.realPullback_graph chargeCoordinates (radial ε h) _ _ _).mpr
  filter_upwards [action_coe ε hε h N hN f,
    KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN f] with x hx hy
  rw [hy,hx,←mul_assoc,←Complex.ofReal_mul]
  congr 2
  unfold symbol multiplier
  ring

theorem radial_domain (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N) (f : Hilbert) :
    action ε hε h N hN f ∈ (operator ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (radial_graph ε hε h N hN f)

theorem sequence_tendsto (ε : ℝ) (hε : 0<ε) (h : ℝ) (f : Hilbert) :
    Tendsto (fun n : ℕ=>action ε hε h ((n:ℝ)+1) (by positivity) f) atTop (𝓝 f) := by
  have hi : Tendsto (fun n : ℕ=>((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hm (x : Joint 2 4) :
      Tendsto (fun n : ℕ=>multiplier ε h ((n:ℝ)+1) x) atTop (𝓝 1) := by
    have he := (tendsto_const_nhds (x:=(1:ℝ))).sub (hi.mul (symbol_tendsto ε hε h x))
    have he' : Tendsto (fun n : ℕ=>1-((n:ℝ)+1)⁻¹*symbol ε h ((n:ℝ)+1) x)
        atTop (𝓝 1) := by simpa only [zero_mul,sub_zero] using he
    apply he'.congr'
    exact Eventually.of_forall (fun n=>multiplier_complement ε hε h _ (by positivity) x)
  have ht := KFCausalDominatedRepresentedL2Limit.represented_tendsto
    (fun n : ℕ=>chargeCoordinates (action ε hε h ((n:ℝ)+1) (by positivity) f))
    (fun n x=>(multiplier ε h ((n:ℝ)+1) x:ℂ)*(chargeCoordinates f) x)
    (chargeCoordinates f) (Lp.memLp _) (fun x=>‖(chargeCoordinates f) x‖) (Lp.memLp _).norm
    (Eventually.of_forall (fun n=>action_coe ε hε h _ (by positivity) f))
    (Eventually.of_forall (fun n=>Eventually.of_forall (fun x=>by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (multiplier_nonnegative ε hε h _ (by positivity) x),norm_norm]
      exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_le_one ε hε h _ (by positivity) x))))
    (Eventually.of_forall (fun x=>by
      simpa only [Complex.ofReal_one,one_mul] using
        ((Complex.continuous_ofReal.tendsto 1).comp (hm x)).mul_const ((chargeCoordinates f) x)))
  have ht' : Tendsto (fun n : ℕ=>chargeCoordinates (action ε hε h ((n:ℝ)+1) (by positivity) f))
      atTop (𝓝 (chargeCoordinates f)) := by simpa only [Lp.toLp_coeFn] using ht
  have he := (chargeCoordinates.symm.continuous.tendsto (chargeCoordinates f)).comp ht'
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using he

#print axioms multiplier_complement
#print axioms multiplier_nonnegative
#print axioms multiplier_le_one
#print axioms action_coe
#print axioms action_norm
#print axioms radial_graph
#print axioms radial_domain
#print axioms sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRegularizer

/- The radial resolvent regularizer retains the actual shifted ordered
outputs. Strong convergence is proved in the physical Hilbert space
from the genuine complex-strip representatives.
This supplies approximation data, not a residual-form reconstruction. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRegularizer
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOrderedTransport
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShifted
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open KFCausalClockFloorRadialResolventRegularizer (action)
open KFCausalClockFloorRadialYosidaOrderedTransport (family family_line_continuous family_bound shift_bound)
open KFCausalClockFloorRadialYosidaStrip (cutoff)
open KFCausalMixedStripExponentialGraph (unitary)
open KFCausalClockFloorDefectCoordinates (straightening)

@[irreducible] def coordinates (ε : ℝ) (hε : 0<ε) : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert := (unitary ε hε).trans (straightening ε hε)

private theorem coordinates_apply (ε : ℝ) (hε : 0<ε) (f : Hilbert) :
    coordinates ε hε f=straightening ε hε (unitary ε hε f) := by
  unfold coordinates
  rfl

def shifted (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (y : ℝ) (hy : |y|≤Real.pi*ε/6) : Hilbert →L[ℂ] Hilbert :=
  ContinuousLinearMap.id ℂ Hilbert-(N⁻¹:ℂ) •
    KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy

def line (ε h N y : ℝ) (x : Space) : ℂ :=
  1-(N⁻¹:ℂ)*KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x

private theorem complement_coe (E : Hilbert ≃ₗᵢ[ℂ] FrequencyHilbert)
    (A : Hilbert →L[ℂ] Hilbert) (m : Space → ℂ) (c : ℂ) (f : Hilbert)
    (hA : E (A f)=ᵐ[volume] fun x=>m x*(E f) x) :
    E ((ContinuousLinearMap.id ℂ Hilbert-c • A) f)=ᵐ[volume]
      fun x=>(1-c*m x)*(E f) x := by
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,map_sub,map_smul]
  filter_upwards [hA,Lp.coeFn_sub (E f) (c • E (A f)),
    Lp.coeFn_smul c (E (A f))] with x hm hs hc
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hm]
  ring

theorem shifted_coe (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (y : ℝ) (hy : |y|≤Real.pi*ε/6) (f : Hilbert) :
    coordinates ε hε (shifted ε hε h N hN y hy f)=ᵐ[volume]
      fun x=>line ε h N y x*(coordinates ε hε f) x := by
  have ha := KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N)
    (Real.pi*ε/6) N (family_line_continuous ε hε h N hN) hN.le
    (family_bound ε hε h N hN) y hy f
  change straightening ε hε (unitary ε hε
    (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy f))=ᵐ[volume]
    fun x=>KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x*
      (straightening ε hε (unitary ε hε f)) x at ha
  have ha' : coordinates ε hε
      (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy f)=ᵐ[volume]
      fun x=>KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x*(coordinates ε hε f) x := by
    simpa only [coordinates_apply] using ha
  unfold shifted line
  exact complement_coe (coordinates ε hε)
    (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy)
    (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y) (N⁻¹:ℂ) f ha'

theorem line_bound (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (y : ℝ) (hy : |y|≤Real.pi*ε/6) (x : Space) : ‖line ε h N y x‖≤2 := by
  have hb := KFCausalStripFamilyExponentialGraph.symbol_bound (family ε h N)
    (Real.pi*ε/6) N (family_bound ε hε h N hN) y hy x
  have hn : ‖(N⁻¹:ℂ)‖=N⁻¹ := by simp [norm_inv,abs_of_pos hN]
  calc
    ‖line ε h N y x‖ ≤ ‖(1:ℂ)‖+‖(N⁻¹:ℂ)‖*
        ‖KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x‖ := by
      simpa only [line,norm_mul] using norm_sub_le (1:ℂ) ((N⁻¹:ℂ)*KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x)
    _ ≤ 1+N⁻¹*N := by rw [norm_one,hn]; gcongr
    _ = 2 := by rw [inv_mul_cancel₀ hN.ne']; norm_num

theorem shifted_norm (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (y : ℝ) (hy : |y|≤Real.pi*ε/6) (f : Hilbert) :
    ‖shifted ε hε h N hN y hy f‖≤2*‖f‖ := by
  have hn : ‖coordinates ε hε (shifted ε hε h N hN y hy f)‖≤2*‖coordinates ε hε f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [shifted_coe ε hε h N hN y hy f] with x hx
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right (line_bound ε hε h N hN y hy x) (norm_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map] using hn

theorem action_charge (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (hh : h≠0) (θ : ℝ) (f : Hilbert) :
    action ε hε h N hN (KFCausalPhysicalCircleAction.action h hh θ f)=
      KFCausalPhysicalCircleAction.action h hh θ (action ε hε h N hN f) := by
  simp only [KFCausalClockFloorRadialResolventRegularizer.action,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smul_apply,map_sub,map_smul,
    KFCausalClockFloorRadialYosidaSymbol.action_charge ε hε h N hN hh θ f]

private theorem cutoff_complement_tendsto (z : ℂ) :
    Tendsto (fun n : ℕ=>1-((((n:ℝ)+1)⁻¹:ℝ):ℂ)*cutoff ((n:ℝ)+1) z)
      atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ=>((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hic := (Complex.continuous_ofReal.tendsto 0).comp hi
  have hc : Tendsto (fun n : ℕ=>1+((((n:ℝ)+1)⁻¹:ℝ):ℂ)*z) atTop (𝓝 (1:ℂ)) := by
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
      (tendsto_const_nhds (x:=(1:ℂ))).add (hic.mul_const z)
  have ht : Tendsto (fun n : ℕ=>1/(1+((((n:ℝ)+1)⁻¹:ℝ):ℂ)*z)) atTop (𝓝 (1:ℂ)) := by
    simpa only [div_one] using (tendsto_const_nhds (x:=(1:ℂ))).div hc one_ne_zero
  apply ht.congr'
  filter_upwards [hc.eventually_ne (show (1:ℂ)≠0 from one_ne_zero)] with n hn
  have hN : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hd : ((((n:ℝ)+1:ℝ):ℂ)+z) ≠ 0 := by
    intro he
    apply hn
    rw [Complex.ofReal_inv]
    field_simp [hN]
    simpa only [mul_zero] using he
  unfold cutoff
  rw [Complex.ofReal_inv]
  field_simp [hN,hd]
  ring

theorem shifted_sequence_tendsto (ε : ℝ) (hε : 0<ε) (h y : ℝ)
    (hy : |y|≤Real.pi*ε/6) (f : Hilbert) :
    Tendsto (fun n : ℕ=>shifted ε hε h ((n:ℝ)+1) (by positivity) y hy f) atTop (𝓝 f) := by
  have hm (x : Space) : Tendsto (fun n : ℕ=>line ε h ((n:ℝ)+1) y x) atTop (𝓝 1) :=
    by
      unfold line KFCausalStripFamilyExponentialGraph.symbol family
        KFCausalClockFloorRadialYosidaStrip.multiplier
      simpa only [Complex.ofReal_inv] using cutoff_complement_tendsto _
  have ht := KFCausalDominatedRepresentedL2Limit.represented_tendsto
    (fun n : ℕ=>coordinates ε hε (shifted ε hε h ((n:ℝ)+1) (by positivity) y hy f))
    (fun n x=>line ε h ((n:ℝ)+1) y x*(coordinates ε hε f) x)
    (coordinates ε hε f) (Lp.memLp _) (fun x=>2*‖(coordinates ε hε f) x‖)
    ((Lp.memLp _).norm.const_mul 2)
    (Eventually.of_forall (fun n=>shifted_coe ε hε h _ (by positivity) y hy f))
    (Eventually.of_forall (fun n=>Eventually.of_forall (fun x=>by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (line_bound ε hε h _ (by positivity) y hy x) (norm_nonneg _))))
    (Eventually.of_forall (fun x=>by simpa only [one_mul] using (hm x).mul_const ((coordinates ε hε f) x)))
  have ht' : Tendsto (fun n : ℕ=>coordinates ε hε
      (shifted ε hε h ((n:ℝ)+1) (by positivity) y hy f)) atTop (𝓝 (coordinates ε hε f)) := by
    simpa only [Lp.toLp_coeFn] using ht
  have he := ((coordinates ε hε).symm.continuous.tendsto (coordinates ε hε f)).comp ht'
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using he

#print axioms shifted_coe
#print axioms line_bound
#print axioms shifted_norm
#print axioms action_charge
#print axioms shifted_sequence_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShifted

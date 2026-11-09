/- Canonical clock momentum reconstructed from the physical longitudinal
expression, its clock weight, and the transverse shear derivative. The
required weighted L2 and shear control are explicit; evolution does not
supply them in this module. -/
import UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (velocity)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response response_bounds clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (rate coupledVelocity_split)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum longitudinalMomentum)

def shearDerivative (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  fderiv ℝ f x ((0,velocity x.2):Configuration)+f x

def weightedDifferential (ε : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  (clock ε x.1:ℂ)*differential ε f x

def correction (ε : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  (response ε x.1/2:ℂ)*f x

theorem derivative_reconstruction (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (x : Configuration) :
    clockDerivative f x = weightedDifferential ε f x-shearDerivative f x+correction ε f x := by
  have hc : ((Real.exp x.1+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  unfold clockDerivative weightedDifferential differential shearDerivative correction
  rw [coupledVelocity_split,map_add,map_smul,map_smul]
  simp only [rate,clock,response,Complex.real_smul]
  push_cast at hc ⊢
  field_simp [hc]
  ring

theorem correction_bound (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (x : Configuration) :
    ‖correction ε f x‖ ≤ (1/2:ℝ)*‖f x‖ := by
  have hb := response_bounds ε x.1 hε
  simp only [correction,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat]
  rw [abs_of_pos hb.1]
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem correction_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) : MemLp (correction ε f) 2 := by
  have hm : Measurable (fun x : Configuration => (response ε x.1/2:ℂ)) := by
    unfold response clock
    fun_prop
  exact hf.of_le_mul (hm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall (correction_bound ε hε f))

theorem correction_norm (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) :
    ‖(correction_memLp ε hε f hf).toLp (correction ε f)‖ ≤ (1/2:ℝ)*‖hf.toLp f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(correction_memLp ε hε f hf).coeFn_toLp,hf.coeFn_toLp] with x hx hy
  rw [hx,hy]
  exact correction_bound ε hε f x

theorem differential_memLp_of_weighted (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration)) :
    MemLp (differential ε f) 2 := by
  have he : differential ε f = fun x => (clock ε x.1:ℂ)⁻¹*weightedDifferential ε f x := by
    funext x
    simp only [weightedDifferential,← mul_assoc,inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε.le).ne'),one_mul]
  rw [he]
  have hm : Measurable (fun x : Configuration => (clock ε x.1:ℂ)⁻¹) := by unfold clock; fun_prop
  apply hw.of_le_mul (hm.aestronglyMeasurable.mul hw.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Pi.mul_apply,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (clock_positive ε x.1 hε.le)]
  exact mul_le_mul_of_nonneg_right
    (inv_anti₀ hε (KFCausalClockFloorFlow.clock_above_floor ε x.1).le) (norm_nonneg _)

theorem clock_memLp_of_controls (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) :
    MemLp (clockDerivative f) 2 := by
  apply ((hw.sub hs).add (correction_memLp ε hε f hf)).ae_eq
  filter_upwards [] with x
  exact (derivative_reconstruction ε hε f x).symm

theorem clock_toLp_reconstruction (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) :
    (clock_memLp_of_controls ε hε f hf hw hs).toLp (clockDerivative f) =
      hw.toLp (weightedDifferential ε f)-hs.toLp (shearDerivative f)+
        (correction_memLp ε hε f hf).toLp (correction ε f) := by
  apply Lp.ext
  filter_upwards [(clock_memLp_of_controls ε hε f hf hw hs).coeFn_toLp,
    Lp.coeFn_add (hw.toLp (weightedDifferential ε f)-hs.toLp (shearDerivative f))
      ((correction_memLp ε hε f hf).toLp (correction ε f)),
    Lp.coeFn_sub (hw.toLp (weightedDifferential ε f)) (hs.toLp (shearDerivative f)),
    hw.coeFn_toLp,hs.coeFn_toLp,(correction_memLp ε hε f hf).coeFn_toLp] with x hx ha hd hw' hs' hc
  rw [hx,ha]
  simp only [Pi.add_apply,Pi.sub_apply,hd,hw',hs',hc]
  exact derivative_reconstruction ε hε f x

theorem clock_graph_controls (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) (hd : Differentiable ℝ f) :
    (hf.toLp f,(-Complex.I*(h:ℂ)) • (hw.toLp (weightedDifferential ε f)-hs.toLp (shearDerivative f)+
      (correction_memLp ε hε f hf).toLp (correction ε f))) ∈ (clockMomentum h).graph := by
  have he := clock_derivative_graph h hh f hf (clock_memLp_of_controls ε hε f hf hw hs) hd
  rw [clock_toLp_reconstruction ε hε f hf hw hs] at he
  exact he

theorem longitudinal_graph_controls (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration)) (hd : Differentiable ℝ f) :
    (hf.toLp f,(-Complex.I*(h:ℂ)) • (differential_memLp_of_weighted ε hε f hw).toLp (differential ε f)) ∈
      (longitudinalMomentum ε hε h).graph :=
  differential_graph ε hε h hh f hf (differential_memLp_of_weighted ε hε f hw) hd

theorem weighted_output_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration)) (hd : Differentiable ℝ f)
    (g : Hilbert) (hg : (hf.toLp f,g) ∈ (longitudinalMomentum ε hε h).graph) :
    (-Complex.I*(h:ℂ)) • hw.toLp (weightedDifferential ε f) =ᵐ[volume]
      fun x => (clock ε x.1:ℂ)*g x := by
  have he := (longitudinalMomentum ε hε h).mem_graph_snd_inj' hg
    (longitudinal_graph_controls ε hε h hh f hf hw hd) rfl
  dsimp only at he
  rw [he]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hw.toLp (weightedDifferential ε f)),
    Lp.coeFn_smul (-Complex.I*(h:ℂ)) ((differential_memLp_of_weighted ε hε f hw).toLp (differential ε f)),
    hw.coeFn_toLp,(differential_memLp_of_weighted ε hε f hw).coeFn_toLp] with x hw' hd' hwc hdc
  rw [hw',hd']
  simp only [Pi.smul_apply,smul_eq_mul,hwc,hdc,weightedDifferential]
  ring

theorem canonical_norm_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration))
    (hw : MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) (hd : Differentiable ℝ f)
    (g : Hilbert) (hg : (hf.toLp f,g) ∈ (clockMomentum h).graph) :
    ‖g‖ ≤ ‖(-Complex.I*(h:ℂ)) • hw.toLp (weightedDifferential ε f)‖+
      ‖(-Complex.I*(h:ℂ)) • hs.toLp (shearDerivative f)‖+|h|/2*‖hf.toLp f‖ := by
  have he := (clockMomentum h).mem_graph_snd_inj' hg
    (clock_graph_controls ε hε h hh f hf hw hs hd) rfl
  dsimp only at he
  rw [he,smul_add,smul_sub]
  have hc := mul_le_mul_of_nonneg_left (correction_norm ε hε f hf) (abs_nonneg h)
  have hn : ‖(-Complex.I*(h:ℂ)) • (correction_memLp ε hε f hf).toLp (correction ε f)‖ ≤
      |h|/2*‖hf.toLp f‖ := by
    simpa only [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      ← mul_assoc,mul_one_div] using hc
  exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) hn)

#print axioms derivative_reconstruction
#print axioms correction_bound
#print axioms correction_memLp
#print axioms correction_norm
#print axioms differential_memLp_of_weighted
#print axioms clock_memLp_of_controls
#print axioms clock_toLp_reconstruction
#print axioms clock_graph_controls
#print axioms longitudinal_graph_controls
#print axioms weighted_output_coe
#print axioms canonical_norm_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction

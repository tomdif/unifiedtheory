/- Continuous actual L2 outputs for bounded source curves after the
complex longitudinal shift. Fixed field multipliers are controlled by
an integrable half-width Gaussian, including the neutral shear. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (configurationLine configurationLine_memLp gaussianState)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates (grouping)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction coordinates_toLp_coe)

def baseLine (ε a α β y : ℝ) : Configuration → ℂ :=
  KFCausalClockFloorShiftedOutput.configurationLine ε a (α/2) (β/2) y

def modifiedLine (ε a α β y : ℝ) (m : Configuration → ℂ) (C : ℂ) (p : ℝ)
    (b : Fin 5 → ℂ) (x : Configuration) : ℂ := m x*(C*configurationLine ε a α β p b y x)

theorem modifiedLine_bound (ε a α β y : ℝ) (hε : 0 < ε) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (C : ℂ) (p : ℝ)
    (b : Fin 5 → ℂ) (x : Configuration) :
    ‖modifiedLine ε a α β y m C p b x‖ ≤
      (‖C‖*envelopeConstant α β p b)*‖m x*baseLine ε a α β y x‖ := by
  have ht := mul_le_mul_of_nonneg_left (line_bound ε a α β p b y hε hα hβ hw hy (grouping x))
    (mul_nonneg (norm_nonneg (m x)) (norm_nonneg C))
  simpa only [modifiedLine,configurationLine,baseLine,KFCausalClockFloorShiftedOutput.configurationLine,
    norm_mul,mul_assoc,mul_comm,mul_left_comm] using ht

theorem modifiedLine_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ)
    (hm : AEStronglyMeasurable m volume) (hbase : MemLp (fun x => m x*baseLine ε a α β y x) 2)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) : MemLp (modifiedLine ε a α β y m C p b) 2 := by
  have hl := configurationLine_memLp ε a α β p b y hε ha hα hβ hw hy
  apply (hbase.const_mul ((‖C‖*envelopeConstant α β p b : ℝ):ℂ)).of_le
    (hm.mul (hl.const_mul C).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖modifiedLine ε a α β y m C p b x‖ ≤
    ‖((‖C‖*envelopeConstant α β p b : ℝ):ℂ)*(m x*baseLine ε a α β y x)‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg C)
      (show 0 ≤ envelopeConstant α β p b from (Real.exp_pos _).le))]
  exact modifiedLine_bound ε a α β y hε hα hβ hw hy m C p b x

theorem uniform_modifiedLine_bound (ε a α β y P B : ℝ) (hε : 0 < ε) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ) (C : ℂ) (p : ℝ)
    (b : Fin 5 → ℂ) (hC : ‖C‖ ≤ 1) (hp : |p| ≤ P) (hb : sourceSize b ≤ B) (x : Configuration) :
    ‖modifiedLine ε a α β y m C p b x‖ ≤
      Real.exp (P*Real.pi/3+B*positionConstant α β/2)*‖m x*baseLine ε a α β y x‖ := by
  have hl : ‖C*configurationLine ε a α β p b y x‖ ≤
      Real.exp (P*Real.pi/3+B*positionConstant α β/2)*‖baseLine ε a α β y x‖ := by
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right hC (norm_nonneg _)).trans
    rw [one_mul]
    exact uniform_line_bound ε a α β p P B b y hε hα hβ hw hy hp hb (grouping x)
  simpa only [modifiedLine,norm_mul,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_left hl (norm_nonneg (m x))

theorem modifiedLine_curve_continuous (ε a α β y P B : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a α β y x) 2)
    (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hb : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ => (modifiedLine_memLp ε a α β y hε ha hα hβ hw hy m hm hbase (C θ) (p θ) (b θ)).toLp
      (modifiedLine ε a α β y m (C θ) (p θ) (b θ))) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _
    (fun x => (Real.exp (P*Real.pi/3+B*positionConstant α β/2):ℂ)*(m x*baseLine ε a α β y x))
    (hbase.const_mul _)
  · intro θ
    filter_upwards [] with x
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      uniform_modifiedLine_bound ε a α β y P B hε hα hβ hw hy m (C θ) (p θ) (b θ) (hC θ) (hp θ) (hb θ) x
  · filter_upwards [] with x
    unfold modifiedLine configurationLine line trial coherentPacket source clockPhase
    fun_prop

def outputState (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ)
    (hm : AEStronglyMeasurable m volume) (hbase : MemLp (fun x => m x*baseLine ε a α β y x) 2)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) : Hilbert :=
  coordinates ε hε ((modifiedLine_memLp ε a α β y hε ha hα hβ hw hy m hm hbase C p b).toLp
    (modifiedLine ε a α β y m C p b))

theorem outputState_coe (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (m : Configuration → ℂ)
    (hm : AEStronglyMeasurable m volume) (hbase : MemLp (fun x => m x*baseLine ε a α β y x) 2)
    (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    outputState ε a α β y hε ha hα hβ hw hy m hm hbase C p b =ᵐ[volume]
      weightedFunction ε hε (modifiedLine ε a α β y m C p b) := coordinates_toLp_coe ε hε _ _

#print axioms modifiedLine_bound
#print axioms modifiedLine_memLp
#print axioms uniform_modifiedLine_bound
#print axioms modifiedLine_curve_continuous
#print axioms outputState_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity

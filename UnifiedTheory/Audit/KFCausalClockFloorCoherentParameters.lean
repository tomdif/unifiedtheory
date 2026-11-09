/- Exact source norms and uniform analytic bounds along the physical
charge-circle orbit. The ground-width matching fixes the normalization. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates (displacement spectatorParameter)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeModulationFlow

theorem coefficients_size (α : ℝ) (v : Block 2) (r : Block 4) :
    sourceSize (coefficients α v r) =
      4*α^2*((v 0)^2+(v 1)^2)+4*Real.pi^2*((r 1)^2+(r 2)^2+(r 3)^2) := by
  simp only [sourceSize,Fin.sum_univ_succ,coefficients]
  dsimp
  simp only [Complex.sq_norm,Complex.normSq_apply]
  simp [Complex.mul_re,Complex.mul_im]
  ring_nf
  rw [scale_square]
  ring

theorem groundWidth_scale_square (hbar : ℝ) (hh : hbar ≠ 0) :
    (groundWidth hbar)^2*(momentumScale hbar)^2 = Real.pi^2 := by
  have hm := (div_eq_iff (groundWidth_positive hbar hh).ne').mp (groundWidth_matching hbar hh)
  nlinarith [hm]

theorem parameter_square (k : Joint 2 4) :
    ‖k‖^2 = (k (.inl 0))^2+(k (.inl 1))^2+(k (.inr 0))^2+
      (k (.inr 1))^2+(k (.inr 2))^2+(k (.inr 3))^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fintype.sum_sum_type,Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]
  ring

theorem sourceCoefficients_size (hbar : ℝ) (hh : hbar ≠ 0) (k : Joint 2 4) :
    sourceSize (sourceCoefficients hbar k) = 4*Real.pi^2*(‖k‖^2-(k (.inr 0))^2) := by
  rw [sourceCoefficients,coefficients_size,parameter_square]
  simp only [displacement,spectatorParameter,split_fst,split_snd,dilate]
  calc
    _ = 4*((groundWidth hbar)^2*(momentumScale hbar)^2)*((k (.inl 0))^2+(k (.inl 1))^2)+
        4*Real.pi^2*((k (.inr 1))^2+(k (.inr 2))^2+(k (.inr 3))^2) := by ring
    _ = _ := by rw [groundWidth_scale_square hbar hh]; ring

theorem sourceCoefficients_bound (hbar : ℝ) (hh : hbar ≠ 0) (k : Joint 2 4) :
    sourceSize (sourceCoefficients hbar k) ≤ 4*Real.pi^2*‖k‖^2 := by
  rw [sourceCoefficients_size hbar hh]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)

theorem clockFrequency_bound (k : Joint 2 4) : |clockFrequency k| ≤ 2*Real.pi*‖k‖ := by
  change |2*Real.pi*k (.inr 0)| ≤ _
  rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le k (.inr 0)) (by positivity)

theorem clockFrequency_parameter (θ : ℝ) (k : Joint 2 4) :
    clockFrequency (parameter θ k) = clockFrequency k := rfl

theorem sourceCoefficients_parameter (hbar : ℝ) (hh : hbar ≠ 0) (θ : ℝ) (k : Joint 2 4) :
    sourceSize (sourceCoefficients hbar (parameter θ k)) = sourceSize (sourceCoefficients hbar k) := by
  rw [sourceCoefficients_size hbar hh,sourceCoefficients_size hbar hh,parameter_norm]
  rfl

theorem amplitudeConstant_bound (hbar : ℝ) (hh : hbar ≠ 0) (k : Joint 2 4) :
    ‖amplitudeConstant hbar k‖ ≤ 1 :=
  constant_norm_le_one _ (groundWidth_positive hbar hh).le _

theorem orbit_line_bound (ε a hbar : ℝ) (hε : 0 < ε) (hh : hbar ≠ 0)
    (θ : ℝ) (k : Joint 2 4) (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (w : ℝ × Grouped) :
    ‖amplitudeConstant hbar (parameter θ k)*
      line ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency (parameter θ k))
        (sourceCoefficients hbar (parameter θ k)) y w‖ ≤
      Real.exp ((2*Real.pi*‖k‖)*Real.pi/3+
        (4*Real.pi^2*‖k‖^2)*positionConstant (groundWidth hbar) (neutralWidth hbar)/2)*
      ‖KFCausalClockFloorFullGaussian.line ε a (groundWidth hbar/2) (neutralWidth hbar/2) y w‖ := by
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right (amplitudeConstant_bound hbar hh _) (norm_nonneg _)).trans
  rw [one_mul]
  refine uniform_line_bound ε a _ _ _ (2*Real.pi*‖k‖) (4*Real.pi^2*‖k‖^2) _ y hε
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hy ?_ ?_ w
  · rw [clockFrequency_parameter]
    exact clockFrequency_bound k
  · rw [sourceCoefficients_parameter hbar hh]
    exact sourceCoefficients_bound hbar hh k

#print axioms coefficients_size
#print axioms groundWidth_scale_square
#print axioms parameter_square
#print axioms sourceCoefficients_size
#print axioms sourceCoefficients_bound
#print axioms clockFrequency_bound
#print axioms clockFrequency_parameter
#print axioms sourceCoefficients_parameter
#print axioms amplitudeConstant_bound
#print axioms orbit_line_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters

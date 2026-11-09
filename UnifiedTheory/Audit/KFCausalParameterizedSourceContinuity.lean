/- Jointly parameterized physical Gaussian and derivative outputs are
continuous in L2 under uniform source bounds. This includes the pair of
charge and source-circle angles needed for polynomial coefficient means. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity
import UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalParameterizedSourceContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity
  (coordinateProfile coordinateProfile_memLp physicalProfile_derivative_toLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
  (widths physicalGaussian_coordinate_memLp physicalGaussian_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity
  (baseLine modifiedLine modifiedLine_memLp uniform_modifiedLine_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (configurationLine)

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem profile_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : X → ℂ) (p : X → ℝ) (b : X → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hb : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ =>
      (physicalProfile_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg).toLp
        (physicalProfile (C θ) (p θ) α β (b θ) g)) := by
  let G : Configuration → ℂ := fun x => (Real.exp (B*positionConstant α β/2):ℂ)*
    (g x.1*physicalGaussian (α/2) (β/2) x.2)
  have hG : MemLp G 2 volume :=
    (configuration_product_memLp _ _ hg (physicalGaussian_memLp _ _ (by positivity) (by positivity))).const_mul _
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _ G hG
  · intro θ
    filter_upwards [] with x
    simpa only [G,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      physicalProfile_bound (C θ) (p θ) α β B hα hβ hw (b θ) g (hC θ) (hb θ) x
  · filter_upwards [] with x
    unfold physicalProfile clockMultiplier sourcedPacket linearSource clockPhase
    fun_prop

theorem coordinate_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : X → ℂ) (p : X → ℝ) (b : X → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hb : ∀ θ, sourceSize (b θ) ≤ B) (i : Fin 5) :
    Continuous (fun θ =>
      (coordinateProfile_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg i).toLp
        (coordinateProfile (C θ) (p θ) α β (b θ) g i)) := by
  let G : Configuration → ℂ := fun x => (Real.exp (B*positionConstant α β/2):ℂ)*
    (g x.1*((x.2 i:ℂ)*physicalGaussian (α/2) (β/2) x.2))
  have hG : MemLp G 2 volume :=
    (configuration_product_memLp _ _ hg
      (physicalGaussian_coordinate_memLp _ _ (by positivity) (by positivity) i)).const_mul _
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _ G hG
  · intro θ
    filter_upwards [] with x
    have hb' := mul_le_mul_of_nonneg_left
      (physicalProfile_bound (C θ) (p θ) α β B hα hβ hw (b θ) g (hC θ) (hb θ) x)
      (norm_nonneg (x.2 i:ℂ))
    simpa only [coordinateProfile,G,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_assoc,mul_left_comm,mul_comm] using hb'
  · filter_upwards [] with x
    unfold coordinateProfile physicalProfile clockMultiplier sourcedPacket linearSource clockPhase
    fun_prop

theorem derivative_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : X → ℂ) (p : X → ℝ) (b : X → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hb : ∀ θ, sourceSize (b θ) ≤ B) (v : Transverse) :
    Continuous (fun θ =>
      (physicalProfile_derivative_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg v).toLp
        (derivative v (physicalProfile (C θ) (p θ) α β (b θ) g))) := by
  have he : (fun θ =>
      (physicalProfile_derivative_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg v).toLp
        (derivative v (physicalProfile (C θ) (p θ) α β (b θ) g))) =
      (fun θ => linearSource (b θ) v •
        (physicalProfile_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg).toLp
          (physicalProfile (C θ) (p θ) α β (b θ) g)+
        ∑ i : Fin 5, ((-2*widths α β i*v i:ℝ):ℂ) •
          (coordinateProfile_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg i).toLp
            (coordinateProfile (C θ) (p θ) α β (b θ) g i)) :=
    funext (fun θ => physicalProfile_derivative_toLp (C θ) (p θ) α β hα hβ hw (b θ) g hg v)
  rw [he]
  apply Continuous.add
  · have hL : Continuous (fun θ => linearSource (b θ) v) := by unfold linearSource; fun_prop
    exact hL.smul (profile_continuous α β B hα hβ hw C p b g hg hCc hpc hbc hC hb)
  · apply continuous_finset_sum
    intro i _
    exact continuous_const.smul
      (coordinate_continuous α β B hα hβ hw C p b g hg hCc hpc hbc hC hb i)

theorem shiftedLine_continuous (ε a α β y P B : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a α β y x) 2)
    (C : X → ℂ) (p : X → ℝ) (b : X → Fin 5 → ℂ)
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

#print axioms profile_continuous
#print axioms coordinate_continuous
#print axioms derivative_continuous
#print axioms shiftedLine_continuous
end
end UnifiedTheory.Audit.KFCausalParameterizedSourceContinuity

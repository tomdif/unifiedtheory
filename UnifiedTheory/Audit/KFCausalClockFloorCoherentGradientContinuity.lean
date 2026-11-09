/- Coordinate moments and derivative outputs of physical sourced profiles
vary continuously in L2 along bounded continuous source curves. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths physicalGaussian_coordinate_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)

def coordinateProfile (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (i : Fin 5) (x : Configuration) : ℂ := (x.2 i:ℂ)*physicalProfile C p α β b g x

theorem coordinateProfile_memLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (i : Fin 5) :
    MemLp (coordinateProfile C p α β b g i) 2 volume := by
  have hm := configuration_product_memLp _ _ (clockMultiplier_memLp C p g hg)
    (sourcedPacket_coordinate_memLp α β hα hβ hw b i)
  convert hm using 1
  funext x
  unfold coordinateProfile physicalProfile
  ring

theorem coordinateProfile_curve_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
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

theorem physicalProfile_derivative_expansion (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (v : Transverse) :
    derivative v (physicalProfile C p α β b g) =
      linearSource b v • physicalProfile C p α β b g+
        ∑ i : Fin 5, ((-2*widths α β i*v i:ℝ):ℂ) • coordinateProfile C p α β b g i := by
  funext x
  rw [physicalProfile_derivative]
  simp only [gradient,mul_add,Finset.mul_sum,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,
    coordinateProfile,physicalProfile]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem physicalProfile_derivative_toLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (v : Transverse) :
    (physicalProfile_derivative_memLp C p α β hα hβ hw b g hg v).toLp
      (derivative v (physicalProfile C p α β b g)) =
      linearSource b v • (physicalProfile_memLp C p α β hα hβ hw b g hg).toLp (physicalProfile C p α β b g)+
        ∑ i : Fin 5, ((-2*widths α β i*v i:ℝ):ℂ) •
          (coordinateProfile_memLp C p α β hα hβ hw b g hg i).toLp (coordinateProfile C p α β b g i) := by
  let R : Configuration → ℂ := linearSource b v • physicalProfile C p α β b g+
    ∑ i : Fin 5, ((-2*widths α β i*v i:ℝ):ℂ) • coordinateProfile C p α β b g i
  have hsum : MemLp (∑ i : Fin 5, ((-2*widths α β i*v i:ℝ):ℂ) • coordinateProfile C p α β b g i) 2 volume := by
    simpa only [Finset.sum_apply] using (memLp_finset_sum Finset.univ (fun i _ =>
      (coordinateProfile_memLp C p α β hα hβ hw b g hg i).const_smul ((-2*widths α β i*v i:ℝ):ℂ)))
  have hR : MemLp R 2 volume :=
    ((physicalProfile_memLp C p α β hα hβ hw b g hg).const_smul (linearSource b v)).add hsum
  calc
    _ = hR.toLp R := by
      apply Lp.ext
      filter_upwards [(physicalProfile_derivative_memLp C p α β hα hβ hw b g hg v).coeFn_toLp,
        hR.coeFn_toLp] with x hx hy
      rw [hx,hy]
      exact congrFun (physicalProfile_derivative_expansion C p α β b g v) x
    _ = _ := by rfl

theorem derivative_curve_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
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
    exact hL.smul (physicalProfile_curve_continuous α β B hα hβ hw C p b g hg hCc hpc hbc hC hb)
  · apply continuous_finset_sum
    intro i _
    exact continuous_const.smul
      (coordinateProfile_curve_continuous α β B hα hβ hw C p b g hg hCc hpc hbc hC hb i)

#print axioms coordinateProfile_memLp
#print axioms coordinateProfile_curve_continuous
#print axioms physicalProfile_derivative_expansion
#print axioms physicalProfile_derivative_toLp
#print axioms derivative_curve_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity

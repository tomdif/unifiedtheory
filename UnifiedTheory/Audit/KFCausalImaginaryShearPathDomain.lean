/- The concrete imaginary-shear path defines a continuous Hilbert-space
curve on the closed unit interval, and each vector has an actual shear
graph. Strong derivatives of this curve and its shear output, and the
charge-averaged endpoint cancellation, remain separate requirements. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)

abbrev Interval := Icc (0:ℝ) 1

variable (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
variable (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)

def state (t : Interval) : Hilbert :=
  (path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property).toLp (path A D α β b t)

theorem state_coe (t : Interval) :
    state A D hA hAm hD hDb α β hα hβ hw b t =ᵐ[volume] path A D α β b t :=
  (path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property).coeFn_toLp

theorem state_continuous : Continuous (state A D hA hAm hD hDb α β hα hβ hw b) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun t : Interval => path A D α β b t)
    (fun t => path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property)
    (envelope A α β b) (envelope_memLp A hAm α β hα hβ b)
  · intro t
    exact Filter.Eventually.of_forall (path_bound A D hDb α β hα hβ hw b t t.property)
  · filter_upwards [] with x
    have hc : Continuous (fun t : ℝ => path A D α β b t x) :=
      (show Differentiable ℝ (fun t : ℝ => path A D α β b t x) from
        fun t => (path_time_derivative A D α β b t x).differentiableAt).continuous
    exact hc.comp continuous_subtype_val

include hDb in
theorem timeScale_bound (t : Interval) (s : ℝ) :
    ‖timeScale D t s‖ ≤ Real.exp ((Real.pi/3)/2) := by
  have hz := scaled_bound (D s) (hDb s) t (by rw [abs_of_nonneg t.property.1]; exact t.property.2)
  exact KFCausalUniformShearGaussian.scale_bound _ _ ((Complex.re_le_norm _).trans hz)

include hA hAm hD hDb hα hβ hw in
theorem differential_memLp (t : Interval) :
    MemLp (shearDerivative (path A D α β b t)) 2 volume :=
  KFCausalRelativeGaussianShearDomain.profile_shear_memLp (timeScale D t)
    (timeScale_smooth D hD t).continuous _ (Real.exp_pos _).le (timeScale_bound D hDb t)
    (timeAmplitude A D t) (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t)
    α β b (path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property)
    (path_quadratic_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property)

def output (h : ℝ) (t : Interval) : Hilbert := (-Complex.I*(h:ℂ)) •
  (differential_memLp A D hA hAm hD hDb α β hα hβ hw b t).toLp
    (shearDerivative (path A D α β b t))

theorem state_graph (h : ℝ) (hh : h ≠ 0) (t : Interval) :
    (state A D hA hAm hD hDb α β hα hβ hw b t,
      output A D hA hAm hD hDb α β hα hβ hw b h t) ∈ (shearMomentum h).graph :=
  KFCausalShearMaximalDifferential.graph_of_shear_differential h hh _
    (path_smooth A D hA hD α β b t)
    (path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property)
    (differential_memLp A D hA hAm hD hDb α β hα hβ hw b t)

omit A D hA hAm hD hDb α β hα hβ hw b in
theorem displacement_strip_bound (ε h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) : ‖displacement ε h s‖ ≤ Real.pi/3 := by
  apply (displacement_bound ε h s hε hb).trans
  apply (div_le_iff₀ (by positivity : 0 < 2*ε)).mpr
  nlinarith

section Actual
variable (ε a p h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : |h| ≤ 2*Real.pi*ε/3)

def actualState (t : Interval) : Hilbert :=
  state (clockAmplitude ε a p (-h/2)) (displacement ε h)
    (clockAmplitude_smooth ε a p (-h/2) hε (half_shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (half_shift_bound ε h hb))
    (displacement_smooth ε h hε hb) (displacement_strip_bound ε h hε hb) α β hα hβ hw b t

theorem actualState_continuous : Continuous (actualState α β hα hβ hw b ε a p h hε ha hb) :=
  state_continuous (clockAmplitude ε a p (-h/2)) (displacement ε h)
    (clockAmplitude_smooth ε a p (-h/2) hε (half_shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (half_shift_bound ε h hb))
    (displacement_smooth ε h hε hb) (displacement_strip_bound ε h hε hb) α β hα hβ hw b

theorem actualState_coe (t : Interval) :
    actualState α β hα hβ hw b ε a p h hε ha hb t =ᵐ[volume]
      actualPath ε a α β p h b t := state_coe _ _ _ _ _ _ _ _ _ _ _ _ t

theorem actualState_one :
    actualState α β hα hβ hw b ε a p h hε ha hb ⟨1,by constructor <;> norm_num⟩ =
      KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2)
        hε ha hα hβ hw (half_shift_bound ε h hb) := by
  apply Lp.ext
  exact (actualState_coe α β hα hβ hw b ε a p h hε ha hb _).trans
    (actualPath_one_gaussian ε a α β p h b hε ha hα hβ hw hb).symm

theorem actualState_shear_domain (hh : h ≠ 0) (t : Interval) :
    actualState α β hα hβ hw b ε a p h hε ha hb t ∈ (shearMomentum h).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_graph (clockAmplitude ε a p (-h/2)) (displacement ε h)
    (clockAmplitude_smooth ε a p (-h/2) hε (half_shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (half_shift_bound ε h hb))
    (displacement_smooth ε h hε hb) (displacement_strip_bound ε h hε hb) α β hα hβ hw b h hh t)

end Actual

#print axioms state_coe
#print axioms state_continuous
#print axioms timeScale_bound
#print axioms differential_memLp
#print axioms state_graph
#print axioms displacement_strip_bound
#print axioms actualState_continuous
#print axioms actualState_coe
#print axioms actualState_one
#print axioms actualState_shear_domain
end
end UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain

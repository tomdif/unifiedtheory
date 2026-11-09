/- An actual L2 orbit over one normalized period. Its mean agrees with
the previously constructed unitary-group average. -/
import UnifiedTheory.Audit.KFCausalProbabilityL2Mean

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean

def angleMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance angle_probability : IsProbabilityMeasure angleMeasure where
  measure_univ := by simp [angleMeasure]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : StrongUnitaryGroup H) (T : ℝ)

theorem orbit_memLp (f : H) : MemLp (fun θ => U.action (T*θ) f) 2 angleMeasure :=
  MemLp.of_bound ((U.continuous_orbit f).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    ‖f‖ (Filter.Eventually.of_forall (fun θ => ((U.action (T*θ)).norm_map f).le))

def orbitState (f : H) : Lp H 2 angleMeasure :=
  (orbit_memLp U T f).toLp (fun θ => U.action (T*θ) f)

theorem orbitState_coe (f : H) : orbitState U T f =ᵐ[angleMeasure] fun θ => U.action (T*θ) f :=
  (orbit_memLp U T f).coeFn_toLp

theorem orbitState_add (f g : H) : orbitState U T (f+g) = orbitState U T f+orbitState U T g := by
  apply Lp.ext
  filter_upwards [orbitState_coe U T (f+g), orbitState_coe U T f,
    orbitState_coe U T g, Lp.coeFn_add (orbitState U T f) (orbitState U T g)] with θ hfg hf hg ha
  simp only [hfg, ha, Pi.add_apply, hf, hg, map_add]

theorem orbitState_smul (c : ℂ) (f : H) : orbitState U T (c • f) = c • orbitState U T f := by
  apply Lp.ext
  filter_upwards [orbitState_coe U T (c • f), orbitState_coe U T f,
    Lp.coeFn_smul c (orbitState U T f)] with θ hc hf hs
  simp only [hc, hs, Pi.smul_apply, hf, map_smul]

theorem orbitState_norm (f : H) : ‖orbitState U T f‖ = ‖f‖ := by
  have he : ∀ᵐ θ ∂angleMeasure, ‖orbitState U T f θ‖ = ‖(Lp.const 2 angleMeasure f) θ‖ := by
    filter_upwards [orbitState_coe U T f, Lp.coeFn_const 2 angleMeasure f] with θ ho hc
    rw [ho, hc]
    exact (U.action (T*θ)).norm_map f
  calc
    _ = ‖Lp.const 2 angleMeasure f‖ := by
      simp only [Lp.norm_def]
      rw [eLpNorm_congr_norm_ae he]
    _ = ‖f‖ := const_norm angleMeasure f

def orbit : H →ₗᵢ[ℂ] Lp H 2 angleMeasure where
  toFun := orbitState U T
  map_add' := orbitState_add U T
  map_smul' := orbitState_smul U T
  norm_map' := orbitState_norm U T

theorem orbit_mean [CompleteSpace H] (hT : T ≠ 0) (f : H) :
    mean angleMeasure (orbit U T f) = average U f T := by
  rw [mean_integral]
  change (∫ θ, orbitState U T f θ ∂angleMeasure) = _
  rw [integral_congr_ae (orbitState_coe U T f)]
  change (∫ θ in Set.Ioc 0 1, U.action (T*θ) f) = _
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left (fun θ => U.action θ f) hT]
  simp only [mul_zero, mul_one, average, primitive]

theorem orbit_fixed (f : H) (hf : f ∈ fixedSpace U) :
    orbit U T f = Lp.const 2 angleMeasure f := by
  apply Lp.ext
  filter_upwards [orbitState_coe U T f, Lp.coeFn_const 2 angleMeasure f] with θ ho hc
  exact ho.trans ((hf (T*θ)).trans hc.symm)

#print axioms angle_probability
#print axioms orbit_memLp
#print axioms orbitState_coe
#print axioms orbitState_add
#print axioms orbitState_smul
#print axioms orbitState_norm
#print axioms orbit_mean
#print axioms orbit_fixed

end
end UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

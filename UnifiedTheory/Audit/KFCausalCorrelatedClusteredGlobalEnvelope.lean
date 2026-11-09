/- A single transverse envelope for the entire clock axis and every
positive width spacing. Its constants depend on the finite profile.
This is absolute domination, not a relative bound uniform over states. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredResponseLimit
import UnifiedTheory.Audit.KFCausalChargedPairKernelGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredGlobalEnvelope
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredBounds
open KFCausalCorrelatedClusteredIntegrals
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargedPairCompactGeometry (region widthFloor widthFloor_positive)
open KFCausalNeutralPlaneClockGeometry (velocity)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)

variable {m : ℕ} (f : Family m)

def reweight (c : Fin m → ℂ) : Family m := { f with amplitude := fun i => f.amplitude i*c i }
def coefficientMass (c : Fin m → ℂ) : ℝ := ∑ i, ‖c i‖^2

theorem coefficientMass_nonnegative (c : Fin m → ℂ) : 0 ≤ coefficientMass c :=
  Finset.sum_nonneg (fun i _ => sq_nonneg ‖c i‖)

theorem blockBound_reweight (c : Fin m → ℂ) (k : ℕ) (α β : ℝ) (r v : ℂ) (p : Joint) :
    blockBound (reweight f c) k α β r v p ≤ coefficientMass c*blockBound f k α β r v p := by
  have hc (i : Fin m) : ‖c i‖^2 ≤ coefficientMass c :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖c j‖) (Finset.mem_univ i)
  have hB (i : Fin m) : 0 ≤ KFCausalClusteredClockEnvelope.componentBound
      (f.degree i) k α β r v (f.source i) (f.polynomial i) p := by
    unfold KFCausalClusteredClockEnvelope.componentBound KFCausalClusteredWidthDensityIntegrability.weight
      KFCausalJointPolynomialIntegrability.weight
    positivity
  unfold blockBound reweight
  dsimp only
  simp only [norm_mul,mul_pow]
  calc
    _ ≤ (m:ℝ)*∑ i, coefficientMass c*(‖f.amplitude i‖^2*
        KFCausalClusteredClockEnvelope.componentBound (f.degree i) k α β r v (f.source i) (f.polynomial i) p) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_left (hc i) (mul_nonneg (sq_nonneg ‖f.amplitude i‖) (hB i))]
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem fullBound_reweight (c : Fin m → ℂ) (α β : ℝ) (r v : ℂ) (p : Joint) :
    fullBound (reweight f c) α β r v p ≤ coefficientMass c*fullBound f α β r v p := by
  unfold fullBound
  have h0 := blockBound_reweight f c 0 α β r v p
  have h1 := blockBound_reweight f c 1 α β r v p
  have h2 := blockBound_reweight f c 2 α β r v p
  linarith

theorem global_envelope (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ ε y s : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → ∀ p, 0 ≤ p.2 →
        fullBound f α β (scale ε y s) (deriv (scale ε y) s) p ≤ D p := by
  let K := region α β
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (KFCausalChargedPairCompactGeometry.region_compact α β)
  let r : K → ℂ := fun x => x.val.2
  let v : K → ℂ := fun x => velocity (1-x.val.1) x.val.1 x.val.2
  have hr : Continuous r := continuous_snd.comp continuous_subtype_val
  have hv : Continuous v := continuous_iff_continuousAt.mpr (fun x =>
    (KFCausalChargedPairKernelGrowth.velocity_continuousAt α β x.val x.property).comp
      continuous_subtype_val.continuousAt)
  have ha (x : K) (_ : x ∈ (Set.univ : Set K)) :
      widthFloor α ≤ α*KFCausalReciprocalGaussianCoordinates.area (r x) := by
    have hc := x.property.2
    change widthFloor α ≤ α*((r x).re^2-(r x).im^2)-8*β*(r x).im^2 at hc
    unfold KFCausalReciprocalGaussianCoordinates.area
    nlinarith [mul_nonneg (show 0 ≤ 8*β by positivity) (sq_nonneg (r x).im)]
  have hc (x : K) (_ : x ∈ (Set.univ : Set K)) :
      widthFloor α ≤ α*KFCausalReciprocalGaussianCoordinates.area (r x)-8*β*(r x).im^2 := x.property.2
  obtain ⟨A,hAi,hA0,hA⟩ := blockBound_envelope f Set.univ isCompact_univ 0 α β (widthFloor α)
    r v hr hv hβ (widthFloor_positive α hα) ha hc
  obtain ⟨B,hBi,hB0,hB⟩ := blockBound_envelope f Set.univ isCompact_univ 1 α β (widthFloor α)
    r v hr hv hβ (widthFloor_positive α hα) ha hc
  obtain ⟨C,hCi,hC0,hC⟩ := blockBound_envelope f Set.univ isCompact_univ 2 α β (widthFloor α)
    r v hr hv hβ (widthFloor_positive α hα) ha hc
  refine ⟨fun p => A p+B p/2+C p/4,(hAi.add (hBi.div_const 2)).add (hCi.div_const 4),?_,?_⟩
  · intro p
    have := hA0 p; have := hB0 p; have := hC0 p
    positivity
  · intro ε y s hε hy p hp
    let x : K := ⟨(fraction ε s,scale ε y s),
      KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hw hε hy⟩
    have hd := (KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy).deriv
    rw [hd]
    exact add_le_add (add_le_add (hA x (Set.mem_univ _) p hp)
      (div_le_div_of_nonneg_right (hB x (Set.mem_univ _) p hp) (by norm_num)))
      (div_le_div_of_nonneg_right (hC x (Set.mem_univ _) p hp) (by norm_num))

#print axioms coefficientMass_nonnegative
#print axioms blockBound_reweight
#print axioms fullBound_reweight
#print axioms global_envelope
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredGlobalEnvelope

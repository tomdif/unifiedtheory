/- Exact symmetries of the raw Wilson kernel preserve the already constructed
full positive vacuum, stationary mass, and raw transition. No new ground
profile or uniform spectral bound is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnTail
import UnifiedTheory.Clay.YangMills.WilsonGroundTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonRawSymmetry
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonPhysicalVariance WilsonHighFieldDecay
open WilsonSingleLinkStaples (character character_continuous)

variable (n : ℕ) [NeZero n]

structure Symmetry where
  map : Slice n ≃ᵐ Slice n
  continuous_map : Continuous map
  continuous_inv : Continuous map.symm
  preserving : MeasurePreserving map (measure n) (measure n)
  invariant : ∀ (β : ℝ) (u v : Slice n),
    rawKernel character β 2 (map u) (map v) = rawKernel character β 2 u v

def inverse (S : Symmetry n) : Symmetry n where
  map := S.map.symm
  continuous_map := S.continuous_inv
  continuous_inv := S.continuous_map
  preserving := S.preserving.symm
  invariant β u v := by
    have h := S.invariant β (S.map.symm u) (S.map.symm v)
    simpa only [MeasurableEquiv.apply_symm_apply] using h.symm

def composition (S T : Symmetry n) : Symmetry n where
  map := S.map.trans T.map
  continuous_map := T.continuous_map.comp S.continuous_map
  continuous_inv := S.continuous_inv.comp T.continuous_inv
  preserving := T.preserving.comp S.preserving
  invariant β u v := (T.invariant β (S.map u) (S.map v)).trans (S.invariant β u v)

def pull (S : Symmetry n) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  ⟨fun u => f (S.map u), f.continuous.comp S.continuous_map⟩

theorem integral_pull (S : Symmetry n) (F : Slice n → ℝ) :
    (∫ u, F (S.map u) ∂measure n) = ∫ u, F u ∂measure n :=
  S.preserving.integral_comp' F

theorem ground_invariant (S : Symmetry n) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    ground n β hβ (S.map u) = ground n β hβ u := by
  let K : C(Slice n × Slice n, ℝ) :=
    ⟨fun uv => rawKernel character β 2 uv.1 uv.2, rawKernel_continuous _ character_continuous _ _⟩
  obtain ⟨a,ha,hfloor⟩ := KernelPartitionNorm.positive_floor K
    (fun uv => rawKernel_pos _ _ _ uv.1 uv.2)
  have hf (v : Slice n) : (∫ w, K (v,w) * pull n S (ground n β hβ) w ∂measure n) =
      ‖transfer n β‖ * pull n S (ground n β hβ) v := by
    have he := integral_pull n S (fun w =>
      rawKernel character β 2 (S.map v) w * ground n β hβ w)
    simp only [S.invariant] at he
    exact he.trans (ground_raw_equation n β hβ (S.map v))
  obtain ⟨c,hc⟩ := PositiveKernelRatio.real_top_proportional (measure n) K
    (ground n β hβ) (ground_pos n β hβ) ‖transfer n β‖ a (‖K‖+1)
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1 ha (by positivity)
    (fun v w => hfloor (v,w))
    (fun v w => (le_abs_self _).trans
      ((ContinuousMap.norm_coe_le_norm K (v,w)).trans (by linarith)))
    (ground_raw_equation n β hβ) (pull n S (ground n β hβ)) hf
  have hi : (∫ v, ground n β hβ v ∂measure n) =
      c * (∫ v, ground n β hβ v ∂measure n) := by
    calc
      _ = ∫ v, pull n S (ground n β hβ) v ∂measure n := (integral_pull n S _).symm
      _ = ∫ v, c * ground n β hβ v ∂measure n := integral_congr_ae (Filter.Eventually.of_forall hc)
      _ = _ := integral_const_mul _ _
  have hc1 : c = 1 := mul_right_cancel₀ (WilsonVacuumConvergence.overlap_pos n β hβ).ne'
    (by simpa using hi.symm)
  simpa only [pull, ContinuousMap.coe_mk, hc1, one_mul] using hc u

theorem mass_pull (S : Symmetry n) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β hβ (pull n S f) = mass n β hβ f := by
  rw [mass_ground, mass_ground]
  have h := integral_pull n S (fun u => (ground n β hβ u * f u) ^ 2)
  simpa only [ground_invariant, pull, ContinuousMap.coe_mk] using h

theorem step_pull (S : Symmetry n) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    step n β hβ (pull n S f) = pull n S (step n β hβ f) := by
  ext u
  apply mul_left_cancel₀ (ground_pos n β hβ u).ne'
  rw [ground_step]
  change _ = ground n β hβ u * step n β hβ f (S.map u)
  rw [← ground_invariant n S β hβ u, ground_step]
  congr 1
  have h := integral_pull n S (fun v =>
    rawKernel character β 2 (S.map u) v * ground n β hβ v * f v)
  simpa only [S.invariant, ground_invariant, pull, ContinuousMap.coe_mk] using h

theorem loss_pull (S : Symmetry n) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    loss n β hβ (pull n S f) = loss n β hβ f := by
  simp only [loss_mass, step_pull, mass_pull]

theorem pull_symm (S : Symmetry n) (f : C(Slice n, ℝ)) :
    pull n S (pull n (inverse n S) f) = f := by
  ext u
  exact congrArg f (S.map.symm_apply_apply u)

end
end UnifiedTheory.Clay.YangMills.WilsonRawSymmetry

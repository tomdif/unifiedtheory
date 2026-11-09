/- A nontrivial center twist of an actual periodic slice preserves every
plaquette and the original transfer kernel. Its winding loop is odd.
The normalized physical ground inherits this symmetry exactly. -/
import UnifiedTheory.Clay.YangMills.WilsonWindingLoop
import UnifiedTheory.Clay.YangMills.WilsonRawSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterTwist
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonWindingLoop
open WilsonSingleLinkStaples (character character_re)
open WilsonGroundLocalComparison WilsonGroundHeatBath WilsonPhysicalVariance

variable (n : ℕ)

def twist (i : Fin 3) (u : Slice n) : Slice n := seam n i (-1) * u

theorem twist_apply (i : Fin 3) (u : Slice n) (e : SpatialVertex n × Fin 3) :
    twist n i u e = if e.2 = i ∧ e.1 i = 0 then -u e else u e := by
  simp only [twist, Pi.mul_apply, seam]
  split_ifs <;> simp

theorem twist_involution (i : Fin 3) (u : Slice n) : twist n i (twist n i u) = u := by
  funext e
  simp only [twist_apply]
  split_ifs <;> simp

theorem twist_continuous (i : Fin 3) : Continuous (twist n i) :=
  continuous_const.mul continuous_id

theorem twist_gauge (i : Fin 3) (h : SliceGauge n Q) (u : Slice n) :
    twist n i (gaugeSlice h u) = gaugeSlice h (twist n i u) := by
  funext e
  simp only [twist_apply, gaugeSlice]
  split_ifs <;> simp

/-- Centrality makes the entire holonomy unchanged, not merely its trace. -/
theorem twist_holonomy (i : Fin 3) (u : Slice n) (x : SpatialVertex n) (j k : Fin 3) :
    spatialHolonomy (twist n i u) x j k = spatialHolonomy u x j k := by
  by_cases hjk : j = k
  · subst k
    simp only [spatialHolonomy]
    group
  · by_cases hji : j = i
    · subst j
      have hki : k ≠ i := Ne.symm hjk
      simp only [spatialHolonomy, twist_apply]
      by_cases hx : x i = 0 <;> simp [spatialStep, hki, hx]
    · by_cases hki : k = i
      · subst k
        simp only [spatialHolonomy, twist_apply]
        by_cases hx : x i = 0 <;> simp [spatialStep, hji, hx]
      · simp [spatialHolonomy, twist_apply, hji, hki]

def homeomorph (i : Fin 3) : Slice n ≃ₜ Slice n where
  toFun := twist n i
  invFun := twist n i
  left_inv := twist_involution n i
  right_inv := twist_involution n i
  continuous_toFun := twist_continuous n i
  continuous_invFun := twist_continuous n i

variable [NeZero n]
local instance haar_left : (WilsonSlabOperator.measure n).IsMulLeftInvariant := by
  unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar
  infer_instance

theorem twist_preserving (i : Fin 3) :
    MeasurePreserving (twist n i) (WilsonSlabOperator.measure n) (WilsonSlabOperator.measure n) :=
  measurePreserving_mul_left (WilsonSlabOperator.measure n) (seam n i (-1))

theorem potential_twist (i : Fin 3) (u : Slice n) :
    potential character 2 (twist n i u) = potential character 2 u := by
  simp only [potential, twist_holonomy]

theorem kinetic_twist (i : Fin 3) (u v : Slice n) :
    kineticAction character 2 (twist n i u) (twist n i v) = kineticAction character 2 u v := by
  simp only [kineticAction, twist, Pi.mul_apply, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem kernel_twist (i : Fin 3) (β : ℝ) (u v : Slice n) :
    WilsonTemporalGauge.rawKernel character β 2 (twist n i u) (twist n i v) =
      WilsonTemporalGauge.rawKernel character β 2 u v := by
  simp only [WilsonTemporalGauge.rawKernel, spatialWeight, kineticWeight,
    potential_twist, kinetic_twist]

def symmetry (i : Fin 3) : WilsonRawSymmetry.Symmetry n where
  map := (homeomorph n i).toMeasurableEquiv
  continuous_map := twist_continuous n i
  continuous_inv := twist_continuous n i
  preserving := twist_preserving n i
  invariant := kernel_twist n i

theorem ground_twist (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    ground n β hβ (twist n i u) = ground n β hβ u :=
  WilsonRawSymmetry.ground_invariant n (symmetry n i) β hβ u

/-- Change of variables for the actual physical-ground stationary law. -/
theorem ground_integral (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (F : Slice n → ℝ) :
    (∫ u, F (twist n i u) ∂groundLaw n β hβ) = ∫ u, F u ∂groundLaw n β hβ := by
  rw [groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous,
    GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  have hh := WilsonRawSymmetry.integral_pull n (symmetry n i)
    (fun u => (ground n β hβ u)^2 * F u)
  change (∫ u, (ground n β hβ (twist n i u))^2 * F (twist n i u)
    ∂WilsonSlabOperator.measure n) = _ at hh
  simpa only [ground_twist] using hh

omit [NeZero n] in
theorem transport_twist (i : Fin 3) (u : Slice n) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    transport n (twist n i u) i k = -transport n u i k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [transport, transport]
    by_cases hk0 : k = 0
    · subst k
      simp [transport, twist_apply, point]
    · have hz : (k : ZMod n) ≠ 0 := by
        intro hz
        have hv := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
        exact hk0 hv
      rw [ih (by omega) (by omega)]
      simp [twist_apply, point, hz]

theorem loop_odd (i : Fin 3) (u : Slice n) : loop n i (twist n i u) = -loop n i u := by
  change (character (transport n (twist n i u) i n)).re = _
  rw [transport_twist n i u n (NeZero.pos n) le_rfl]
  simp [loop, character_re, Unitary.coe_neg]

end
end UnifiedTheory.Clay.YangMills.WilsonCenterTwist

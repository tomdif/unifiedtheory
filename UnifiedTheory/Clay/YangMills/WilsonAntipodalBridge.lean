/- Opposite middle-bridge endpoints remove temporal pinning exactly.
On even spatial periods they are gauge equivalent for every configuration,
so their actual physical variance-pair source weight is zero. This exact
cancellation does not control a neighborhood of those endpoint pairs. -/
import UnifiedTheory.Clay.YangMills.WilsonMiddleBridge
import UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAntipodalBridge
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonMiddleBridge
open WilsonSingleLinkStaples (character)
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n]

theorem kinetic_antipodal (u v : Slice n) :
    kineticAction character 2 u v+kineticAction character 2 u (-v) =
      4*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) := by
  have he (e : SpatialVertex n × Fin 3) :
      (character ((u e)⁻¹*v e)).re+(character ((u e)⁻¹*(-v e))).re = 0 := by
    rw [WilsonRowGeometry.character_pair, WilsonRowGeometry.character_pair]
    change 2*⟪(u e : ℍ), (v e : ℍ)⟫+2*⟪(u e : ℍ), -(v e : ℍ)⟫ = 0
    rw [inner_neg_right]
    ring
  unfold kineticAction
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _e : SpatialVertex n × Fin 3, (4 : ℝ) :=
      Finset.sum_congr rfl (fun e _ => by
        have h := he e
        change (2-(character ((u e)⁻¹*v e)).re)+(2-(character ((u e)⁻¹*(-v e))).re) = 4
        linarith)
    _ = _ := by simp; ring

theorem action_antipodal (β : ℝ) (v u : Slice n) :
    action n β v (-v) u = β*potential character 2 u+
      4*β*(Fintype.card (SpatialVertex n × Fin 3) : ℝ) := by
  unfold action
  rw [add_assoc, ← mul_add, kinetic_antipodal]
  ring

omit n [NeZero n] in
theorem antipodal_distance (u v : Q) :
    ‖(u : ℍ) - (v : ℍ)‖ ^ 2+‖(u : ℍ) - ((-v : Q) : ℍ)‖ ^ 2 = 4 := by
  simp only [norm_sub_sq_real, QuaternionSymmetricChange.unit_norm]
  change 1^2-2*⟪(u : ℍ), (v : ℍ)⟫+1^2+
    (1^2-2*⟪(u : ℍ), -(v : ℍ)⟫+1^2) = 4
  rw [inner_neg_right]
  ring

def parity (heven : 2 ∣ n) (x : SpatialVertex n) : ZMod 2 :=
  ∑ i, ZMod.castHom heven (ZMod 2) (x i)

omit [NeZero n] in
theorem parity_step (heven : 2 ∣ n) (x : SpatialVertex n) (i : Fin 3) :
    parity n heven (spatialStep n x i) = parity n heven x+1 := by
  classical
  change (∑ j, ZMod.castHom heven (ZMod 2)
    (x j+(Pi.single i (1 : ZMod n) : SpatialVertex n) j)) = _
  simp only [map_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, map_one]
  · intro j _ hj
    simp only [Pi.single_eq_of_ne hj, map_zero]
  · simp

def alternatingGauge (heven : 2 ∣ n) : SliceGauge n Q := fun x =>
  if parity n heven x = 0 then 1 else -1

omit [NeZero n] in
theorem alternating_step (heven : 2 ∣ n) (x : SpatialVertex n) (i : Fin 3) :
    alternatingGauge n heven (spatialStep n x i) = -alternatingGauge n heven x := by
  unfold alternatingGauge
  rw [parity_step]
  generalize parity n heven x = p
  fin_cases p
  · norm_num
  · norm_num
    intro h
    exact (h (by decide)).elim

omit [NeZero n] in
/-- The antipode is on the same gauge orbit for every spatial field, not
only at flat or constant fields. -/
theorem gauge_antipode (heven : 2 ∣ n) (v : Slice n) :
    gaugeSlice (alternatingGauge n heven) v = -v := by
  funext e
  change alternatingGauge n heven e.1*v e*
    (alternatingGauge n heven (spatialStep n e.1 e.2))⁻¹ = -v e
  rw [alternating_step]
  unfold alternatingGauge
  split <;> simp

omit [NeZero n] in
theorem physical_antipodal (heven : 2 ∣ n) (F : Slice n → ℝ)
    (hF : ∀ h u, F (gaugeSlice h u) = F u) (v : Slice n) : F (-v) = F v := by
  rw [← gauge_antipode n heven v]
  exact hF _ _

/-- The actual endpoint source factor vanishes at exact opposite endpoints.
No continuity modulus or neighborhood estimate follows from this identity. -/
theorem endpoint_source_zero (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(Slice n, ℝ)) (hF : ∀ h u, F (gaugeSlice h u) = F u) (v : Slice n) :
    endpointWeight n β hβ v (-v)*(F v-F (-v))^2 = 0 := by
  rw [physical_antipodal n heven F hF v, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]

end
end UnifiedTheory.Clay.YangMills.WilsonAntipodalBridge

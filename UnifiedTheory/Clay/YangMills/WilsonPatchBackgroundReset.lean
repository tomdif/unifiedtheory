/- A concrete background keeps the sampled exterior and copies one
endpoint inside the patch. Its eligibility cost is controlled by the
same sampled middle field's local interacting energy. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchEligibility
import UnifiedTheory.Clay.YangMills.WilsonPatchExteriorDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchBackgroundReset
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonPatchLocalEnergy
open WilsonPatchComplementTail WilsonPatchNeighborhood WilsonJointRotation
open WilsonPatchExteriorDecomposition
open WilsonSingleLinkStaples (character)
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def outsideOf (S : Finset (SpatialVertex n × Fin 3)) (v : Slice n) : Outside n S :=
  fun e => v e.1

omit [NeZero n] in
theorem outside_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (outsideOf n S) := continuous_pi (fun e => continuous_apply e.1)

def reset (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) : Slice n :=
  background n S u (outsideOf n S v)

omit [NeZero n] in
theorem reset_inside (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n)
    (e : SpatialVertex n × Fin 3) (he : e ∈ S) : reset n S u v e = u e :=
  WilsonBlockMarginal.assemble_inside S _ e he

omit [NeZero n] in
theorem reset_outside (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n)
    (e : SpatialVertex n × Fin 3) (he : e ∉ S) : reset n S u v e = v e :=
  WilsonBlockMarginal.assemble_outside S _ e he

omit [NeZero n] in
theorem background_continuous (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n) :
    Continuous (background n S u) :=
  (WilsonBlockMarginal.assemble_continuous S).comp (continuous_id.prodMk continuous_const)

omit [NeZero n] in
theorem reset_continuous (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n) :
    Continuous (reset n S u) := (background_continuous n S u).comp (outside_continuous n S)

theorem incident_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (incidentEnergy n S) :=
  (part_continuous n (bulk n S)).add (part_continuous n (boundary n S))

omit [NeZero n] in
theorem endpoint_continuous (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n) :
    Continuous (fun v => endpointEnergy n S v u w) := by
  have hc := WilsonSingleLinkStaples.character_continuous
  unfold endpointEnergy kineticPart
  fun_prop

theorem local_continuous (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n) :
    Continuous (fun v => localEnergy n S v u w) :=
  (incident_continuous n S).add (endpoint_continuous n S u w)

theorem cost_continuous (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n) :
    Continuous (fun v => backgroundCost n S v u w) :=
  (continuous_const.mul (incident_continuous n S)).add
    (continuous_const.mul (endpoint_continuous n S u w))

theorem potential_fixed (S : Finset (SpatialVertex n × Fin 3)) (v₀ v : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) :
    potential character 2 v = bulkPotential n Sᶜ v₀ + incidentEnergy n S v := by
  rw [potential_split n S v, bulk_congr n Sᶜ v v₀
    (fun e he => hv e (Finset.mem_compl.mp he))]
  unfold incidentEnergy
  ring

theorem incident_upper (S : Finset (SpatialVertex n × Fin 3)) (v₀ v : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) :
    incidentEnergy n S v ≤ 2 * incidentEnergy n S v₀ + 32 * distanceSq n v₀ v := by
  let a : Slice n := v * v₀⁻¹
  have hav : a * v₀ = v := by dsimp only [a]; group
  have ha (e : SpatialVertex n × Fin 3) (he : e ∉ S) : a e = 1 := by
    simp only [a, Pi.mul_apply, Pi.inv_apply, hv e he, mul_inv_cancel]
  have hm : ∀ e ∉ S, (a⁻¹ * v₀) e = v₀ e := by
    intro e he
    simp only [Pi.mul_apply, Pi.inv_apply, ha e he, inv_one, one_mul]
  have hc : cost n a = distanceSq n v₀ v := by
    unfold cost displacement distanceSq
    apply Finset.sum_congr rfl
    intro e _
    simp only [a, Pi.mul_apply, Pi.inv_apply, QuaternionChordMidpoint.rotation_chord,
      norm_sub_rev (v e : ℍ) (v₀ e : ℍ)]
  have hh := potential_second_bound n a v₀
  rw [hav, potential_fixed n S v₀ v hv,
    potential_fixed n S v₀ (a⁻¹ * v₀) hm,
    potential_fixed n S v₀ v₀ (fun _ _ => rfl), hc] at hh
  have hm0 := incident_nonneg n S (a⁻¹ * v₀)
  linarith

theorem reset_distance (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) :
    distanceSq n v (reset n S u v) = kineticPart n S v u := by
  rw [distance_supported n S v _ (reset_outside n S u v), kinetic_distance]
  apply Finset.sum_congr rfl
  intro e he
  rw [reset_inside n S u v e he]

omit [NeZero n] in
theorem reset_endpoint (S : Finset (SpatialVertex n × Fin 3)) (u w v : Slice n) :
    endpointEnergy n S (reset n S u v) u w = kineticPart n S u w := by
  unfold endpointEnergy
  rw [kinetic_congr n S (reset n S u v) u u u (reset_inside n S u v) (fun _ _ => rfl),
    kinetic_congr n S (reset n S u v) w u w (reset_inside n S u v) (fun _ _ => rfl)]
  simp only [kinetic_distance, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add]

omit [NeZero n] in
theorem endpoint_triangle (S : Finset (SpatialVertex n × Fin 3)) (u w v : Slice n) :
    kineticPart n S u w ≤ 2 * kineticPart n S v u + 2 * kineticPart n S v w := by
  rw [kinetic_distance, kinetic_distance, kinetic_distance,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  simpa only [norm_sub_rev (u e : ℍ) (v e : ℍ),
    norm_sub_rev (w e : ℍ) (v e : ℍ)] using
    chord_triangle_square (u e) (v e) (w e)

/-- The reset background is eligible whenever the sampled local bridge
energy is at most threshold/70. No arbitrary replacement distribution is used. -/
theorem reset_cost_bound (S : Finset (SpatialVertex n × Fin 3)) (u w v : Slice n) :
    backgroundCost n S (reset n S u v) u w ≤ 70 * localEnergy n S v u w := by
  have hi := incident_upper n S v (reset n S u v) (reset_outside n S u v)
  rw [reset_distance] at hi
  have hk := endpoint_triangle n S u w v
  have hp := incident_nonneg n S v
  have hw := kinetic_nonneg n S v w
  unfold backgroundCost
  rw [reset_endpoint]
  unfold localEnergy endpointEnergy
  linarith only [hi, hk, hp, hw]

omit [NeZero n] in
theorem outside_assemble (S : Finset (SpatialVertex n × Fin 3))
    (z : Outside n S × WilsonPatchConditioning.Inside n S) :
    outsideOf n S (WilsonBlockMarginal.assemble S z) = z.1 := by
  funext e
  exact WilsonBlockMarginal.assemble_outside S z e.1 e.2

omit [NeZero n] in
theorem reset_assemble (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n)
    (z : Outside n S × WilsonPatchConditioning.Inside n S) :
    reset n S u (WilsonBlockMarginal.assemble S z) = background n S u z.1 := by
  unfold reset
  rw [outside_assemble]

theorem background_fiber_bound (S : Finset (SpatialVertex n × Fin 3)) (u w : Slice n)
    (b : Outside n S) (x : WilsonPatchConditioning.Inside n S) :
    backgroundCost n S (background n S u b) u w ≤
      70 * localEnergy n S (WilsonBlockMarginal.assemble S (b, x)) u w := by
  simpa only [reset_assemble] using reset_cost_bound n S u w
    (WilsonBlockMarginal.assemble S (b, x))

end
end UnifiedTheory.Clay.YangMills.WilsonPatchBackgroundReset

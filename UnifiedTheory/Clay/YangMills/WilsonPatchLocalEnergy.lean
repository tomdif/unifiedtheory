/- Local middle-bridge energy keeps every incident plaquette and cancels
only the fixed exterior. Its global upper and lower bounds have no
exterior-volume factor and require no small-field hypothesis. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchCovarianceTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchLocalEnergy
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonPatchNeighborhood
open WilsonPatchConditioning WilsonJointRotation
open WilsonSingleLinkStaples (character)
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def incidentEnergy (S : Finset (SpatialVertex n × Fin 3)) (v : Slice n) : ℝ :=
  bulkPotential n S v + boundaryPotential n S v

def endpointEnergy (S : Finset (SpatialVertex n × Fin 3)) (v u w : Slice n) : ℝ :=
  kineticPart n S v u + kineticPart n S v w

def localEnergy (S : Finset (SpatialVertex n × Fin 3)) (v u w : Slice n) : ℝ :=
  incidentEnergy n S v + endpointEnergy n S v u w

def exteriorEnergy (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w : Slice n) : ℝ :=
  bulkPotential n Sᶜ v₀ + kineticPart n Sᶜ v₀ u + kineticPart n Sᶜ v₀ w

theorem incident_nonneg (S : Finset (SpatialVertex n × Fin 3)) (v : Slice n) :
    0 ≤ incidentEnergy n S v :=
  add_nonneg (part_bounds n (bulk n S) v).1 (part_bounds n (boundary n S) v).1

omit [NeZero n] in
theorem endpoint_nonneg (S : Finset (SpatialVertex n × Fin 3)) (v u w : Slice n) :
    0 ≤ endpointEnergy n S v u w :=
  add_nonneg (kinetic_nonneg n S v u) (kinetic_nonneg n S v w)

theorem local_nonneg (S : Finset (SpatialVertex n × Fin 3)) (v u w : Slice n) :
    0 ≤ localEnergy n S v u w := add_nonneg (incident_nonneg n S v) (endpoint_nonneg n S v u w)

theorem action_split (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w v : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) (β : ℝ) :
    WilsonMiddleBridge.action n β u w v =
      β * exteriorEnergy n S v₀ u w + β * localEnergy n S v u w := by
  have ho : ∀ e ∈ Sᶜ, v e = v₀ e := fun e he => hv e (Finset.mem_compl.mp he)
  unfold WilsonMiddleBridge.action
  rw [potential_split n S v, kinetic_split n S v u, kinetic_split n S v w,
    bulk_congr n Sᶜ v v₀ ho,
    kinetic_congr n Sᶜ v u v₀ u ho (fun _ _ => rfl),
    kinetic_congr n Sᶜ v w v₀ w ho (fun _ _ => rfl)]
  unfold exteriorEnergy localEnergy incidentEnergy endpointEnergy
  ring

omit n [NeZero n] in
theorem pair_defect (a b : Q) : 2 - (character (a⁻¹ * b)).re = ‖(a : ℍ) - (b : ℍ)‖ ^ 2 := by
  rw [WilsonRowGeometry.character_pair, norm_sub_sq_real,
    CStarRing.norm_of_mem_unitary a.property, CStarRing.norm_of_mem_unitary b.property]
  ring

omit [NeZero n] in
theorem kinetic_distance (S : Finset (SpatialVertex n × Fin 3)) (v u : Slice n) :
    kineticPart n S v u = ∑ e ∈ S, ‖(v e : ℍ) - (u e : ℍ)‖ ^ 2 := by
  simp only [kineticPart, pair_defect]

theorem distance_supported (S : Finset (SpatialVertex n × Fin 3)) (v₀ v : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) :
    distanceSq n v₀ v = ∑ e ∈ S, ‖(v₀ e : ℍ) - (v e : ℍ)‖ ^ 2 := by
  unfold distanceSq
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun e _ he => by rw [hv e he]; simp)

omit n [NeZero n] in
theorem chord_triangle_square (a b c : Q) :
    ‖(a : ℍ) - (c : ℍ)‖ ^ 2 ≤
      2 * ‖(a : ℍ) - (b : ℍ)‖ ^ 2 + 2 * ‖(c : ℍ) - (b : ℍ)‖ ^ 2 := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (a : ℍ) (b : ℍ) (c : ℍ)
  rw [norm_sub_rev (b : ℍ) (c : ℍ)] at ht
  have hs := sq_le_sq₀ (norm_nonneg ((a : ℍ) - (c : ℍ)))
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr ht
  nlinarith [sq_nonneg (‖(a : ℍ) - (b : ℍ)‖ - ‖(c : ℍ) - (b : ℍ)‖)]

theorem distance_kinetic_bound (S : Finset (SpatialVertex n × Fin 3)) (v₀ v u : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) :
    distanceSq n v₀ v ≤ 2 * kineticPart n S v₀ u + 2 * kineticPart n S v u := by
  rw [distance_supported n S v₀ v hv, kinetic_distance, kinetic_distance,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun e _ => chord_triangle_square (v₀ e) (u e) (v e))

/-- An endpoint mismatch is charged only on the active links. -/
theorem local_lower (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w v : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) :
    distanceSq n v₀ v - endpointEnergy n S v₀ u w ≤ localEnergy n S v u w := by
  have hu := distance_kinetic_bound n S v₀ v u hv
  have hw := distance_kinetic_bound n S v₀ v w hv
  have hp := incident_nonneg n S v
  unfold localEnergy endpointEnergy
  linarith

/-- Positivity of the reflected configuration upgrades the existing
symmetric action bound to a global one-sided Gaussian upper bound. -/
theorem local_upper (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w v : Slice n)
    (hv : ∀ e ∉ S, v e = v₀ e) :
    localEnergy n S v u w ≤ 2 * localEnergy n S v₀ u w + 36 * distanceSq n v₀ v := by
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
  have hh := WilsonMiddleBridge.action_second_bound n 1 (by norm_num) a u w v₀
  rw [hav, action_split n S v₀ u w v hv,
    action_split n S v₀ u w (a⁻¹ * v₀) hm,
    action_split n S v₀ u w v₀ (fun _ _ => rfl), hc] at hh
  have hm0 := local_nonneg n S (a⁻¹ * v₀) u w
  linarith

omit [NeZero n] in
theorem insert_outside (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (x : Inside n S) (e : SpatialVertex n × Fin 3) (he : e ∉ S) :
    insert n S v₀ x e = v₀ e := WilsonBlockMarginal.assemble_outside S _ e he

theorem bad_distance (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Inside n S) (hx : x ∉ event n S v₀ ε) :
    ε ^ 2 ≤ distanceSq n v₀ (insert n S v₀ x) := by
  classical
  have hex : ∃ e : {e : SpatialVertex n × Fin 3 // e ∈ S},
      ε < ‖(x e : ℍ) - (v₀ e.1 : ℍ)‖ := by
    simpa only [event, Set.mem_pi, Set.mem_univ, forall_const,
      QuaternionCapContraction.cap, Set.mem_setOf_eq, not_forall, not_le] using hx
  obtain ⟨e, he⟩ := hex
  have hs := Finset.single_le_sum (f := fun b =>
    ‖(v₀ b : ℍ) - (insert n S v₀ x b : ℍ)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ e.1)
  change _ ≤ distanceSq n v₀ (insert n S v₀ x) at hs
  have hi : insert n S v₀ x e.1 = x e := WilsonBlockMarginal.assemble_inside S _ e.1 e.2
  dsimp only at hs
  rw [hi, norm_sub_rev] at hs
  exact (pow_le_pow_left₀ hε he.le 2).trans hs

end
end UnifiedTheory.Clay.YangMills.WilsonPatchLocalEnergy

/- A fixed product chord neighborhood preserves the incident-plaquette
and endpoint hypotheses. It is compact and closed under exact quaternion
midpoints. Fields and defects outside the incident region are unrestricted. -/
import UnifiedTheory.Clay.YangMills.QuaternionChordMidpoint
import UnifiedTheory.Clay.YangMills.WilsonMaskedCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchNeighborhood
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonJointRotation
open QuaternionChordMidpoint
open scoped Quaternion

variable (n : ℕ)

def region (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) : Set (Slice n) :=
  {v | (∀ e, e ∉ S → v e = v₀ e) ∧ (∀ e, ‖(v e : ℍ) - (v₀ e : ℍ)‖ ≤ ε)}

theorem center_mem (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 ≤ ε) : v₀ ∈ region n S v₀ ε := by
  exact ⟨fun _ _ => rfl, fun _ => by simpa only [sub_self, norm_zero] using hε⟩

theorem region_closed (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    IsClosed (region n S v₀ ε) := by
  unfold region
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · exact isClosed_iInter (fun e => isClosed_iInter (fun _ : e ∉ S =>
      isClosed_eq (continuous_apply e : Continuous (fun v : Slice n => v e))
        continuous_const))
  · exact isClosed_iInter (fun e => isClosed_le
      ((continuous_subtype_val.comp (continuous_apply e :
        Continuous (fun v : Slice n => v e))).sub continuous_const).norm continuous_const)

variable [NeZero n]

omit [NeZero n] in
theorem region_compact (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    IsCompact (region n S v₀ ε) := (region_closed n S v₀ ε).isCompact

def distanceSq (v w : Slice n) : ℝ := ∑ e, ‖(v e : ℍ) - (w e : ℍ)‖ ^ 2

theorem distanceSq_nonneg (v w : Slice n) : 0 ≤ distanceSq n v w :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem distanceSq_eq_zero (v w : Slice n) : distanceSq n v w = 0 ↔ v = w := by
  constructor
  · intro h
    funext e
    have he : ‖(v e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ distanceSq n v w := by
      unfold distanceSq
      exact Finset.single_le_sum (f := fun b => ‖(v b : ℍ) - (w b : ℍ)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ e)
    rw [h] at he
    have hz : ‖(v e : ℍ) - (w e : ℍ)‖ = 0 := by nlinarith [norm_nonneg ((v e : ℍ) - (w e : ℍ))]
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz))
  · rintro rfl
    simp [distanceSq]

/-- A midpoint remains in the same fixed region, with no field-dependent mask.
Its symmetric rotation is supported there and controls endpoint distance. -/
theorem exists_midpoint (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : ε ^ 2 < 2) (v w : Slice n)
    (hv : v ∈ region n S v₀ ε) (hw : w ∈ region n S v₀ ε) :
    ∃ m ∈ region n S v₀ ε, ∃ a : Slice n,
      (∀ e, e ∉ S → a e = 1) ∧ a * m = v ∧ a⁻¹ * m = w ∧
        distanceSq n v w ≤ 4 * cost n a := by
  have hne (e) : (v e : ℍ) + (w e : ℍ) ≠ 0 :=
    sum_ne_zero (v e) (w e) (v₀ e) ε hε (hv.2 e) (hw.2 e)
  let m : Slice n := fun e => midpoint (v e) (w e) (hne e)
  let a : Slice n := v * m⁻¹
  have hm : m ∈ region n S v₀ ε := by
    constructor
    · intro e he
      dsimp [m]
      simp only [hv.1 e he, hw.1 e he, QuaternionChordMidpoint.midpoint_self]
    · intro e
      exact midpoint_cap (v e) (w e) (v₀ e) ε hε (hv.2 e) (hw.2 e) (hne e)
  refine ⟨m, hm, a, ?_, ?_, ?_, ?_⟩
  · intro e he
    change v e * (m e)⁻¹ = 1
    rw [hv.1 e he, hm.1 e he, mul_inv_cancel]
  · dsimp [a]
    group
  · funext e
    exact midpoint_symmetric (v e) (w e) (hne e)
  · unfold distanceSq cost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    simpa only [a, Pi.mul_apply, Pi.inv_apply, displacement, rotation_chord] using
      midpoint_chord (v e) (w e) (hne e)

omit [NeZero n] in
/-- Any link field within epsilon of the base has plaquette chord drift
at most four epsilon, including repeated links on a small periodic lattice. -/
theorem holonomy_drift (v v₀ : Slice n) (ε : ℝ)
    (hv : ∀ e, ‖(v e : ℍ) - (v₀ e : ℍ)‖ ≤ ε) (p : Plaquette n) :
    ‖((spatialHolonomy v p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ + 4 * ε := by
  let a : Slice n := v * v₀⁻¹
  have ha : a * v₀ = v := by dsimp [a]; group
  have he (e) : displacement n a e ≤ ε := by
    simpa only [displacement, a, Pi.mul_apply, Pi.inv_apply, rotation_chord] using hv e
  have hh := (holonomy_variation n a v₀ p.1 p.2.1.1 p.2.1.2).1
  rw [ha, mul_one] at hh
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((spatialHolonomy v p.1 p.2.1.1 p.2.1.2 : Q) : ℍ)
    ((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) 1
  linarith [he (p.1, p.2.1.1), he (spatialStep n p.1 p.2.1.1, p.2.1.2),
    he (spatialStep n p.1 p.2.1.2, p.2.1.1), he (p.1, p.2.1.2)]

omit [NeZero n] in
theorem incident_small (S : Finset (SpatialVertex n × Fin 3)) (v₀ v : Slice n)
    (hv : v ∈ region n S v₀ (1 / 256))
    (hflat : ∀ p e, e ∈ S → e ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64) :
    ∀ p e, e ∈ S → e ∈ support n p →
      ‖((spatialHolonomy v p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 32 := by
  intro p e he hp
  have hh := holonomy_drift n v v₀ (1 / 256) hv.2 p
  linarith [hflat p e he hp]

omit [NeZero n] in
theorem endpoint_small (S : Finset (SpatialVertex n × Fin 3)) (v₀ v u : Slice n)
    (hv : v ∈ region n S v₀ (1 / 256))
    (hu : ∀ e ∈ S, ‖(v₀ e : ℍ) - (u e : ℍ)‖ ≤ 1 / 2) :
    ∀ e ∈ S, ‖(v e : ℍ) - (u e : ℍ)‖ ^ 2 ≤ 1 / 2 := by
  intro e he
  have ht := norm_sub_le_norm_sub_add_norm_sub (v e : ℍ) (v₀ e : ℍ) (u e : ℍ)
  have hb : ‖(v e : ℍ) - (u e : ℍ)‖ ≤ 129 / 256 := by linarith [hv.2 e, hu e he]
  nlinarith [norm_nonneg ((v e : ℍ) - (u e : ℍ))]

end
end UnifiedTheory.Clay.YangMills.WilsonPatchNeighborhood

/- Actual gauge-invariant winding loops distinguish exactly flat spatial
slices on every positive periodic lattice. Local plaquette data therefore
do not exhaust the physical small-field observables. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonWindingLoop
noncomputable section
open WilsonTimeSlab WilsonSlabOperator
open WilsonSingleLinkStaples (character character_continuous character_re character_classFunction)

variable (n : ℕ)

def point (i : Fin 3) (k : ℕ) : SpatialVertex n := Pi.single i (k : ZMod n)

theorem point_zero (i : Fin 3) : point n i 0 = 0 := by simp [point]

theorem point_succ (i : Fin 3) (k : ℕ) :
    point n i (k + 1) = spatialStep n (point n i k) i := by
  simp only [point, spatialStep, Nat.cast_add, Nat.cast_one, Pi.single_add]

theorem point_period (i : Fin 3) : point n i n = 0 := by simp [point]

def transport (u : Slice n) (i : Fin 3) : ℕ → Q
  | 0 => 1
  | k + 1 => transport u i k * u (point n i k, i)

theorem transport_continuous (i : Fin 3) (k : ℕ) :
    Continuous (fun u : Slice n => transport n u i k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact ih.mul (continuous_apply _)

theorem transport_gauge (h : SliceGauge n Q) (u : Slice n) (i : Fin 3) (k : ℕ) :
    transport n (gaugeSlice h u) i k =
      h 0 * transport n u i k * (h (point n i k))⁻¹ := by
  induction k with
  | zero => simp [transport, point_zero]
  | succ k ih =>
    rw [transport, ih, point_succ]
    simp only [gaugeSlice, transport]
    group

def loop (i : Fin 3) : C(Slice n, ℝ) :=
  ⟨fun u => (character (transport n u i n)).re,
    Complex.continuous_re.comp (character_continuous.comp (transport_continuous n i n))⟩

theorem loop_gauge (i : Fin 3) (h : SliceGauge n Q) (u : Slice n) :
    loop n i (gaugeSlice h u) = loop n i u := by
  change (character (transport n (gaugeSlice h u) i n)).re = _
  rw [transport_gauge, point_period, character_classFunction]
  rfl

/-- One seam carries q; all links in the other directions equal the identity. -/
def seam (i : Fin 3) (q : Q) : Slice n :=
  fun e => if e.2 = i ∧ e.1 i = 0 then q else 1

theorem seam_transverse (i j : Fin 3) (hji : j ≠ i) (q : Q) (x : SpatialVertex n) :
    seam n i q (spatialStep n x j, i) = seam n i q (x, i) := by
  simp [seam, spatialStep, hji]

/-- The flat family permits arbitrary SU(2) seam holonomy, not only central values. -/
theorem seam_flat (i : Fin 3) (q : Q) (x : SpatialVertex n) (j k : Fin 3) :
    spatialHolonomy (seam n i q) x j k = 1 := by
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      simp only [spatialHolonomy]
      group
    · rw [spatialHolonomy, seam_transverse n i k hki]
      simp [seam, hki]
  · by_cases hki : k = i
    · subst k
      rw [spatialHolonomy, seam_transverse n i j hji]
      simp [seam, hji]
    · simp [spatialHolonomy, seam, hji, hki]

variable [NeZero n]

omit [NeZero n] in
theorem seam_transport (i : Fin 3) (q : Q) (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    transport n (seam n i q) i k = q := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [transport]
    by_cases hk0 : k = 0
    · subst k
      simp [transport, seam, point]
    · have hz : (k : ZMod n) ≠ 0 := by
        intro hz
        have hv := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
        exact hk0 hv
      rw [ih (by omega) (by omega)]
      simp [seam, point, hz]

theorem loop_seam (i : Fin 3) (q : Q) : loop n i (seam n i q) = (character q).re := by
  change (character (transport n (seam n i q) i n)).re = _
  rw [seam_transport n i q n (NeZero.pos n) le_rfl]

/-- These exactly flat configurations are physically distinguishable even at even periods. -/
theorem flat_separation (i : Fin 3) :
    loop n i (seam n i 1) ≠ loop n i (seam n i (-1)) := by
  rw [loop_seam, loop_seam]
  norm_num [character_re, Unitary.coe_neg]

theorem not_gauge_equivalent (i : Fin 3) :
    ¬∃ h : SliceGauge n Q, gaugeSlice h (seam n i 1) = seam n i (-1) := by
  rintro ⟨h, hh⟩
  have he := loop_gauge n i h (seam n i 1)
  rw [hh] at he
  exact flat_separation n i he.symm

/-- Even complete local plaquette holonomies cannot reconstruct every physical observable. -/
theorem no_plaquette_representation (i : Fin 3) :
    ¬∃ F : (SpatialVertex n → Fin 3 → Fin 3 → Q) → ℝ,
      ∀ u : Slice n, loop n i u = F (spatialHolonomy u) := by
  rintro ⟨F, hF⟩
  have he : spatialHolonomy (seam n i 1) = spatialHolonomy (seam n i (-1)) := by
    funext x j k
    rw [seam_flat, seam_flat]
  exact flat_separation n i ((hF _).trans ((congrArg F he).trans (hF _).symm))

/-- This winding observable has positive variance under the original ground law. -/
theorem loop_variance_positive (β : ℝ) (hβ : 0 ≤ β) (i : Fin 3) :
    0 < WilsonPhysicalVariance.variance n β hβ (loop n i) :=
  WilsonGroundVarianceBudget.variance_positive n β hβ (loop n i)
    (seam n i 1) (seam n i (-1)) (flat_separation n i)

end
end UnifiedTheory.Clay.YangMills.WilsonWindingLoop

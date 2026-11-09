/- Full-Schwartz contact subtraction for the actual second removed Wilson covariance.
The finite-range hypothesis is proved from the true induced product law. This is a
finite two-step statement and gives no bound on the final retained covariance. -/
import UnifiedTheory.Clay.YangMills.WilsonSecondNoiseCellPairing
import UnifiedTheory.Clay.YangMills.WilsonSecondNoiseLocality
import UnifiedTheory.Clay.YangMills.FiniteRangeSchwartzContact
import UnifiedTheory.Clay.YangMills.WilsonSchwartzContactPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSecondNoiseContact
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonIndependentBlocks WilsonInducedProduct WilsonSchwartzContactPath
open WilsonSecondNoiseCellPairing
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

def pairing (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∫ z : Spacetime × Spacetime, (kernel n β a S T plane plane' z.1 z.2 : ℂ) * F z

def contact4 (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  FiniteRangeSchwartzContact.contact (fun z => kernel n β a S T plane plane' z.1 z.2) a R 3 F

/-- The actual ten-spacing range implies the twelve-spacing tube used in the estimate. -/
theorem local_zero (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (ha : 0 < a) (hperiod : 2 * R + 5 * a < (n : ℝ) * a)
    (plane plane' : Plane) (z : Spacetime × Spacetime) (hx : ‖z.1‖ ≤ R) (hy : ‖z.2‖ ≤ R)
    (hfar : (4 * 3) * a < ‖z.1 - z.2‖) : kernel n β a S T plane plane' z.1 z.2 = 0 := by
  unfold kernel
  rw [WilsonSecondNoiseLocality.physical_zero_far n β S hS T hT a R ha hperiod
    plane plane' z.1 z.2 hx hy (by nlinarith)]
  exact mul_zero _

def pairingCLM (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane) :
    SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ :=
  WilsonContactDistribution.boundedKernelCLM volume
    (fun z => (kernel n β a S T plane plane' z.1 z.2 : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      (kernel_measurable n β a S T plane plane')).aestronglyMeasurable
    (4 / a ^ 8) (by positivity) (fun z => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        kernel_abs_le n β a S T plane plane' z.1 z.2)

def contactCLM (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane) (ha : 0 < a) :
    SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ :=
  FiniteRangeSchwartzContact.contactCLM
    (fun z => kernel n β a S T plane plane' z.1 z.2)
    (kernel_measurable n β a S T plane plane') a R 3 4 ha (by norm_num) (by norm_num)
    (fun z => kernel_abs_le n β a S T plane plane' z.1 z.2)

def remainderCLM (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane) (ha : 0 < a) :
    SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ :=
  pairingCLM n β a S T plane plane' - contactCLM n β a R S T plane plane' ha

theorem pairingCLM_apply (β a : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    pairingCLM n β a S T plane plane' F = pairing n β a S T plane plane' F := rfl

theorem contactCLM_apply (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane) (ha : 0 < a)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contactCLM n β a R S T plane plane' ha F = contact4 n β a R S T plane plane' F := rfl

theorem contact_diagonal_support (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (plane plane' : Plane)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hF : ∀ x : Spacetime, (x, x) ∉ tsupport F) : contact4 n β a R S T plane plane' F = 0 :=
  FiniteRangeSchwartzContact.contact_diagonal_support _ a R 3 F hF

/-- Full physical Schwartz bound, including every periodic alias outside the pair ball. -/
theorem subtraction_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (ha : 0 < a) (hR : 0 < R) (hperiod : 2 * R + 5 * a < (n : ℝ) * a)
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    ‖pairing n β a S T plane plane' F - contact4 n β a R S T plane plane' F‖ ≤
      ((FiniteRangeSchwartzContact.mass 4 3 1 * (4 * 3) ^ 5 / 24) *
        SchwartzMap.seminorm ℝ 0 5 F) * (a * R ^ 4) +
          (4 * SchwartzWeightedTail.weightedMoment volume m F) * (a ^ 8 * R ^ m)⁻¹ :=
  FiniteRangeSchwartzContact.subtraction_bound_scaled
    (fun z => kernel n β a S T plane plane' z.1 z.2)
    (kernel_measurable n β a S T plane plane') a R 3 4 ha hR (by norm_num) (by norm_num)
    (fun z => kernel_abs_le n β a S T plane plane' z.1 z.2)
    (local_zero n β a R S hS T hT ha hperiod plane plane') F m

omit [NeZero n] in
/-- The stronger no-wrap requirement for the induced response neighborhood holds on the path. -/
theorem no_wrap (k : ℕ) (hk : 2 ≤ k) :
    2 * radius k + 5 * spacing k < (period k : ℝ) * spacing k := by
  rw [physical_size]
  have hr : 3 ≤ radius k := by unfold radius; exact_mod_cast (show 3 ≤ k + 1 by omega)
  have hs : spacing k ≤ 1 := by
    unfold spacing
    exact (div_le_one (pow_pos (radius_pos k) 8)).mpr (one_le_pow₀ (by linarith))
  nlinarith

omit [NeZero n] in
/-- Explicit actual second-stage estimate: a fourth-order local rate and an eighth-order tail. -/
theorem error_bound (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (T : (k : ℕ) → Finset {e : Edge (Vertex (period k)) // e ∉ S k})
    (hT : ∀ k, NextSeparated (period k) (S k) (T k))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ)
    (k : ℕ) (hk : 2 ≤ k) :
    ‖pairing (period k) (β k) (spacing k) (S k) (T k) plane plane' F -
      contact4 (period k) (β k) (spacing k) (radius k) (S k) (T k) plane plane' F‖ ≤
      ((FiniteRangeSchwartzContact.mass 4 3 1 * (4 * 3) ^ 5 / 24) *
        SchwartzMap.seminorm ℝ 0 5 F) / radius k ^ 4 +
          (4 * SchwartzWeightedTail.weightedMoment volume 72 F) / radius k ^ 8 := by
  have h := subtraction_bound (period k) (β k) (spacing k) (radius k) (S k) (hS k)
    (T k) (hT k) (spacing_pos k) (radius_pos k) (no_wrap k hk) plane plane' F 72
  simpa only [local_factor, tail_factor, div_eq_mul_inv] using h

omit [NeZero n] in
/-- Full-Schwartz convergence of the actual second removed covariance after contact subtraction. -/
theorem subtraction_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (T : (k : ℕ) → Finset {e : Edge (Vertex (period k)) // e ∉ S k})
    (hT : ∀ k, NextSeparated (period k) (S k) (T k))
    (plane plane' : Plane) (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k => pairing (period k) (β k) (spacing k) (S k) (T k) plane plane' F -
      contact4 (period k) (β k) (spacing k) (radius k) (S k) (T k) plane plane' F)
      atTop (𝓝 0) := by
  apply FiniteRangeSchwartzContact.subtraction_tendsto_of_growth atTop
    (fun k z => kernel (period k) (β k) (spacing k) (S k) (T k) plane plane' z.1 z.2)
    (fun k => kernel_measurable _ _ _ _ _ _ _) spacing radius 3 4
    (by norm_num) (by norm_num) F 72
    (Eventually.of_forall spacing_pos) (Eventually.of_forall radius_pos)
    (Eventually.of_forall (fun k z => kernel_abs_le _ _ _ _ _ _ _ z.1 z.2)) ?_
    local_factor_tendsto tail_factor_tendsto
  filter_upwards [eventually_atTop.2 ⟨2, fun k hk => no_wrap k hk⟩] with k hk
  exact local_zero (period k) (β k) (spacing k) (radius k) (S k) (hS k) (T k) (hT k)
    (spacing_pos k) hk plane plane'

end
end UnifiedTheory.Clay.YangMills.WilsonSecondNoiseContact

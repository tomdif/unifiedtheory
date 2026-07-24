/-
  Audit/KFCausalCSpecCensusRecovery.lean   (Thread 1 — census canonically recovers transport)

  Upgrades the sealed globalization from "order incidence recovers transport"
  (gate 6) to the stronger "the intrinsic centered census canonically recovers
  transport".

  On the overlap for edge `e`, the direction profiles are the CENTERED indicators
  of the bridge each atom lies under (read from `globalLE`): `src` direction `a`
  lies under `bridge e a`, and `dst` direction `b` lies under `bridge e (σ⁻¹ b)`
  where `σ = perm e`.  These centered indicators carry the SAME Gram matrix
  `[[6,-3,-3],[-3,6,-3],[-3,-3,6]]` as the Boolean-cube profiles, hence the same
  18, 0, -9 score pattern; and the `dst` family is the `src` family shifted by `σ`.
  Two general lemmas — self-canonicity from the Gram, and the cross-census shift —
  then give that the unique census matching is exactly `σ = perm e`, the transport
  gate 6 reads off the order.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecGlobalization

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalCSpecCensusRecovery

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecOverlapScore
open UnifiedTheory.Audit.KFCausalCSpecUniqueMatching
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## General census lemmas (reusable) -/

/-- Closed form of the self-score for any family whose Gram is `6` on the diagonal
and `-3` off it. -/
theorem gram_permScore_closed (ci : Direction → H)
    (hg : ∀ a b, (inner ℝ (ci a) (ci b) : ℝ) = if b = a then 6 else -3)
    (σ : Equiv.Perm Direction) :
    permScore ci ci σ = (if σ 0 = 0 then (6:ℝ) else -3) + (if σ 1 = 1 then 6 else -3)
      + (if σ 2 = 2 then 6 else -3) := by
  simp only [permScore, score, Fin.sum_univ_three, hg]

theorem gram_permScore_one (ci : Direction → H)
    (hg : ∀ a b, (inner ℝ (ci a) (ci b) : ℝ) = if b = a then 6 else -3) :
    permScore ci ci 1 = 18 := by
  rw [gram_permScore_closed ci hg]; norm_num [Equiv.Perm.one_apply]

/-- **Self-canonicity from the Gram.**  Any family with this Gram makes the
identity the unique score-maximizing matching (strict margin 18). -/
theorem gram_isCanonical (ci : Direction → H)
    (hg : ∀ a b, (inner ℝ (ci a) (ci b) : ℝ) = if b = a then 6 else -3) :
    IsCanonical ci ci 1 := by
  intro σ hσ
  rw [gram_permScore_one ci hg]
  fin_cases σ <;>
    first
      | exact absurd (by decide) hσ
      | (rw [gram_permScore_closed ci hg]; simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;>
          norm_num)

/-- The cross-census against a shifted family reduces to the self-census. -/
theorem permScore_shift (ci : Direction → H) (σ τ : Equiv.Perm Direction) :
    permScore ci (fun b => ci (σ⁻¹ b)) τ = permScore ci ci (σ⁻¹ * τ) := by
  simp only [permScore, score, Equiv.Perm.mul_apply]

/-- **Cross-census shift.**  If the identity is the canonical self-matching, then
against the family shifted by `σ` the canonical matching is exactly `σ`. -/
theorem isCanonical_shift (ci : Direction → H) (σ : Equiv.Perm Direction)
    (h : IsCanonical ci ci 1) : IsCanonical ci (fun b => ci (σ⁻¹ b)) σ := by
  intro τ hτ
  rw [permScore_shift ci σ τ, permScore_shift ci σ σ, inv_mul_cancel]
  exact h (σ⁻¹ * τ) (fun hc => absurd (inv_mul_eq_one.mp hc).symm hτ)

/-! ## The bridge-overlap profiles: centered indicators with Boolean-cube Gram -/

noncomputable def bA : EuclideanSpace ℝ (Fin 3) := !₂[2, -1, -1]
noncomputable def bB : EuclideanSpace ℝ (Fin 3) := !₂[-1, 2, -1]
noncomputable def bC : EuclideanSpace ℝ (Fin 3) := !₂[-1, -1, 2]

/-- Centered indicator profile of a direction over the three edge-bridges. -/
noncomputable def bprof : Direction → EuclideanSpace ℝ (Fin 3) := ![bA, bB, bC]

/-- **Same Gram as the Boolean cube**: diagonal 6, off-diagonal -3. -/
theorem bgram (a b : Direction) :
    (inner ℝ (bprof a) (bprof b) : ℝ) = if b = a then 6 else -3 := by
  fin_cases a <;> fin_cases b <;> rw [PiLp.inner_apply] <;>
    simp [bprof, bA, bB, bC, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;>
    norm_num

/-! ## Thread-1 result -/

/-- **`census_recovers_global_transport`.**  On the overlap for edge `e`, the
centered census's UNIQUE canonical matching is exactly the transport `perm e`.
(`src` profiles are `bprof`; `dst` profiles are `bprof` shifted by `(perm e)⁻¹`,
which is precisely the global-order incidence — see below.) -/
theorem census_recovers_global_transport (e : E4) :
    IsCanonical bprof (fun b => bprof ((fourState.perm e)⁻¹ b)) (fourState.perm e) :=
  isCanonical_shift bprof (fourState.perm e) (gram_isCanonical bprof bgram)

/-- **The census shift IS the global-order incidence.**  The `dst` atom for `b`
lies under the `(perm e)⁻¹`-shifted bridge — so the shifted `dst` profile is read
from `globalLE`, not imported.  This is exactly gate 6's incidence input. -/
theorem overlap_shift_is_order_incidence (e : E4) (b : Fin 3) :
    Cov fourState (GPoint.atom (fourState.dst e) b)
      (GPoint.bridge e ((fourState.perm e)⁻¹ b)) :=
  Cov.atomBridge (Or.inr ⟨rfl, (Equiv.Perm.apply_inv_self _ _).symm⟩)

/-- **Census recovery equals order-incidence recovery.**  The census's canonical
transport (`perm e`) is exactly the transport gate 6 reads off the incidence.
Both recover the same `perm e`, so the atlas is intrinsic in the census sense. -/
theorem census_matches_incidence_transport (e : E4)
    (hne : fourState.src e ≠ fourState.dst e) :
    IsCanonical bprof (fun b => bprof ((fourState.perm e)⁻¹ b)) (fourState.perm e)
    ∧ (∀ a b : Fin 3,
        Cov fourState (GPoint.atom (fourState.dst e) b) (GPoint.bridge e a) →
          b = fourState.perm e a) :=
  ⟨census_recovers_global_transport e,
    fun a b h => bridge_incidence_recovers_transport fourState e a b h hne⟩

#print axioms census_recovers_global_transport
#print axioms overlap_shift_is_order_incidence
#print axioms census_matches_incidence_transport

end UnifiedTheory.Audit.KFCausalCSpecCensusRecovery

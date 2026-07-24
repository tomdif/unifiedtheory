/-
  Audit/KFCausalCSpecVolumeSector.lean   (Volume sector — opening unit)

  The order sector (census) recovers the CONFORMAL transport but is blind to the
  SCALE.  Malament: causal order fixes the metric only up to a conformal factor;
  the scale lives in the VOLUME.  This file opens the volume sector by formalizing
  exactly that split:

    * `census_scale_blind`   : the census (canonical matching) is INVARIANT under a
                               positive rescaling of the profiles — it cannot see
                               the scale.  So the volume sector is NECESSARY, not a
                               reformulation of the order sector.
    * `scale_recovered`      : given the mesoscopic volume law `n = rho * C * tau^d`,
                               the interval cardinality `n` recovers the proper time
                               `tau` (the scale) exactly.

  Together these are Malament's split made formal: conformal from the census,
  scale from the count; neither determines the other.

  THE OPEN WALL.  `scale_recovered` assumes the volume law HOLDS.  That the count
  actually equals `rho * C * tau^d` — mesoscopically and up to Poisson fluctuation
  and curvature bias — is the quantitative Hauptvermutung, the genuinely hard open
  problem of this sector (the volume-side analogue of R3).  It is NOT proved here,
  and must not be conflated with the deterministic recovery below.  A separate
  numerical study (interval-cardinality anchor, mesoscopic window n greater than a
  few hundred and tau/lambda less than about 0.5) supports it empirically only.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecUniqueMatching

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecVolumeSector

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecOverlapScore
open UnifiedTheory.Audit.KFCausalCSpecUniqueMatching

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## The census is scale-blind (why the volume sector is necessary) -/

/-- Rescaling both profile families by `c` scales every score by `c^2`. -/
theorem permScore_smul (c : ℝ) (ci cj : Direction → H) (σ : Equiv.Perm Direction) :
    permScore (c • ci) (c • cj) σ = c ^ 2 * permScore ci cj σ := by
  simp only [permScore, score, Pi.smul_apply, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- **The census cannot see the scale.**  The canonical matching is invariant
under any positive rescaling of the profiles.  So the order/census sector recovers
the conformal transport but NOTHING about the metric scale — the volume sector is
genuinely complementary, not redundant. -/
theorem census_scale_blind (c : ℝ) (hc : 0 < c) (ci cj : Direction → H)
    (σ : Equiv.Perm Direction) :
    IsCanonical (c • ci) (c • cj) σ ↔ IsCanonical ci cj σ := by
  unfold IsCanonical
  constructor
  · intro h τ hτ
    have hlt := h τ hτ
    rw [permScore_smul, permScore_smul] at hlt
    exact lt_of_mul_lt_mul_left hlt (by positivity)
  · intro h τ hτ
    rw [permScore_smul, permScore_smul]
    exact mul_lt_mul_of_pos_left (h τ hτ) (by positivity)

/-! ## The volume recovers the scale (given the volume law) -/

/-- A local mesoscopic interval: dimension `d`, sprinkling density `rho`, diamond
constant `C`, all positive. -/
structure LocalInterval where
  d : ℕ
  rho : ℝ
  C : ℝ
  hd : 0 < d
  hrho : 0 < rho
  hC : 0 < C

/-- The small-diamond volume law: interval cardinality `= rho * C * tau^d`. -/
def volumeLaw (I : LocalInterval) (tau : ℝ) : ℝ := I.rho * I.C * tau ^ I.d

/-- **Scale recovery.**  Under the volume law, the interval cardinality determines
the proper time exactly: `(n / (rho*C))^(1/d) = tau`.  This is the SCALE datum the
census is blind to — the volume-sector complement of the census's transport. -/
theorem scale_recovered (I : LocalInterval) (tau : ℝ) (hτ : 0 ≤ tau) :
    (volumeLaw I tau / (I.rho * I.C)) ^ ((I.d : ℝ)⁻¹) = tau := by
  have hpos : (0:ℝ) < I.rho * I.C := mul_pos I.hrho I.hC
  have hstep : volumeLaw I tau / (I.rho * I.C) = tau ^ I.d := by
    rw [volumeLaw, mul_comm (I.rho * I.C) (tau ^ I.d), mul_div_assoc,
      div_self hpos.ne', mul_one]
  rw [hstep, ← Real.rpow_natCast tau I.d, ← Real.rpow_mul hτ,
    mul_inv_cancel₀ (by exact_mod_cast I.hd.ne'), Real.rpow_one]

/-- **Malament split, formal summary.**  For any positive scale `c`, the census
gives the SAME canonical matching on the rescaled profiles (scale-blind), while
the volume law recovers the scale itself.  Conformal transport and metric scale
are recovered by disjoint data. -/
theorem malament_split (I : LocalInterval) (tau : ℝ) (hτ : 0 ≤ tau)
    (c : ℝ) (hc : 0 < c) (ci cj : Direction → H) (σ : Equiv.Perm Direction) :
    (IsCanonical (c • ci) (c • cj) σ ↔ IsCanonical ci cj σ)
    ∧ (volumeLaw I tau / (I.rho * I.C)) ^ ((I.d : ℝ)⁻¹) = tau :=
  ⟨census_scale_blind c hc ci cj σ, scale_recovered I tau hτ⟩

#print axioms census_scale_blind
#print axioms scale_recovered
#print axioms malament_split

end UnifiedTheory.Audit.KFCausalCSpecVolumeSector

/- The high-density sector contains explicit nonzero physical observables.
Constant quaternion axes realize maximal spatial plaquette defects. -/
import UnifiedTheory.Clay.YangMills.WilsonHighFieldDecay
import UnifiedTheory.Clay.YangMills.QuaternionRotationFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHighFieldSector
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonHighFieldNormalization WilsonHighFieldDecay
open WilsonPhysicalVariance WilsonSingleLinkStaples
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def largeField : Slice n := fun e => QuaternionRotationFrame.rotation 1 e.2

omit [NeZero n] in
theorem large_holonomy (x : SpatialVertex n) (p : SpatialPlane) :
    spatialHolonomy (largeField n) x p.1.1 p.1.2 = -1 := by
  rcases p with ⟨⟨i,j⟩,hij⟩
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    apply Subtype.ext
    simp only [spatialHolonomy, ← Unitary.star_eq_inv, Submonoid.coe_mul,
      Unitary.coe_star, Unitary.coe_neg, OneMemClass.coe_one]
    ext <;> norm_num [spatialHolonomy, largeField, QuaternionRotationFrame.rotation,
      QuaternionRotationFrame.cosine, QuaternionRotationFrame.sine, QuaternionRotationFrame.axis]

theorem large_potential : potential character 2 (largeField n) = 4*links n := by
  unfold potential
  simp_rw [large_holonomy]
  norm_num [character_re, Unitary.coe_neg, WilsonSlabBounds.spatialPlane_card, links,
    Fintype.card_prod, Fintype.card_fin]
  ring

theorem flat_potential : potential character 2 (1 : Slice n) = 0 := by
  simp [potential, spatialHolonomy, character_re]

def potentialMap : C(Slice n, ℝ) :=
  ⟨potential character 2, by
    have hc := character_continuous
    unfold potential spatialHolonomy
    fun_prop⟩

def bump (r : ℝ) : C(Slice n, ℝ) :=
  ⟨fun u => max 0 (potentialMap n u-r * links n),
    continuous_const.max ((potentialMap n).continuous.sub continuous_const)⟩

theorem bump_physical (r : ℝ) (h : SliceGauge n WilsonSlabOperator.Q) (u : Slice n) :
    bump n r (gaugeSlice h u) = bump n r u := by
  change max 0 (potential character 2 (gaugeSlice h u)-r * links n) = _
  rw [WilsonSlabGauge.potential_gauge character character_classFunction]
  rfl

theorem bump_supported (r : ℝ) (u : Slice n) (hu : potential character 2 u < r * links n) :
    bump n r u = 0 := by
  exact max_eq_left (sub_nonpos.mpr hu.le)

theorem bump_nonconstant (r : ℝ) (hr : 0 ≤ r) (h4 : r < 4) :
    bump n r (1 : Slice n) ≠ bump n r (largeField n) := by
  change max 0 (potential character 2 (1 : Slice n)-r * links n) ≠
    max 0 (potential character 2 (largeField n)-r * links n)
  rw [flat_potential, large_potential]
  have hp := mul_pos (sub_pos.mpr h4) (links_pos n)
  rw [max_eq_left (show 0-r * links n ≤ 0 by nlinarith [links_pos n]),
    max_eq_right (show 0 ≤ 4*links n-r * links n by nlinarith)]
  nlinarith

theorem bump_mass_positive (β : ℝ) (hβ : 0 ≤ β) (r : ℝ) (hr : 0 ≤ r) (h4 : r < 4) :
    0 < mass n β hβ (bump n r) := by
  have hp := WilsonEndpointSupport.loss_positive n β hβ (bump n r) _ _
    (bump_nonconstant n r hr h4)
  rw [loss_mass] at hp
  have hn := mass_nonneg n β hβ (step n β hβ (bump n r))
  linarith

/-- An explicit nonzero physical source obeys the proved high-density
coercivity estimate whenever the quantitative free-energy condition holds. -/
theorem bump_coercivity (β : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 ≤ r)
    (he : 4 * WilsonGroundSlabEnergy.envelope β ≤ r / 2) :
    (1-Real.exp (-β*r / 2))*mass n β hβ.le (bump n r) ≤ loss n β hβ.le (bump n r) :=
  uniform_highfield_loss n β hβ r hr he (bump n r) (bump_supported n r)

end
end UnifiedTheory.Clay.YangMills.WilsonHighFieldSector

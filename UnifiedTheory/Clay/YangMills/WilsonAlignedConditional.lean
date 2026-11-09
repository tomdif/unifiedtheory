/- Exact conditional response at constant, flat Wilson configurations.
These are actual lattice exteriors, not independently prescribed staple sums. -/
import UnifiedTheory.Clay.YangMills.WilsonCoordinateInfluence
import UnifiedTheory.Clay.YangMills.ParallelOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAlignedConditional
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples WilsonIndependentBlocks SingleLinkWilsonOscillation
open PeriodicPlaquetteReflection SU2StarEnergy SU2WilsonConditionalSource SU2HaarTilt
open scoped Quaternion RealInnerProductSpace

/-- A continuous bounded test of the raw link orientation. -/
def probe : C(Q, ℝ) :=
  ⟨fun q => ⟪(q : ℍ), (1 : ℍ)⟫, continuous_subtype_val.inner continuous_const⟩

theorem probe_abs (q : Q) : |probe q| ≤ 1 := by
  have h := abs_real_inner_le_norm (q : ℍ) (1 : ℍ)
  simpa only [probe, ContinuousMap.coe_mk, norm_one,
    CStarRing.norm_of_mem_unitary q.property, mul_one] using h

theorem probe_oscillation (q r : Q) : |probe q - probe r| ≤ 2 :=
  (abs_sub _ _).trans (by linarith [probe_abs q, probe_abs r])

/-- The witness test is not gauge invariant under left multiplication of one link. -/
theorem probe_not_left_invariant : ¬ ∀ h q : Q, probe (h * q) = probe q := by
  intro h
  have hh := h (-1) 1
  norm_num [probe, Quaternion.inner_def, Unitary.coe_neg, OneMemClass.coe_one] at hh

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- Every positive link is assigned the same unit quaternion. -/
def constantConfiguration (q : Q) : Configuration (Vertex n) Q := fun _ => q

omit [NeZero n] [Fact (1 < n)] in
theorem constant_plaquette (q : Q) (p : PlaquetteIndex n) :
    plaquetteTerm n Q character 2 (constantConfiguration n q) p = 0 := by
  unfold plaquetteTerm WilsonMomentBounds.loopObservable wilson
  change 2 - (character (holonomy _ Q _ (plaquette n p.1 p.2.1.1 p.2.1.2))).re = 0
  rw [plaquette_holonomy_eq_product]
  simp [plaquetteProduct, PeriodicTimeReflection.linkValue, link, constantConfiguration,
    character_re]

omit [NeZero n] [Fact (1 < n)] in
theorem constant_starEnergy (q : Q) (x : Vertex n) (μ : Fin 4) :
    starEnergy n x μ (constantConfiguration n q) = 0 := by
  simp only [starEnergy, constant_plaquette, Finset.sum_const_zero]

/-- The true exterior staple is exactly six times the constant link, including its direction. -/
theorem constant_stapleField (q : Q) (x : Vertex n) (μ : Fin 4) :
    stapleField n x μ (constantConfiguration n q) = (6 : ℝ) • (q : ℍ) := by
  let A := stapleField n x μ (constantConfiguration n q)
  have he := starEnergy_eq n x μ (constantConfiguration n q)
  rw [constant_starEnergy] at he
  have hinner : ⟪(q : ℍ), A⟫ = 6 := by
    change 0 = 12 - 2 * ⟪(q : ℍ), A⟫ at he
    linarith
  have hnorm : ‖A‖ ≤ 6 := stapleField_norm_le_six n x μ (constantConfiguration n q)
  have hq : ‖(q : ℍ)‖ = 1 := CStarRing.norm_of_mem_unitary q.property
  have hinner' : ⟪A, (q : ℍ)⟫ = 6 := (real_inner_comm (q : ℍ) A).trans hinner
  have hs := norm_sub_sq_real A ((6 : ℝ) • (q : ℍ))
  simp only [norm_smul, real_inner_smul_right, hinner', hq] at hs
  norm_num at hs
  change A = (6 : ℝ) • (q : ℍ)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg A, norm_nonneg (A - (6 : ℝ) • (q : ℍ))]

/-- The actual Wilson coordinate law at each flat constant configuration has this exact mean. -/
theorem constant_coordinate_mean (β : ℝ) (q : Q) (a : Link n) :
    (∫ z, probe z ∂WilsonCoordinateInfluence.coordinateLaw n β (fun _ => q) a) =
      axisMean (12 * β) * probe q := by
  change (∫ z, probe z ∂conditionalLaw n a.1 a.2 β
    (exterior n a.1 a.2 (constantConfiguration n q))) = _
  rw [conditionalLaw_eq_tiltLaw]
  change (∫ z, ⟪(z : ℍ), (1 : ℍ)⟫ ∂tiltLaw β
    (stapleField n a.1 a.2 (constantConfiguration n q))) = _
  rw [constant_stapleField, tiltLaw_inner_mean, tiltMean_rotational]
  have hq : ‖(q : ℍ)‖ = 1 := CStarRing.norm_of_mem_unitary q.property
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 6), hq,
    mul_one, real_inner_smul_left]
  have hβ : 2 * β * 6 = 12 * β := by ring
  rw [hβ]
  change axisMean (12 * β) * (6 * probe q) / 6 = _
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonAlignedConditional

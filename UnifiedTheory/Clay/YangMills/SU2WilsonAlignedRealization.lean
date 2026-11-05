/- Full-lattice realization of the aligned two-staple SU(2) Gaussian model on
the nondegenerate four-dimensional periodic Wilson lattice (n > 1). Setting the
two forward transverse links at (x, 1) and (x, 2) to unit-circle rotors and all
other links to the identity realizes four identity staples and two independent
rotating staples for the link (x, 0). Consequently, the actual generated factor
produced by FiniteFactorElimination.nextFactor on {selectedLink n x 0} has a
four-point mixed interaction rectangle converging to -x * y / 3 at weak
coupling with an explicit O(1 / β) remainder. -/
import UnifiedTheory.Clay.YangMills.SU2AlignedGaussianApproximation
import UnifiedTheory.Clay.YangMills.WilsonFactorTower
import UnifiedTheory.Clay.YangMills.GibbsMixedInteraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonAlignedRealization
noncomputable section
open MeasureTheory Filter Set RegulatedGauge PeriodicLattice4
open PeriodicTimeReflection PeriodicPlaquetteReflection
open SingleLinkWilsonOscillation WilsonUniformVariance WilsonSingleLinkStaples
open SU2QuaternionEquivalence SU2HaarTilt SU2InducedAction
open SU2ConditionalInfluence SU2AlignedGaussianApproximation
open FiniteFactorConditional FiniteFactorElimination WilsonFactorTower
open scoped Quaternion RealInnerProductSpace Topology

/-- Squared quaternion norm of the unit-circle rotor equals one. -/
theorem rotor_normSq (t : ℝ) : Quaternion.normSq (rotor t) = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self, rotor_norm, mul_one]

/-- The unit-circle rotor as an element of the SU(2) unit-quaternion group. -/
def rotorUnit (t : ℝ) : Q :=
  ⟨rotor t, by
    constructor
    · rw [Quaternion.star_mul_self, rotor_normSq]
      rfl
    · rw [Quaternion.self_mul_star, rotor_normSq]
      rfl⟩

@[simp] theorem coe_rotorUnit (t : ℝ) : (rotorUnit t : ℍ) = rotor t := rfl

@[simp] theorem rotorUnit_zero : rotorUnit 0 = 1 := by
  apply Subtype.ext
  simp [rotorUnit, rotor, imaginaryUnit]

/-- Canonical (0, 1) coordinate plane. -/
def plane01 : Plane := ⟨(0, 1), by decide⟩

/-- Canonical (0, 2) coordinate plane. -/
def plane02 : Plane := ⟨(0, 2), by decide⟩

/-- Canonical (0, 3) coordinate plane. -/
def plane03 : Plane := ⟨(0, 3), by decide⟩

/-- The three coordinate planes containing direction 0 are plane01, plane02, and plane03. -/
theorem planes_zero_eq : planes 0 = {plane01, plane02, plane03} := by
  decide

/-- Explicit expansion of a sum over the three coordinate planes containing direction 0. -/
theorem sum_planes_zero (f : Plane → ℍ) :
    ∑ p ∈ planes 0, f p = f plane01 + f plane02 + f plane03 := by
  have h12 : plane01 ≠ plane02 := by decide
  have h13 : plane01 ≠ plane03 := by decide
  have h23 : plane02 ≠ plane03 := by decide
  have hm1 : plane01 ∉ ({plane02, plane03} : Finset Plane) := by simp [h12, h13]
  have hm2 : plane02 ∉ ({plane03} : Finset Plane) := by simp [h23]
  rw [planes_zero_eq, Finset.sum_insert hm1, Finset.sum_insert hm2, Finset.sum_singleton,
    add_assoc]

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

omit [NeZero n] in
/-- Stepping forward in direction μ after stepping backward in a distinct direction ν never
returns to the starting vertex on a nondegenerate periodic lattice. -/
theorem step_backward_ne (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    step n (backward n x ν) μ ≠ x := by
  intro he
  have h := congrArg (fun z : Vertex n => z μ) he
  change (x μ - (Pi.single ν (1 : ZMod n) : Vertex n) μ) +
    (Pi.single μ (1 : ZMod n) : Vertex n) μ = x μ at h
  have hz : (1 : ZMod n) = 0 := by
    simpa only [Pi.single_eq_of_ne hμν, Pi.single_eq_same, sub_zero, add_eq_left] using h
  exact one_ne_zero hz

omit [NeZero n] in
/-- The six-plaquette staple sum splits into forward and backward staples over planes μ. -/
theorem stapleSum_eq_planes_sum (U : Configuration (Vertex n) Q) (x : Vertex n) (μ : Fin 4) :
    stapleSum n U x μ =
      ∑ p ∈ planes μ,
        ((forwardStaple n Q U x μ (transverse μ p) : ℍ) +
          (backwardStaple n Q U x μ (transverse μ p) : ℍ)) := by
  classical
  unfold stapleSum weightedStaple affected
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    have hne : (x, p) ≠ (x - Pi.single (transverse μ p) 1, p) := by
      intro h
      exact backward_ne n x (transverse μ p) (congrArg Prod.fst h).symm
    have hnb : x - Pi.single (transverse μ p) 1 ≠ x := backward_ne n x (transverse μ p)
    rw [Finset.sum_pair hne]
    simp only [one_smul, staple, if_true, if_neg hnb]
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    have ha : a.2 = p := by
      rcases Finset.mem_insert.mp hap with h | h
      · exact congrArg Prod.snd h
      · exact congrArg Prod.snd (Finset.mem_singleton.mp h)
    have hb : a.2 = q := by
      rcases Finset.mem_insert.mp haq with h | h
      · exact congrArg Prod.snd h
      · exact congrArg Prod.snd (Finset.mem_singleton.mp h)
    exact hpq (ha.symm.trans hb)

private theorem pair_snd_ne {α β : Type*} {a₁ a₂ : α} {b₁ b₂ : β} (hb : b₁ ≠ b₂) :
    (a₁, b₁) ≠ (a₂, b₂) :=
  fun h => hb (congrArg Prod.snd h)

/-- Full-lattice configuration with rotors at (x, 1) and (x, 2) and identity elsewhere. -/
def alignedConfig (x : Vertex n) (t s : ℝ) : Configuration (Vertex n) Q :=
  replaceLink n Q (replaceLink n Q (fun _ => 1) x 1 (rotorUnit t)) x 2 (rotorUnit s)

omit [NeZero n] [Fact (1 < n)] in
theorem alignedConfig_link_one (x : Vertex n) (t s : ℝ) :
    linkValue n Q (alignedConfig n x t s) x 1 = rotorUnit t := by
  unfold alignedConfig
  rw [link_replace_other n Q _ x x 2 1 _ (pair_snd_ne (by decide)), link_replace_self]

omit [NeZero n] [Fact (1 < n)] in
theorem alignedConfig_link_two (x : Vertex n) (t s : ℝ) :
    linkValue n Q (alignedConfig n x t s) x 2 = rotorUnit s := by
  unfold alignedConfig
  exact link_replace_self n Q _ x 2 (rotorUnit s)

omit [NeZero n] [Fact (1 < n)] in
theorem alignedConfig_other (x y : Vertex n) (ν : Fin 4) (t s : ℝ)
    (h1 : (y, ν) ≠ (x, 1)) (h2 : (y, ν) ≠ (x, 2)) :
    linkValue n Q (alignedConfig n x t s) y ν = 1 := by
  unfold alignedConfig
  rw [link_replace_other n Q _ x y 2 ν _ h2, link_replace_other n Q _ x y 1 ν _ h1]
  rfl

omit [NeZero n] [Fact (1 < n)] in
theorem alignedConfig_apply_zero (x : Vertex n) (t s : ℝ) :
    alignedConfig n x t s (selectedLink n x 0) = 1 :=
  alignedConfig_other n x x 0 t s (pair_snd_ne (by decide)) (pair_snd_ne (by decide))

omit [NeZero n] in
/-- Each forward staple of (x, 0) in alignedConfig equals the single link value at (x, ν). -/
theorem alignedConfig_forwardStaple (x : Vertex n) (ν : Fin 4) (t s : ℝ) :
    forwardStaple n Q (alignedConfig n x t s) x 0 ν =
      linkValue n Q (alignedConfig n x t s) x ν := by
  unfold forwardStaple
  have h1 : linkValue n Q (alignedConfig n x t s) (step n x ν) 0 = 1 :=
    alignedConfig_other n x (step n x ν) 0 t s
      (pair_snd_ne (by decide)) (pair_snd_ne (by decide))
  have h2 : linkValue n Q (alignedConfig n x t s) (step n x 0) ν = 1 :=
    alignedConfig_other n x (step n x 0) ν t s
      (fun h => PeriodicPlaquetteNontriviality.step_ne n x 0 (congrArg Prod.fst h))
      (fun h => PeriodicPlaquetteNontriviality.step_ne n x 0 (congrArg Prod.fst h))
  rw [h1, h2, mul_one, inv_one, mul_one]

omit [NeZero n] in
/-- Every backward staple of (x, 0) in alignedConfig equals the identity. -/
theorem alignedConfig_backwardStaple (x : Vertex n) (ν : Fin 4) (hν : (0 : Fin 4) ≠ ν)
    (t s : ℝ) :
    backwardStaple n Q (alignedConfig n x t s) x 0 ν = 1 := by
  unfold backwardStaple
  have h1 : linkValue n Q (alignedConfig n x t s) (backward n x ν) ν = 1 :=
    alignedConfig_other n x (backward n x ν) ν t s
      (fun h => backward_ne n x ν (congrArg Prod.fst h))
      (fun h => backward_ne n x ν (congrArg Prod.fst h))
  have h2 : linkValue n Q (alignedConfig n x t s) (backward n x ν) 0 = 1 :=
    alignedConfig_other n x (backward n x ν) 0 t s
      (fun h => backward_ne n x ν (congrArg Prod.fst h))
      (fun h => backward_ne n x ν (congrArg Prod.fst h))
  have h3 : linkValue n Q (alignedConfig n x t s) (step n (backward n x ν) 0) ν = 1 :=
    alignedConfig_other n x (step n (backward n x ν) 0) ν t s
      (fun h => step_backward_ne n x 0 ν hν (congrArg Prod.fst h))
      (fun h => step_backward_ne n x 0 ν hν (congrArg Prod.fst h))
  rw [h1, h2, h3, inv_one, mul_one, mul_one]

omit [NeZero n] in
/-- Full-lattice realization: the staple sum of (x, 0) on alignedConfig is alignedSum t s. -/
theorem alignedConfig_stapleSum (x : Vertex n) (t s : ℝ) :
    stapleSum n (alignedConfig n x t s) x 0 = alignedSum t s := by
  rw [stapleSum_eq_planes_sum, sum_planes_zero]
  have ht1 : transverse 0 plane01 = 1 := rfl
  have ht2 : transverse 0 plane02 = 2 := rfl
  have ht3 : transverse 0 plane03 = 3 := rfl
  rw [ht1, ht2, ht3,
    alignedConfig_forwardStaple, alignedConfig_forwardStaple, alignedConfig_forwardStaple,
    alignedConfig_backwardStaple n x 1 (by decide) t s,
    alignedConfig_backwardStaple n x 2 (by decide) t s,
    alignedConfig_backwardStaple n x 3 (by decide) t s,
    alignedConfig_link_one, alignedConfig_link_two,
    alignedConfig_other n x x 3 t s (pair_snd_ne (by decide)) (pair_snd_ne (by decide))]
  change (rotor t + (1 : ℍ)) + (rotor s + (1 : ℍ)) + ((1 : ℍ) + (1 : ℍ)) =
    (4 : ℝ) • (1 : ℍ) + rotor t + rotor s
  module

/-- Exterior configuration of (x, 0) extracted from alignedConfig. -/
def alignedExterior (x : Vertex n) (t s : ℝ) : Exterior n Q x 0 :=
  ((SingleCoordinateProduct.assemble (selectedLink n x 0)).symm (alignedConfig n x t s)).1

omit [Fact (1 < n)] in
theorem exteriorConfig_alignedExterior (x : Vertex n) (t s : ℝ) :
    exteriorConfig n x 0 (alignedExterior n x t s) = alignedConfig n x t s := by
  funext e
  by_cases he : e = selectedLink n x 0
  · subst e
    simp [exteriorConfig, SingleCoordinateProduct.assemble_self, alignedConfig_apply_zero]
  · unfold exteriorConfig alignedExterior
    have h := congrFun
      ((SingleCoordinateProduct.assemble (selectedLink n x 0)).apply_symm_apply
        (alignedConfig n x t s)) e
    rw [SingleCoordinateProduct.assemble_other _ _ he] at h
    rw [SingleCoordinateProduct.assemble_other _ _ he]
    exact h

/-- The exterior staple functional on the full periodic lattice realizes alignedSum t s. -/
theorem alignedExterior_staple (x : Vertex n) (t s : ℝ) :
    exteriorStaple n x 0 (alignedExterior n x t s) = alignedSum t s := by
  unfold exteriorStaple
  rw [exteriorConfig_alignedExterior, alignedConfig_stapleSum]

omit [NeZero n] [Fact (1 < n)] in
theorem reference_alignedConfig (x : Vertex n) (t s : ℝ) :
    FiniteFactorElimination.reference {selectedLink n x 0} 1 (alignedConfig n x t s) =
      alignedConfig n x t s := by
  funext e
  by_cases he : e ∈ ({selectedLink n x 0} : Finset (Edge (Vertex n)))
  · have heq : e = selectedLink n x 0 := Finset.mem_singleton.mp he
    subst e
    simp only [FiniteFactorElimination.reference, Finset.mem_singleton, ↓reduceIte,
      alignedConfig_apply_zero]
  · simp only [FiniteFactorElimination.reference, if_neg he]

/-- Single-link action increment for (x, 0) evaluated on alignedConfig. -/
theorem increment_alignedConfig (x : Vertex n) (β t s : ℝ) (q : Q) :
    FiniteFactorElimination.increment (initialFactor n β) {selectedLink n x 0} 1
      ⟨selectedLink n x 0, Finset.mem_singleton_self _⟩ (alignedConfig n x t s, q) =
      2 * β * ⟪(1 : ℍ), alignedSum t s⟫ - 2 * β * ⟪(q : ℍ), alignedSum t s⟫ := by
  unfold FiniteFactorElimination.increment
  dsimp only
  rw [reference_alignedConfig, initial_sum]
  change orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2
      (replaceLink n Q (alignedConfig n x t s) x 0 q) -
    orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2
      (alignedConfig n x t s) = _
  have h1 : alignedConfig n x t s = replaceLink n Q (alignedConfig n x t s) x 0 1 := by
    funext e
    by_cases he : e = selectedLink n x 0
    · subst e
      simp [replaceLink, alignedConfig_apply_zero]
    · simp [replaceLink, Function.update_of_ne he]
  nth_rw 2 [h1]
  rw [action_replace, action_replace, alignedConfig_stapleSum]
  change (β * _ - 2 * β * ⟪(q : ℍ), alignedSum t s⟫) -
    (β * _ - 2 * β * ⟪(1 : ℍ), alignedSum t s⟫) = _
  ring

/-- The literal generated factor produced by eliminating {selectedLink n x 0} on alignedConfig. -/
def generatedAlignedFactor (x : Vertex n) (β t s : ℝ) : ℝ :=
  FiniteFactorElimination.nextFactor (compactHaar Q) (initialFactor n β)
    {selectedLink n x 0} 1 (.inr ⟨selectedLink n x 0, Finset.mem_singleton_self _⟩)
    (alignedConfig n x t s)

/-- Exact identity relating the generated lattice factor to starPotential and the reference term. -/
theorem generatedAlignedFactor_eq (x : Vertex n) (β t s : ℝ) :
    generatedAlignedFactor n x β t s =
      starPotential β t s - 2 * β * (2 - Real.cos t - Real.cos s) := by
  unfold generatedAlignedFactor FiniteFactorElimination.nextFactor
    LocalPotentialElimination.evolvedFactor LocalPotentialElimination.generated
    GibbsMarginalTower.effectiveAction GibbsMarginalTower.fiberMass
  dsimp only [Sum.elim_inr]
  have he (q : Q) :
      Real.exp (-FiniteFactorElimination.increment (initialFactor n β) {selectedLink n x 0} 1
        ⟨selectedLink n x 0, Finset.mem_singleton_self _⟩ (alignedConfig n x t s, q)) =
      Real.exp (-(2 * β * ⟪(1 : ℍ), alignedSum t s⟫)) * tiltWeight β (alignedSum t s) q := by
    rw [increment_alignedConfig]
    unfold tiltWeight
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  change -Real.log (∫ q : Q, Real.exp (-(2 * β * ⟪(1 : ℍ), alignedSum t s⟫)) *
    tiltWeight β (alignedSum t s) q ∂haar) = _
  rw [integral_const_mul]
  change -Real.log (Real.exp (-(2 * β * ⟪(1 : ℍ), alignedSum t s⟫)) *
    tiltPartition β (alignedSum t s)) = _
  rw [Real.log_mul (Real.exp_ne_zero _) (tiltPartition_pos β (alignedSum t s)).ne',
    Real.log_exp]
  have hre : ⟪(1 : ℍ), alignedSum t s⟫ = 4 + Real.cos t + Real.cos s := by
    simp [Quaternion.inner_def, alignedSum, rotor, imaginaryUnit]
  rw [hre]
  unfold starPotential potential
  ring

/-- Four-point mixed interaction rectangle of the actual generated factor on the lattice. -/
def generatedMixedInteraction (x : Vertex n) (β t s : ℝ) : ℝ :=
  generatedAlignedFactor n x β t s - generatedAlignedFactor n x β t 0 -
    generatedAlignedFactor n x β 0 s + generatedAlignedFactor n x β 0 0

/-- All single-variable reference terms cancel in the four-point mixed interaction rectangle. -/
theorem generatedMixedInteraction_eq_starMixed (x : Vertex n) (β t s : ℝ) :
    generatedMixedInteraction n x β t s =
      starPotential β t s - starPotential β t 0 - starPotential β 0 s + starPotential β 0 0 := by
  unfold generatedMixedInteraction
  rw [generatedAlignedFactor_eq, generatedAlignedFactor_eq,
    generatedAlignedFactor_eq, generatedAlignedFactor_eq]
  ring

/-- Quantitative O(1 / β) Gaussian approximation for the generated mixed interaction on the
four-dimensional periodic lattice in fluctuation coordinates (x / √β, y / √β). -/
theorem scaled_generatedMixedInteraction_error (z : Vertex n) (β R x y : ℝ)
    (hβ : max 1 (R ^ 2) ≤ β) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |generatedMixedInteraction n z β (x / Real.sqrt β) (y / Real.sqrt β) - (-x * y / 3)| ≤
      (3 * R ^ 4 / 2 + 9 * R ^ 2 / 10) / β := by
  have hR : |0| ≤ R := by simpa only [abs_zero] using (abs_nonneg x).trans hx
  have hxy := scaled_star_error β R x y hβ hx hy
  have hx0 := scaled_star_error β R x 0 hβ hx hR
  have h0y := scaled_star_error β R 0 y hβ hR hy
  rw [zero_div] at hx0 h0y
  let Exy := starPotential β (x / Real.sqrt β) (y / Real.sqrt β) - starPotential β 0 0 -
    (5 * x ^ 2 + 5 * y ^ 2 - 2 * x * y) / 6
  let Ex0 := starPotential β (x / Real.sqrt β) 0 - starPotential β 0 0 -
    (5 * x ^ 2 + 5 * 0 ^ 2 - 2 * x * 0) / 6
  let E0y := starPotential β 0 (y / Real.sqrt β) - starPotential β 0 0 -
    (5 * 0 ^ 2 + 5 * y ^ 2 - 2 * 0 * y) / 6
  have hid : generatedMixedInteraction n z β (x / Real.sqrt β) (y / Real.sqrt β) - (-x * y / 3) =
      (Exy - Ex0) - E0y := by
    rw [generatedMixedInteraction_eq_starMixed]
    dsimp only [Exy, Ex0, E0y]
    ring
  rw [hid]
  have htri : |(Exy - Ex0) - E0y| ≤ |Exy| + |Ex0| + |E0y| :=
    (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
  have hsum : |Exy| + |Ex0| + |E0y| ≤ 3 * ((R ^ 4 / 2 + 3 * R ^ 2 / 10) / β) := by
    dsimp only [Exy, Ex0, E0y]
    linarith [hxy, hx0, h0y]
  refine htri.trans (hsum.trans_eq ?_)
  ring

/-- In fluctuation coordinates (x / √β, y / √β), the generated four-point mixed interaction on
the actual periodic lattice converges to -x * y / 3 as β → ∞. -/
theorem scaled_generatedMixedInteraction_tendsto (z : Vertex n) (x y : ℝ) :
    Tendsto (fun β : ℝ =>
      generatedMixedInteraction n z β (x / Real.sqrt β) (y / Real.sqrt β))
      atTop (𝓝 (-x * y / 3)) := by
  have hxy := scaled_star_tendsto x y
  have hx0 := scaled_star_tendsto x 0
  have h0y := scaled_star_tendsto 0 y
  simp only [zero_div] at hx0 h0y
  have hcomb := (hxy.sub hx0).sub h0y
  have heq : (fun β : ℝ =>
      ((starPotential β (x / Real.sqrt β) (y / Real.sqrt β) - starPotential β 0 0) -
        (starPotential β (x / Real.sqrt β) 0 - starPotential β 0 0)) -
        (starPotential β 0 (y / Real.sqrt β) - starPotential β 0 0)) =
      (fun β : ℝ => generatedMixedInteraction n z β (x / Real.sqrt β) (y / Real.sqrt β)) := by
    funext β
    rw [generatedMixedInteraction_eq_starMixed]
    ring
  have hval : ((5 * x ^ 2 + 5 * y ^ 2 - 2 * x * y) / 6 -
      (5 * x ^ 2 + 5 * 0 ^ 2 - 2 * x * 0) / 6) -
      (5 * 0 ^ 2 + 5 * y ^ 2 - 2 * 0 * y) / 6 = -x * y / 3 := by ring
  rw [heq, hval] at hcomb
  exact hcomb

end
end UnifiedTheory.Clay.YangMills.SU2WilsonAlignedRealization

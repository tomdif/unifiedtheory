/-
Exact energy cost of a small six-plaquette staple in the original Wilson model.
The event is defined on full configurations through their actual exterior
links. Its geometry and energy threshold do not depend on a coupling, source,
probability comparison, or continuum hypothesis.
-/
import UnifiedTheory.Clay.YangMills.SU2HaarCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2StarEnergy
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples WilsonIndependentBlocks SingleLinkWilsonOscillation
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The actual retained links of a full configuration. -/
def exterior (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) :
    Exterior n Q x μ := fun e => U e.val

/-- The actual six exterior staple triples, without a source or coupling parameter. -/
def stapleField (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) : ℍ :=
  exteriorStaple n x μ (exterior n x μ U)

/-- The energy of the six actual plaquettes incident to the selected link. -/
def starEnergy (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) : ℝ :=
  ∑ p ∈ affected n x μ, plaquetteTerm n Q character 2 U p

/-- Small exterior staple event in the original configuration space. -/
def badEvent (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) : Set (Configuration (Vertex n) Q) :=
  {U | ‖stapleField n x μ U‖ ≤ r₀}

omit [NeZero n] [Fact (1 < n)] in
theorem exterior_continuous (x : Vertex n) (μ : Fin 4) : Continuous (exterior n x μ) := by
  apply continuous_pi
  intro e
  exact continuous_apply e.val

omit [Fact (1 < n)] in
theorem stapleField_continuous (x : Vertex n) (μ : Fin 4) : Continuous (stapleField n x μ) :=
  (exteriorStaple_continuous n x μ).comp (exterior_continuous n x μ)

omit [NeZero n] [Fact (1 < n)] in
theorem starEnergy_continuous (x : Vertex n) (μ : Fin 4) : Continuous (starEnergy n x μ) := by
  unfold starEnergy
  apply continuous_finset_sum
  intro p _
  apply continuous_const.sub
  exact Complex.continuous_re.comp
    ((continuous_wilson (Quiver.Symmetrify (Vertex n)) Q character character_continuous
      (loops n p)).comp (continuous_orientedExtension (Vertex n) Q))

omit [Fact (1 < n)] in
theorem badEvent_isClosed (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) :
    IsClosed (badEvent n x μ r₀) :=
  isClosed_le (stapleField_continuous n x μ).norm continuous_const

omit [Fact (1 < n)] in
theorem badEvent_measurable (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) :
    MeasurableSet (badEvent n x μ r₀) := (badEvent_isClosed n x μ r₀).measurableSet

omit [NeZero n] [Fact (1 < n)] in
theorem exterior_replaceLink (x : Vertex n) (μ : Fin 4)
    (U : Configuration (Vertex n) Q) (q : Q) :
    exterior n x μ (replaceLink n Q U x μ q) = exterior n x μ U := by
  funext e
  exact Function.update_of_ne e.property q U

omit [NeZero n] [Fact (1 < n)] in
theorem stapleField_replaceLink (x : Vertex n) (μ : Fin 4)
    (U : Configuration (Vertex n) Q) (q : Q) :
    stapleField n x μ (replaceLink n Q U x μ q) = stapleField n x μ U := by
  unfold stapleField
  rw [exterior_replaceLink]

omit [NeZero n] [Fact (1 < n)] in
theorem badEvent_replaceLink (x : Vertex n) (μ : Fin 4) (r₀ : ℝ)
    (U : Configuration (Vertex n) Q) (q : Q) :
    replaceLink n Q U x μ q ∈ badEvent n x μ r₀ ↔ U ∈ badEvent n x μ r₀ := by
  simp only [badEvent, Set.mem_setOf_eq, stapleField_replaceLink]

omit [Fact (1 < n)] in
theorem assemble_exterior (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) :
    SingleCoordinateProduct.assemble (selectedLink n x μ)
      (exterior n x μ U, U (selectedLink n x μ)) = U := by
  funext e
  by_cases he : e = selectedLink n x μ
  · subst e
    exact SingleCoordinateProduct.assemble_self _ _
  · rw [SingleCoordinateProduct.assemble_other _ _ he]
    rfl

/-- Exact energy identity in the true exterior/link coordinates. -/
theorem starEnergy_assemble (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ) (q : Q) :
    starEnergy n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) (r, q)) =
      12 - 2 * ⟪(q : ℍ), exteriorStaple n x μ r⟫ := by
  have h := affected_source_replace n (exteriorConfig n x μ r) x μ (fun _ => 1) q
  rw [replaceLink_exteriorConfig] at h
  norm_num only [one_mul, Finset.sum_const, nsmul_eq_mul, affected_card_eq_six,
    Nat.cast_ofNat, mul_one] at h
  exact h

/-- The selected link is the only non-exterior variable in the exact identity. -/
theorem starEnergy_eq (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) :
    starEnergy n x μ U =
      12 - 2 * ⟪(U (selectedLink n x μ) : ℍ), stapleField n x μ U⟫ := by
  have h := starEnergy_assemble n x μ (exterior n x μ U) (U (selectedLink n x μ))
  rw [assemble_exterior] at h
  exact h

omit [NeZero n] in
theorem stapleField_norm_le_six (x : Vertex n) (μ : Fin 4)
    (U : Configuration (Vertex n) Q) : ‖stapleField n x μ U‖ ≤ 6 :=
  exteriorStaple_norm_le_six n x μ (exterior n x μ U)

/-- An actual deterministic energy cost for a small exterior staple. -/
theorem starEnergy_lower (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) :
    2 * (6 - ‖stapleField n x μ U‖) ≤ starEnergy n x μ U := by
  rw [starEnergy_eq]
  have h := real_inner_le_norm (U (selectedLink n x μ) : ℍ) (stapleField n x μ U)
  rw [CStarRing.norm_of_mem_unitary (U (selectedLink n x μ)).property, one_mul] at h
  linarith

theorem starEnergy_nonneg (x : Vertex n) (μ : Fin 4) (U : Configuration (Vertex n) Q) :
    0 ≤ starEnergy n x μ U := by
  have h := starEnergy_lower n x μ U
  have hr := stapleField_norm_le_six n x μ U
  linarith

theorem badEvent_energy_lower (x : Vertex n) (μ : Fin 4) (r₀ : ℝ)
    (U : Configuration (Vertex n) Q) (hU : U ∈ badEvent n x μ r₀) :
    2 * (6 - r₀) ≤ starEnergy n x μ U := by
  have h := starEnergy_lower n x μ U
  change ‖stapleField n x μ U‖ ≤ r₀ at hU
  linarith

theorem badEvent_subset_energy (x : Vertex n) (μ : Fin 4) (r₀ : ℝ) :
    badEvent n x μ r₀ ⊆ {U | 2 * (6 - r₀) ≤ starEnergy n x μ U} := by
  intro U hU
  exact badEvent_energy_lower n x μ r₀ U hU

end
end UnifiedTheory.Clay.YangMills.SU2StarEnergy

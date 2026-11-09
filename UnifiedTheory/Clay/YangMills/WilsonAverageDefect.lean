/- Actual nonnegative unitary plaquette defects and their volume average.
Translation invariance bounds every plaquette mean by six times the average.
No continuum field identification is made. -/
import UnifiedTheory.Clay.YangMills.UnitaryHolonomyDefect
import UnifiedTheory.Clay.YangMills.PeriodicSpacetimeTranslation
import UnifiedTheory.Clay.YangMills.WilsonLocalOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Clay.YangMills.WilsonAverageDefect
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4
open PeriodicTimeReflection PeriodicPlaquetteReflection PeriodicSpacetimeTranslation
open WilsonCrossingKernel UnitaryCharacterObservables UnitaryHolonomyDefect

variable (N : ℕ) [NeZero N] (G : Type*) [Group G]
  {d : Type*} [Fintype d] [DecidableEq d]

def plaquetteDefect (ρ : G →* Matrix.unitaryGroup d ℂ)
    (p : PlaquetteIndex N) (U : Configuration (Vertex N) G) : ℝ :=
  defect ρ (holonomy (Quiver.Symmetrify (Vertex N)) G
    (orientedExtension (Vertex N) G U) (loops N p))

def averageDefect (ρ : G →* Matrix.unitaryGroup d ℂ)
    (U : Configuration (Vertex N) G) : ℝ :=
  (∑ p : PlaquetteIndex N, plaquetteDefect N G ρ p U) /
    (6 * (Fintype.card (Vertex N) : ℝ))

theorem volume_pos : 0 < (Fintype.card (Vertex N) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem plaquette_card : Fintype.card (PlaquetteIndex N) = 6 * Fintype.card (Vertex N) := by
  rw [Fintype.card_prod, WilsonLocalOscillation.plane_card]
  omega

theorem plaquette_nonneg (ρ : G →* Matrix.unitaryGroup d ℂ) (p : PlaquetteIndex N)
    (U : Configuration (Vertex N) G) : 0 ≤ plaquetteDefect N G ρ p U :=
  defect_nonneg ρ _

theorem plaquette_le (ρ : G →* Matrix.unitaryGroup d ℂ) (p : PlaquetteIndex N)
    (U : Configuration (Vertex N) G) : plaquetteDefect N G ρ p U ≤ 2 * (Fintype.card d : ℝ) :=
  defect_le ρ _

theorem average_nonneg (ρ : G →* Matrix.unitaryGroup d ℂ) (U : Configuration (Vertex N) G) :
    0 ≤ averageDefect N G ρ U :=
  div_nonneg (Finset.sum_nonneg (fun p _ => plaquette_nonneg N G ρ p U))
    (mul_nonneg (by norm_num) (volume_pos N).le)

theorem average_le_of_plaquette_le (ρ : G →* Matrix.unitaryGroup d ℂ)
    (U : Configuration (Vertex N) G) (eps : ℝ)
    (h : ∀ p, plaquetteDefect N G ρ p U ≤ eps) : averageDefect N G ρ U ≤ eps := by
  rw [averageDefect, div_le_iff₀ (mul_pos (by norm_num) (volume_pos N))]
  calc
    ∑ p : PlaquetteIndex N, plaquetteDefect N G ρ p U ≤ ∑ _ : PlaquetteIndex N, eps :=
      Finset.sum_le_sum (fun p _ => h p)
    _ = eps * (6 * (Fintype.card (Vertex N) : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, plaquette_card,
        Nat.cast_mul, Nat.cast_ofNat]
      ring

theorem average_le (ρ : G →* Matrix.unitaryGroup d ℂ) (U : Configuration (Vertex N) G) :
    averageDefect N G ρ U ≤ 2 * (Fintype.card d : ℝ) :=
  average_le_of_plaquette_le N G ρ U _ (fun p => plaquette_le N G ρ p U)

theorem total_eq_average (ρ : G →* Matrix.unitaryGroup d ℂ) (U : Configuration (Vertex N) G) :
    ∑ p : PlaquetteIndex N, plaquetteDefect N G ρ p U =
      (6 * (Fintype.card (Vertex N) : ℝ)) * averageDefect N G ρ U := by
  unfold averageDefect
  field_simp

theorem action_eq_average (ρ : G →* Matrix.unitaryGroup d ℂ) (beta : ℝ)
    (U : Configuration (Vertex N) G) :
    orientedWilsonAction (Vertex N) G (unitaryCharacter ρ) (base N) (loops N)
      beta (Fintype.card d) U =
      (beta * (6 * (Fintype.card (Vertex N) : ℝ))) * averageDefect N G ρ U := by
  change beta * (∑ p, plaquetteDefect N G ρ p U) = _
  rw [total_eq_average]
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem plaquette_continuous (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (p : PlaquetteIndex N) : Continuous (plaquetteDefect N G ρ p) :=
  (defect_continuous ρ hρ).comp ((continuous_holonomy (Quiver.Symmetrify (Vertex N)) G
    (loops N p)).comp (continuous_orientedExtension (Vertex N) G))

theorem average_continuous (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) :
    Continuous (averageDefect N G ρ) :=
  (continuous_finset_sum _ (fun p _ => plaquette_continuous N G ρ hρ p)).div_const _

theorem mean_translation (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta offset : ℝ) (x y : Vertex N) (plane : Plane) :
    (∫ U, plaquetteDefect N G ρ (x, plane) U
      ∂wilsonLaw N G (unitaryCharacter ρ) beta offset) =
    ∫ U, plaquetteDefect N G ρ (y, plane) U
      ∂wilsonLaw N G (unitaryCharacter ρ) beta offset := by
  have hp := wilsonLaw_preserves_shift N G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) beta offset (y - x)
  have hi := hp.integral_comp
    (configurationShiftMeasurableEquiv N G (y - x)).measurableEmbedding
    (plaquetteDefect N G ρ (x, plane))
  have he : (fun U => plaquetteDefect N G ρ (x, plane)
      (shiftConfiguration N G (y - x) U)) = plaquetteDefect N G ρ (y, plane) := by
    funext U
    change defect ρ (holonomy (Quiver.Symmetrify (Vertex N)) G
      (orientedExtension (Vertex N) G (shiftConfiguration N G (y-x) U))
      (plaquette N x plane.1.1 plane.1.2)) =
      defect ρ (holonomy (Quiver.Symmetrify (Vertex N)) G
        (orientedExtension (Vertex N) G U) (plaquette N y plane.1.1 plane.1.2))
    rw [plaquette_holonomy_shift]
    have hx : shiftVertex N (y-x) x = y := by unfold shiftVertex; abel
    rw [hx]
  rw [he] at hi
  exact hi.symm

/-- All sites have equal mean. Nonnegativity of the other five planes gives
this estimate without requiring rotation symmetry of the finite lattice. -/
theorem mean_plaquette_le_six_average (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta offset : ℝ) (p : PlaquetteIndex N) :
    (∫ U, plaquetteDefect N G ρ p U ∂wilsonLaw N G (unitaryCharacter ρ) beta offset) ≤
      6 * ∫ U, averageDefect N G ρ U ∂wilsonLaw N G (unitaryCharacter ρ) beta offset := by
  let μ := wilsonLaw N G (unitaryCharacter ρ) beta offset
  letI := wilsonLaw_probability N G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) beta offset
  have hint (q : PlaquetteIndex N) : Integrable (plaquetteDefect N G ρ q) μ :=
    (plaquette_continuous N G ρ hρ q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have havg : Integrable (averageDefect N G ρ) μ :=
    (average_continuous N G ρ hρ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : ∀ U, (∑ x : Vertex N, plaquetteDefect N G ρ (x, p.2) U) ≤
      (6 * (Fintype.card (Vertex N) : ℝ)) * averageDefect N G ρ U := by
    intro U
    rw [← total_eq_average, Fintype.sum_prod_type]
    exact Finset.sum_le_sum (fun x _ => Finset.single_le_sum
      (fun q _ => plaquette_nonneg N G ρ (x,q) U) (Finset.mem_univ p.2))
  have h := integral_mono (integrable_finset_sum _ (fun x _ => hint (x,p.2)))
    (havg.const_mul _) hp
  rw [integral_finset_sum _ (fun x _ => hint (x,p.2)), integral_const_mul] at h
  have he : (∑ x : Vertex N, ∫ U, plaquetteDefect N G ρ (x,p.2) U ∂μ) =
      (Fintype.card (Vertex N) : ℝ) * ∫ U, plaquetteDefect N G ρ p U ∂μ := by
    simp_rw [show ∀ x : Vertex N, (∫ U, plaquetteDefect N G ρ (x,p.2) U ∂μ) =
      ∫ U, plaquetteDefect N G ρ p U ∂μ from
        fun x => mean_translation N G ρ hρ beta offset x p.1 p.2]
    simp
  rw [he] at h
  have hv := volume_pos N
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonAverageDefect

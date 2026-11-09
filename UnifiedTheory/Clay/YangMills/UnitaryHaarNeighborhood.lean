/- A proved dimension-dependent polynomial lower bound for the actual
Haar mass of a unitary-representation identity neighborhood. It is obtained
from a finite grid and translation invariance, not an assumed volume formula. -/
import UnifiedTheory.Clay.YangMills.UnitaryCoordinateGrid
import UnifiedTheory.Clay.YangMills.UnitaryEntryEstimates
import UnifiedTheory.Clay.YangMills.FinitePartitionMass
import UnifiedTheory.Clay.YangMills.RegulatedGaugeMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryHaarNeighborhood
noncomputable section
open MeasureTheory RegulatedGauge UnitaryCoordinateGrid UnitaryEntryEstimates UnitaryHolonomyDefect

variable (d : Type*) [Fintype d]

def massLower (K : ℕ) : ℝ := 1 / ((2*K+1 : ℕ) : ℝ)^(2*(Fintype.card d)^2)

def entryRadius (K : ℕ) : ℝ := 2*(Fintype.card d : ℝ)/(K : ℝ)

def defectTolerance (K : ℕ) : ℝ :=
  (Fintype.card d : ℝ)*(1+3*(Fintype.card d : ℝ))*entryRadius d K

def squaredTolerance (K : ℕ) : ℝ :=
  (Fintype.card d : ℝ)^2*((1+3*(Fintype.card d : ℝ))*entryRadius d K)^2/2

theorem massLower_pos (K : ℕ) : 0 < massLower d K := by unfold massLower; positivity

theorem defectTolerance_nonneg (K : ℕ) : 0 ≤ defectTolerance d K := by
  unfold defectTolerance entryRadius
  positivity

theorem squaredTolerance_nonneg (K : ℕ) : 0 ≤ squaredTolerance d K := by
  unfold squaredTolerance
  positivity

theorem squaredTolerance_formula (K : ℕ) : squaredTolerance d K =
    2*(Fintype.card d : ℝ)^4*(1+3*(Fintype.card d : ℝ))^2/(K : ℝ)^2 := by
  unfold squaredTolerance entryRadius
  ring

variable {d} [DecidableEq d]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def nearIdentity (ρ : G →* Matrix.unitaryGroup d ℂ) (K : ℕ) : Set G :=
  {g | ∀ i j, ‖(ρ g) i j - (1 : Matrix d d ℂ) i j‖ ≤ entryRadius d K}

theorem nearIdentity_measurable (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (K : ℕ) : MeasurableSet (nearIdentity ρ K) := by
  simp only [nearIdentity, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  have hc : Continuous (fun g => (ρ g : Matrix d d ℂ) i j) :=
    (continuous_apply _).comp ((continuous_apply _).comp (continuous_subtype_val.comp hρ))
  exact (isClosed_le (hc.sub continuous_const).norm continuous_const).measurableSet

/-- Actual normalized Haar mass is bounded below by a completely explicit
power of the grid size. No injectivity of the representation is needed. -/
theorem nearIdentity_mass_lower (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (K : ℕ) (hK : 0 < K) :
    massLower d K ≤ (compactHaar G).real (nearIdentity ρ K) := by
  let s := fun g => grid K (ρ g)
  have hs : ∀ i, MeasurableSet (s ⁻¹' {i}) := fun i =>
    (grid_measurable ρ hρ K) (measurableSet_singleton i)
  obtain ⟨h,hh⟩ := FinitePartitionMass.exists_representative (compactHaar G) s hs
  have hsub : (fun g => h*g) ⁻¹' (s ⁻¹' {s h}) ⊆ nearIdentity ρ K := by
    intro g hg i j
    have hgrid : grid K (ρ (h*g)) = grid K (ρ h) := hg
    have hentry := grid_same_entry K hK (ρ (h*g)) (ρ h) hgrid
    have ht := translate_to_identity (ρ h) (ρ (h*g)) (2/(K : ℝ)) hentry i j
    simp only [map_mul, inv_mul_cancel_left] at ht
    change ‖(ρ g) i j-(1 : Matrix d d ℂ) i j‖ ≤ _
    convert ht using 1 <;> unfold entryRadius <;> ring
  have hm : (compactHaar G) ((fun g => h*g) ⁻¹' (s ⁻¹' {s h})) =
      (compactHaar G) (s ⁻¹' {s h}) :=
    (measurePreserving_mul_left (compactHaar G) h).measure_preimage (hs _).nullMeasurableSet
  calc
    massLower d K = 1 / (Fintype.card (((d × d) × Bool) → Fin (2*K+1)) : ℝ) := by
      rw [grid_card]
      simp only [massLower, Nat.cast_pow]
    _ ≤ (compactHaar G).real (s ⁻¹' {s h}) := hh
    _ = (compactHaar G).real ((fun g => h*g) ⁻¹' (s ⁻¹' {s h})) := by
      unfold Measure.real
      rw [hm]
    _ ≤ (compactHaar G).real (nearIdentity ρ K) := measureReal_mono hsub

theorem four_link_defect_bound (ρ : G →* Matrix.unitaryGroup d ℂ) (K : ℕ)
    (a b c e : G) (ha : a ∈ nearIdentity ρ K) (hb : b ∈ nearIdentity ρ K)
    (hc : c ∈ nearIdentity ρ K) (he : e ∈ nearIdentity ρ K) :
    defect ρ (a*b*c⁻¹*e⁻¹) ≤ defectTolerance d K := by
  have h := trace_defect_le (ρ a*ρ b*(ρ c)⁻¹*(ρ e)⁻¹)
    ((1+3*(Fintype.card d : ℝ))*entryRadius d K)
    (four_product_close (ρ a) (ρ b) (ρ c) (ρ e) (entryRadius d K) ha hb hc he)
  simpa only [defect, WilsonCrossingKernel.unitaryCharacter, map_mul, map_inv,
    defectTolerance, mul_assoc] using h

theorem four_link_defect_squared_bound (ρ : G →* Matrix.unitaryGroup d ℂ) (K : ℕ)
    (a b c e : G) (ha : a ∈ nearIdentity ρ K) (hb : b ∈ nearIdentity ρ K)
    (hc : c ∈ nearIdentity ρ K) (he : e ∈ nearIdentity ρ K) :
    defect ρ (a*b*c⁻¹*e⁻¹) ≤ squaredTolerance d K := by
  have h := trace_defect_square_le (ρ a*ρ b*(ρ c)⁻¹*(ρ e)⁻¹)
    ((1+3*(Fintype.card d : ℝ))*entryRadius d K)
    (by unfold entryRadius; positivity)
    (four_product_close (ρ a) (ρ b) (ρ c) (ρ e) (entryRadius d K) ha hb hc he)
  simpa only [defect, WilsonCrossingKernel.unitaryCharacter, map_mul, map_inv,
    squaredTolerance] using h

end
end UnifiedTheory.Clay.YangMills.UnitaryHaarNeighborhood
